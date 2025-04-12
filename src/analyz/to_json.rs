use rustc_abi::ExternAbi;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::def::CtorKind;
use rustc_hir::Mutability;
use rustc_index::{IndexVec, Idx};
use rustc_middle::mir::{AssertMessage, BasicBlock, BinOp, Body, CastKind, interpret, NullOp, UnOp};
use rustc_middle::ty::{self, DynKind, FloatTy, IntTy, TyCtxt, UintTy};
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::source_map::Spanned;
use rustc_span::symbol::Symbol;
use serde_json;
use std::collections::BTreeMap;
use std::collections::{HashMap, HashSet, hash_map};
use std::fmt::Write;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::mem;


pub struct CompileState<'a, 'tcx> {
    pub session: &'a Session,
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Clone, Debug)]
pub struct UsedSet<T: Hash+Eq> {
    cur: HashSet<T>,
    new: HashSet<T>,
}

impl<T: Hash+Eq> Default for UsedSet<T> {
    fn default() -> Self {
        UsedSet {
            cur: HashSet::new(),
            new: HashSet::new(),
        }
    }
}

impl<T: Hash+Eq+Clone> UsedSet<T> {
    pub fn insert(&mut self, x: T) {
        if self.cur.insert(x.clone()) {
            // `x` was not in `cur`
            self.new.insert(x);
        }
    }

    pub fn take_new(&mut self) -> HashSet<T> {
        mem::replace(&mut self.new, HashSet::new())
    }

    pub fn has_new(&self) -> bool {
        self.new.len() > 0
    }
}

impl<T: Hash+Eq> Deref for UsedSet<T> {
    type Target = HashSet<T>;
    fn deref(&self) -> &HashSet<T> {
        &self.cur
    }
}

#[derive(Default)]
pub struct Used<'tcx> {
    pub types: UsedSet<AdtInst<'tcx>>,
    pub vtables: UsedSet<ty::PolyTraitRef<'tcx>>,
    pub instances: UsedSet<ty::Instance<'tcx>>,
    pub traits: UsedSet<TraitInst<'tcx>>,
}

impl<'tcx> Used<'tcx> {
    pub fn has_new(&self) -> bool {
        let Used { ref types, ref vtables, ref instances, ref traits } = *self;
        types.has_new() ||
        vtables.has_new() ||
        instances.has_new() ||
        traits.has_new()
    }
}

/// A trait, specialized to a particular set of type parameters and assignments to its associated
/// types.  For example, `Iterator<Item = u8>`.  Only the `Self` type is left unconstrained.
///
/// Another way to think of this is as the name of a single monomorphic "vtable signature".  The
/// types `dyn Iterator<Item = u8>` and `dyn Iterator<Item = i32>` are based on the same `TraitRef`
/// (and the same trait `DefId`), but have distinct `TraitInst`s and distinct vtable signatures,
/// because their `next` methods return different types.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TraitInst<'tcx> {
    pub trait_ref: Option<ty::ExistentialTraitRef<'tcx>>,
    pub projs: Vec<ty::ExistentialProjection<'tcx>>,
}

impl<'tcx> TraitInst<'tcx> {
    pub fn from_dynamic_predicates(
        tcx: TyCtxt<'tcx>,
        preds: &'tcx ty::List<ty::Binder<'tcx, ty::ExistentialPredicate<'tcx>>>,
    ) -> TraitInst<'tcx> {
        let trait_ref = preds.principal().map(|tr| tcx.instantiate_bound_regions_with_erased(tr));
        let mut projs = preds.projection_bounds()
            .map(|proj| tcx.instantiate_bound_regions_with_erased(proj))
            .collect::<Vec<_>>();
        projs.sort_by_key(|p| (p.def_id.krate, p.def_id.index));
        TraitInst { trait_ref, projs }
    }

    /// Obtain the `TraitInst` from a concrete `TraitRef`.  This erases the `Self` type, and
    /// generates a list of `ExistentialProjection` predicates based on the actual associated types
    /// declared in the impl.
    pub fn from_trait_ref(
        tcx: TyCtxt<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> TraitInst<'tcx> {
        let ex_trait_ref = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);

        let mut all_super_traits = HashSet::new();
        let mut pending = vec![trait_ref.def_id];
        all_super_traits.insert(trait_ref.def_id);
        while let Some(def_id) = pending.pop() {
            let super_preds = tcx.explicit_super_predicates_of(def_id);
            for &(ref pred, _) in super_preds.skip_binder() {
                let tpred = match tcx.instantiate_bound_regions_with_erased(pred.kind()) {
                    ty::ClauseKind::Trait(x) => x,
                    ty::ClauseKind::TypeOutlives(..) => continue,
                    _ => panic!("unexpected predicate kind: {:?}", pred),
                };
                assert_eq!(tpred.polarity, ty::PredicatePolarity::Positive);
                if all_super_traits.insert(tpred.trait_ref.def_id) {
                    pending.push(tpred.trait_ref.def_id);
                }
            }
        }
        let mut all_super_traits = all_super_traits.into_iter().collect::<Vec<_>>();
        all_super_traits.sort_by_key(|def_id| (def_id.krate, def_id.index));

        let mut projs = Vec::new();
        for super_trait_def_id in all_super_traits {
            for ai in tcx.associated_items(super_trait_def_id).in_definition_order() {
                match ai.kind {
                    ty::AssocKind::Type => {},
                    _ => continue,
                }
                let proj_ty = ty::Ty::new_projection(tcx, ai.def_id, trait_ref.args);
                let actual_ty = tcx.normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    proj_ty,
                );
                projs.push(ty::ExistentialProjection::new(
                    tcx,
                    ai.def_id,
                    ex_trait_ref.args,
                    actual_ty.into(),
                ));
            }
        }
        projs.sort_by_key(|p| (p.def_id.krate, p.def_id.index));

        TraitInst {
            trait_ref: Some(ex_trait_ref),
            projs,
        }
    }

    pub fn dyn_ty(&self, tcx: TyCtxt<'tcx>) -> Option<ty::Ty<'tcx>> {
        let trait_ref = self.trait_ref?;
        let mut preds = Vec::with_capacity(self.projs.len() + 1);
        preds.push(ty::Binder::dummy(ty::ExistentialPredicate::Trait(trait_ref)));
        preds.extend(
            self.projs.iter().map(|p| ty::Binder::dummy(ty::ExistentialPredicate::Projection(*p))),
        );
        let preds = tcx.mk_poly_existential_predicates(&preds);
        // Always emit `DynKind::Dyn`.  We don't support `dyn*` (`DynKind::DynStar`) yet.
        Some(ty::Ty::new_dynamic(tcx, preds, tcx.lifetimes.re_erased, DynKind::Dyn))
    }

    /// Build a concrete, non-existential TraitRef, filling in the `Self` parameter with the `dyn`
    /// type representing this trait instance.  For example: `dyn Trait<T, Assoc=U>: Trait<T>`.
    /// The substs from the resulting trait ref should be sufficient to `subst_and_normalize` the
    /// signature of any object-safe method to a concrete, monomorphic signature (no params or
    /// projections).
    pub fn concrete_trait_ref(&self, tcx: TyCtxt<'tcx>) -> Option<ty::TraitRef<'tcx>> {
        let tref = self.trait_ref?;
        let dyn_ty = self.dyn_ty(tcx)
            .expect("dyn_ty should only return None when self.trait_ref is None");
        Some(tref.with_self_ty(tcx, dyn_ty))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct AdtInst<'tcx> {
    pub adt: ty::AdtDef<'tcx>,
    pub args: ty::GenericArgsRef<'tcx>,
}

impl<'tcx> AdtInst<'tcx> {
    pub fn new(adt: ty::AdtDef<'tcx>, args: ty::GenericArgsRef<'tcx>) -> AdtInst<'tcx> {
        AdtInst { adt, args }
    }

    pub fn def_id(&self) -> DefId {
        self.adt.did()
    }
}

#[derive(Default, Debug)]
pub struct TyIntern<'tcx> {
    map: HashMap<ty::Ty<'tcx>, String>,
    /// Types that are newly referenced since the last `take_new_types()`.
    new_vals: Vec<serde_json::Value>,
}

/// Info for describing a type.  The `String` indicates (at minimum) the `TyKind`, and the `bool`
/// is `true` if a hash of the type should be included when forming the type's unique ID.
fn ty_desc(ty: ty::Ty) -> (String, bool) {
    let kind_str = match *ty.kind() {
        // Special case: primitive types print as themselves and don't require a hash.
        ty::TyKind::Bool |
        ty::TyKind::Char |
        ty::TyKind::Int(_) |
        ty::TyKind::Uint(_) |
        ty::TyKind::Float(_) |
        ty::TyKind::Str => return (format!("{:?}", ty), false),

        ty::TyKind::Adt(..) => "Adt",
        ty::TyKind::Foreign(..) => "Foreign",
        ty::TyKind::Array(..) => "Array",
        ty::TyKind::Pat(..) => "Pat",
        ty::TyKind::Slice(..) => "Slice",
        ty::TyKind::RawPtr(..) => "RawPtr",
        ty::TyKind::Ref(..) => "Ref",
        ty::TyKind::FnDef(..) => "FnDef",
        ty::TyKind::FnPtr(..) => "FnPtr",
        ty::TyKind::UnsafeBinder(..) => "UnsafeBinder",
        ty::TyKind::Dynamic(..) => "Dynamic",
        ty::TyKind::Closure(..) => "Closure",
        ty::TyKind::CoroutineClosure(..) => "Coroutine",
        ty::TyKind::Coroutine(..) => "Coroutine",
        ty::TyKind::CoroutineWitness(..) => "CoroutineWitness",
        ty::TyKind::Never => "Never",
        ty::TyKind::Tuple(..) => "Tuple",
        ty::TyKind::Alias(..) => "Alias",
        ty::TyKind::Param(..) => "Param",
        ty::TyKind::Bound(..) => "Bound",
        ty::TyKind::Placeholder(..) => "Placeholder",
        ty::TyKind::Infer(..) => "Infer",
        ty::TyKind::Error(..) => "Error",
    };
    (kind_str.to_owned(), true)
}

fn ty_unique_id(ty: ty::Ty, j: &serde_json::Value) -> String {
    let (kind_str, needs_hash) = ty_desc(ty);
    if needs_hash {
        let mut h = hash_map::DefaultHasher::new();
        serde_json::to_string(&j).unwrap().hash(&mut h);
        let hash_val = h.finish();
        format!("ty::{}::{:016x}", kind_str, hash_val)
    } else {
        format!("ty::{}", kind_str)
    }
}

impl<'tcx> TyIntern<'tcx> {
    pub fn get(&self, ty: ty::Ty<'tcx>) -> Option<&str> {
        self.map.get(&ty).map(|x| x as &str)
    }

    pub fn insert(&mut self, ty: ty::Ty<'tcx>, j: serde_json::Value) -> String {
        let id = ty_unique_id(ty, &j);
        self.new_vals.push(json!({
            "name": &id,
            "ty": j,
        }));
        let old = self.map.insert(ty, id.clone());
        assert!(old.is_none(), "duplicate insert for type {:?}", ty);
        id
    }

    pub fn take_new_types(&mut self) -> Vec<serde_json::Value> {
        mem::replace(&mut self.new_vals, Vec::new())
    }
}

/// How many functions should be exported in the JSON output?
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExportStyle {
    /// Only export functions annotated with the `#[crux::test]` attribute.
    ExportCruxTests,
    /// Export all functions.
    ExportAll
}

impl Default for ExportStyle {
    fn default() -> Self {
        ExportStyle::ExportCruxTests
    }
}

#[derive(Default, Debug)]
pub struct AllocIntern<'tcx> {
    /// We key this map on both ConstAllocations and their Tys. Keying the map
    /// on ConstAllocations alone is not sufficient, as two ConstAllocations
    /// with different types can share the same underlying memory representation
    /// (e.g., `0: u8` and `Ok(()) : Result<(), ()>`).
    map: HashMap<(interpret::ConstAllocation<'tcx>, ty::Ty<'tcx>), String>,
    new_vals: Vec<serde_json::Value>,
}

impl<'tcx> AllocIntern<'tcx> {
    pub fn get(&self, alloc: interpret::ConstAllocation<'tcx>, ty: ty::Ty<'tcx>) -> Option<&str> {
        self.map.get(&(alloc, ty)).map(|x| x as &str)
    }

    pub fn insert(&mut self, tcx: TyCtxt<'tcx>,
                  alloc: interpret::ConstAllocation<'tcx>, ty: ty::Ty<'tcx>,
                  mut static_def: serde_json::Value) -> String {
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let disambig = tcx.crate_hash(LOCAL_CRATE);
        // NB: The use of :: here is important, as mir-json's dead
        // code elimination relies on it.
        // See https://github.com/GaloisInc/mir-json/issues/36.
        let id = format!("{}/{}::{{{{alloc}}}}[{}]", crate_name, disambig, self.map.len());
        static_def["name"] = id.clone().into();
        self.new_vals.push(static_def);
        let old = self.map.insert((alloc, ty), id.clone());
        assert!(old.is_none(), "duplicate insert for type {:?}", alloc);
        id
    }

    pub fn take_new_allocs(&mut self) -> Vec<serde_json::Value> {
        mem::replace(&mut self.new_vals, Vec::new())
    }
}

pub struct MirState<'a, 'tcx : 'a> {
    pub mir: Option<&'tcx Body<'tcx>>,
    pub used: &'a mut Used<'tcx>,
    pub state: &'a CompileState<'a, 'tcx>,
    pub tys: &'a mut TyIntern<'tcx>,
    /// Maps the span of each pattern in a `match` expression to the span of the `match`'s
    /// scrutinee expression.  We use this for coverage reporting: the `SwitchInt` terminator
    /// introduced by the `match` will have its span set to one of the patterns, but we'd rather
    /// report coverage errors on the scrutinee instead, so we adjust the `discr_span` of the
    /// `SwitchInt` using this map.
    ///
    /// Note this works only for `match` expressions in the current crate.  Code inlined
    /// cross-crate will not have an entry in this map, and will not have its `SwitchInt` spans
    /// rewritten.  This seems okay for now since the user is mostly interested in coverage in
    /// their own top-level crate anyway.
    pub match_span_map: &'a HashMap<Span, Span>,
    pub allocs: &'a mut AllocIntern<'tcx>,
    pub export_style: ExportStyle,
}

/// Trait for converting MIR elements to JSON.
///
/// The `'tcx` parameter allows writing impls like `ToJson<'tcx> for Ty<'tcx>`, where the lifetime
/// parameter on `Self` is known to match the lifetime of `mir.state.tcx`.  This enables passing
/// `self` (or its fields) to some `TyCtxt` methods that would otherwise be unusable.
pub trait ToJson<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value;
}

impl ToJson<'_> for String {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(self)
    }
}

impl ToJson<'_> for Symbol {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(*self.as_str())
    }
}

impl<'tcx, T> ToJson<'tcx> for Option<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &Some(ref i) => i.to_json(mir),
            &None => serde_json::Value::Null,
        }
    }
}

impl<'tcx, T> ToJson<'tcx> for Box<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        <T as ToJson>::to_json(self, mir)
    }
}

impl<'tcx, K, V> ToJson<'tcx> for BTreeMap<K, V>
    where
    K: ToJson<'tcx>,
    V: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut jsons = Vec::new();
        for (k, v) in self.iter() {
            jsons.push(json!({"name": k.to_json(mir), "val": v.to_json(mir)}))
        }
        serde_json::Value::Array(jsons)
    }
}

impl<'a> ToJson<'_> for AssertMessage<'a> {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}

impl ToJson<'_> for BasicBlock {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}

// enum handlers

impl ToJson<'_> for ExternAbi {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            ExternAbi::Rust => json!({ "kind": "Rust" }),
            ExternAbi::PtxKernel => json!({ "kind": "PtxKernel" }),
            ExternAbi::Msp430Interrupt => json!({ "kind": "Msp430Interrupt" }),
            ExternAbi::X86Interrupt => json!({ "kind": "X86Interrupt" }),
            ExternAbi::GpuKernel => json!({ "kind": "GpuKernel" }),
            ExternAbi::EfiApi => json!({ "kind": "EfiApi" }),
            ExternAbi::AvrInterrupt => json!({ "kind": "AvrInterrupt" }),
            ExternAbi::AvrNonBlockingInterrupt => json!({ "kind": "AvrNonBlockingInterrupt" }),
            ExternAbi::CCmseNonSecureCall => json!({ "kind": "CCmseNonSecureCall" }),
            ExternAbi::CCmseNonSecureEntry => json!({ "kind": "CCmseNonSecureEntry" }),
            ExternAbi::RustIntrinsic => json!({ "kind": "RustIntrinsic" }),
            ExternAbi::RustCall => json!({ "kind": "RustCall" }),
            ExternAbi::Unadjusted => json!({ "kind": "Unadjusted" }),
            ExternAbi::RustCold => json!({ "kind": "RustCold" }),
            ExternAbi::RiscvInterruptM => json!({ "kind": "RiscvInterruptM" }),
            ExternAbi::RiscvInterruptS => json!({ "kind": "RiscvInterruptS" }),

            // Data-carrying variants — use Debug formatting
            ExternAbi::C { .. }
            | ExternAbi::Cdecl { .. }
            | ExternAbi::Stdcall { .. }
            | ExternAbi::Fastcall { .. }
            | ExternAbi::Vectorcall { .. }
            | ExternAbi::Thiscall { .. }
            | ExternAbi::Aapcs { .. }
            | ExternAbi::Win64 { .. }
            | ExternAbi::SysV64 { .. }
            | ExternAbi::System { .. } => {
                json!({ "kind": format!("{:?}", self) })
            }
        }
    }
}

impl ToJson<'_> for BinOp {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            BinOp::Add => json!({ "kind": "Add" }),
            BinOp::AddUnchecked => json!({ "kind": "AddUnchecked" }),
            BinOp::AddWithOverflow => json!({ "kind": "AddWithOverflow" }),
            BinOp::Sub => json!({ "kind": "Sub" }),
            BinOp::SubUnchecked => json!({ "kind": "SubUnchecked" }),
            BinOp::SubWithOverflow => json!({ "kind": "SubWithOverflow" }),
            BinOp::Mul => json!({ "kind": "Mul" }),
            BinOp::MulUnchecked => json!({ "kind": "MulUnchecked" }),
            BinOp::MulWithOverflow => json!({ "kind": "MulWithOverflow" }),
            BinOp::Div => json!({ "kind": "Div" }),
            BinOp::Rem => json!({ "kind": "Rem" }),
            BinOp::BitXor => json!({ "kind": "BitXor" }),
            BinOp::BitAnd => json!({ "kind": "BitAnd" }),
            BinOp::BitOr => json!({ "kind": "BitOr" }),
            BinOp::Shl => json!({ "kind": "Shl" }),
            BinOp::ShlUnchecked => json!({ "kind": "ShlUnchecked" }),
            BinOp::Shr => json!({ "kind": "Shr" }),
            BinOp::ShrUnchecked => json!({ "kind": "ShrUnchecked" }),
            BinOp::Eq => json!({ "kind": "Eq" }),
            BinOp::Lt => json!({ "kind": "Lt" }),
            BinOp::Le => json!({ "kind": "Le" }),
            BinOp::Ne => json!({ "kind": "Ne" }),
            BinOp::Ge => json!({ "kind": "Ge" }),
            BinOp::Gt => json!({ "kind": "Gt" }),
            BinOp::Cmp => json!({ "kind": "Cmp" }),
            BinOp::Offset => json!({ "kind": "Offset" }),
        }
    }
}

impl ToJson<'_> for CastKind {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            CastKind::PointerExposeProvenance => json!({ "kind": "PointerExposeProvenance" }),
            CastKind::PointerWithExposedProvenance => json!({ "kind": "PointerWithExposedProvenance" }),
            CastKind::IntToInt => json!({ "kind": "IntToInt" }),
            CastKind::FloatToInt => json!({ "kind": "FloatToInt" }),
            CastKind::FloatToFloat => json!({ "kind": "FloatToFloat" }),
            CastKind::IntToFloat => json!({ "kind": "IntToFloat" }),
            CastKind::PtrToPtr => json!({ "kind": "PtrToPtr" }),
            CastKind::FnPtrToPtr => json!({ "kind": "FnPtrToPtr" }),
            CastKind::Transmute => json!({ "kind": "Transmute" }),

            // Data-carrying variants — use Debug formatting
            CastKind::PointerCoercion { .. } => json!({ "kind": format!("{:?}", self) }),
        }
    }
}

impl ToJson<'_> for CtorKind {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            CtorKind::Fn => json!({ "kind": "Fn" }),
            CtorKind::Const => json!({ "kind": "Const" }),
        }
    }
}

impl ToJson<'_> for FloatTy {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            FloatTy::F16 => json!({ "kind": "F16" }),
            FloatTy::F32 => json!({ "kind": "F32" }),
            FloatTy::F64 => json!({ "kind": "F64" }),
            FloatTy::F128 => json!({ "kind": "F128" }),
        }
    }
}

impl ToJson<'_> for IntTy {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            IntTy::Isize => json!({ "kind": "Isize" }),
            IntTy::I8 => json!({ "kind": "I8" }),
            IntTy::I16 => json!({ "kind": "I16" }),
            IntTy::I32 => json!({ "kind": "I32" }),
            IntTy::I64 => json!({ "kind": "I64" }),
            IntTy::I128 => json!({ "kind": "I128" }),
        }
    }
}

impl ToJson<'_> for Mutability {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            Mutability::Not => json!({ "kind": "Not" }),
            Mutability::Mut => json!({ "kind": "Mut" }),
        }
    }
}

impl<'tcx> ToJson<'tcx> for NullOp<'tcx> {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            NullOp::SizeOf => json!({ "kind": "SizeOf" }),
            NullOp::AlignOf => json!({ "kind": "AlignOf" }),
            NullOp::UbChecks => json!({ "kind": "UbChecks" }),
            NullOp::ContractChecks => json!({ "kind": "ContractChecks" }),

            // Data-carrying variants — use Debug formatting
            NullOp::OffsetOf { .. } => json!({ "kind": format!("{:?}", self) }),
        }
    }
}

impl ToJson<'_> for UintTy {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            UintTy::Usize => json!({ "kind": "Usize" }),
            UintTy::U8 => json!({ "kind": "U8" }),
            UintTy::U16 => json!({ "kind": "U16" }),
            UintTy::U32 => json!({ "kind": "U32" }),
            UintTy::U64 => json!({ "kind": "U64" }),
            UintTy::U128 => json!({ "kind": "U128" }),
        }
    }
}

// end enum handlers

impl ToJson<'_> for UnOp {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            UnOp::Not => json!({ "kind": "Not" }),
            UnOp::Neg => json!({ "kind": "Neg" }),
            UnOp::PtrMetadata => json!({ "kind": "PtrMetadata" }),
        }
    }
}

impl<'tcx, A, B> ToJson<'tcx> for (A, B)
where
    A: ToJson<'tcx>,
    B: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let &(ref a, ref b) = self;
        json!(vec![a.to_json(mir), b.to_json(mir)])
    }
}

impl<'tcx, T> ToJson<'tcx> for [T]
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}

impl<'tcx, T> ToJson<'tcx> for Vec<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        <[T]>::to_json(self, mir)
    }
}

impl<'tcx, I, T> ToJson<'tcx> for IndexVec<I, T>
where
    I: Idx,
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        self.raw.to_json(mir)
    }
}

impl<'tcx, T> ToJson<'tcx> for Spanned<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        self.node.to_json(mir)
    }
}
