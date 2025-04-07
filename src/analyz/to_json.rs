use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::mir::{Body, CastKind, interpret};
use rustc_middle::ty::{self, TyCtxt, DynKind};
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::symbol::Symbol;
use serde_json;
use std::collections::BTreeMap;
use std::collections::{HashMap, HashSet, hash_map};
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
        let trait_ref = preds.principal().map(|tr| tcx.erase_late_bound_regions(tr));
        let mut projs = preds.projection_bounds()
            .map(|proj| tcx.erase_late_bound_regions(proj))
            .collect::<Vec<_>>();
        projs.sort_by_key(|p| p.def_id);
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
            let super_preds = tcx.super_predicates_of(def_id);
            for &(ref pred, _) in super_preds.predicates {
                let tpred = match tcx.erase_late_bound_regions(pred.kind()) {
                    ty::PredicateKind::Clause(ty::Clause::Trait(x)) => x,
                    ty::PredicateKind::Clause(ty::Clause::TypeOutlives(..)) => continue,
                    _ => panic!("unexpected predicate kind: {:?}", pred),
                };
                assert_eq!(tpred.polarity, ty::ImplPolarity::Positive);
                if all_super_traits.insert(tpred.trait_ref.def_id) {
                    pending.push(tpred.trait_ref.def_id);
                }
            }
        }
        let mut all_super_traits = all_super_traits.into_iter().collect::<Vec<_>>();
        all_super_traits.sort();

        let mut projs = Vec::new();
        for super_trait_def_id in all_super_traits {
            for ai in tcx.associated_items(super_trait_def_id).in_definition_order() {
                match ai.kind {
                    ty::AssocKind::Type => {},
                    _ => continue,
                }
                let proj_ty = tcx.mk_projection(ai.def_id, trait_ref.substs);
                let actual_ty = tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), proj_ty);
                projs.push(ty::ExistentialProjection {
                    def_id: ai.def_id,
                    substs: ex_trait_ref.substs,
                    term: actual_ty.into(),
                });
            }
        }
        projs.sort_by_key(|p| p.def_id);

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
        let preds = tcx.intern_poly_existential_predicates(&preds);
        // Always emit `DynKind::Dyn`.  We don't support `dyn*` (`DynKind::DynStar`) yet.
        Some(tcx.mk_dynamic(preds, tcx.mk_region(ty::RegionKind::ReErased), DynKind::Dyn))
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
    pub substs: ty::subst::SubstsRef<'tcx>,
}

impl<'tcx> AdtInst<'tcx> {
    pub fn new(adt: ty::AdtDef<'tcx>, substs: ty::subst::SubstsRef<'tcx>) -> AdtInst<'tcx> {
        AdtInst { adt, substs }
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
        ty::TyKind::Slice(..) => "Slice",
        ty::TyKind::RawPtr(..) => "RawPtr",
        ty::TyKind::Ref(..) => "Ref",
        ty::TyKind::FnDef(..) => "FnDef",
        ty::TyKind::FnPtr(..) => "FnPtr",
        ty::TyKind::Dynamic(..) => "Dynamic",
        ty::TyKind::Closure(..) => "Closure",
        ty::TyKind::Generator(..) => "Generator",
        ty::TyKind::GeneratorWitness(..) => "GeneratorWitness",
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

#[macro_export]
macro_rules! basic_json_impl {
    ($n : path) => {
        impl ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}

};
}

#[macro_export]
macro_rules! basic_json_enum_impl {
    ($n : path) => {
        impl ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}

};
}

impl ToJson<'_> for CastKind {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        match self {
            CastKind::PointerExposeAddress => json!({ "kind": "PointerExposeAddress" }),
            CastKind::PointerFromExposedAddress => json!({ "kind": "PointerFromExposedAddress" }),
            CastKind::DynStar => json!({ "kind": "DynStar" }),
            CastKind::IntToInt => json!({ "kind": "IntToInt" }),
            CastKind::FloatToInt => json!({ "kind": "FloatToInt" }),
            CastKind::FloatToFloat => json!({ "kind": "FloatToFloat" }),
            CastKind::IntToFloat => json!({ "kind": "IntToFloat" }),
            CastKind::PtrToPtr => json!({ "kind": "PtrToPtr" }),
            CastKind::FnPtrToPtr => json!({ "kind": "FnPtrToPtr" }),
            CastKind::Pointer(_) => json!({ "kind": format!("{:?}", self) }),
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

impl<'tcx, T> ToJson<'tcx> for Vec<T>
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
