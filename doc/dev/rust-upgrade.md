# Upgrading the supported Rust toolchain for `mir-json`, `crucible-mir`, and `saw-script`

1. Pick a Rust nightly version.

    `mir-json` only works with nightly versions of Rust. Rust uses a [train
    release
    model](https://doc.rust-lang.org/book/appendix-07-nightly-rust.html#choo-choo-release-channels-and-riding-the-trains)
    where a beta is created by branching off from the current nightly every 6
    weeks, and then 6 weeks after that, the beta version becomes stable.
    Nightlies are simply builds of the Rust repository's `main` branch and are
    versioned by date, while beta and stable have a numbered version (e.g.
    1.91). When upgrading the `mir-json` Rust toolchain to a given numbered
    version, you can look on [releases.rs](https://releases.rs) to find the date
    that the numbered version was branched off of the `main` branch. The nightly
    corresponding to that date is a fine choice for the new `mir-json` Rust
    toolchain.[^1] The changelogs on [releases.rs](https://releases.rs) might
    also provide some clue as to the amount of effort required for this version
    upgrade.

    [^1]: Each nightly `rustc` actually also reports a numbered version when you
       ask for it. Whenever a beta for version `1.n` is branched off of nightly,
       subsequent nightlies then report themselves as being version `1.(n+1)`.
       But the actual features that will go into beta and stable `1.(n+1)` are
       gradually added over the next 6 weeks, until the branch happens. So if we
       claim that `mir-json` supports a given numbered version, we should pick
       the nightly with that numbered version that is the closest to the
       branching point, so it will be the most similar to the beta and stable
       builds of that version.

       Occasionally important fixes are backported from nightly onto beta, or
       patch releases are made for stable. Usually these fixes aren't important
       enough to affect `mir-json` and what we use it for, but it might be worth
       taking a look at the backported commits or the patch version release
       notes, and if there are any fixes that we care about, consider choosing a
       nightly that has those fixes applied. This nightly may have a higher
       numbered version than the version of Rust we are claiming to support.

       There is actually a gap of a few days between when the beta branches off
       of nightly and when the version number of the nightly is bumped. For
       instance, https://releases.rs/docs/1.91.0/ says that 1.91 was branched
       from `master` on 2025-09-12, but the nightly builds up until 2025-09-14
       still report their version as 1.91, and only 2025-09-15 has version 1.92.
       For the 1.86 and 1.91 upgrades I picked the last nightly that still
       reports that version number, rather than the nightly that the stable
       build was branched off of, but honestly I don't think it matters, and
       it's probably easier just to use the nightly corresponding to the
       branching date.

       An additional point of confusion is that when you run `rustc --version`
       for a nightly `rustc`, it will generally report a date that is one day
       *before* the nightly toolchain's date; for instance, `rustc` on
       `nightly-2025-09-14` reports `rustc 1.91.0-nightly (02c7b1a7a
       2025-09-13)`. This is because it is built from a commit made on
       `2025-09-13`, but the actual build was released on `2025-09-14` and is
       versioned as such.

2. Update the toolchain name in `mir-json`.

    The toolchain name (e.g. `nightly-2025-09-14`) is referenced in several
    places, such as `rust-toolchain.toml`, `src/bin/wrapper.rs`, `README.md`,
    `.github/workflows/ci.yml`, and `Dockerfile`. Update it to the new toolchain
    you just picked, and commit the changes on a new branch of `mir-json`.

3. Fix the compile errors in `mir-json`.

    `mir-json` makes use of a lot of `rustc`'s internal APIs, and these are
    refactored upstream all the time, so there might be dozens of errors if you
    just update the toolchain name and run `cargo build`. Most of these errors
    will be relatively easy to fix (e.g. a function was renamed), but a few
    might be more involved. To figure out what changed upstream and what you
    should do to fix it, useful resources are the [`rustc` API
    docs](https://doc.rust-lang.org/1.91.0/nightly-rustc/) (that link goes to
    the 1.91.0 docs; replace the version in the URL with the one you want!) and
    the [`rust-lang/rust` repo](https://github.com/rust-lang/rust) itself. What
    I usually do is:

    - For upstream things that appear to have been *added* (indicated by e.g. an
      error about a missing case in a `match` expression) or *changed* (e.g. a
      type error): `git blame` the upstream file in the `rust` repo in which
      that thing is defined, and find the commit that added or changed it.
    - For upstream things that appear to have been *removed* (e.g. name not
      defined): `git log -pS 'thing_that_was_removed'
      compiler/path/to/where_the_thing_used_to_be_defined` will usually get you
      the commit that removed it. Often the removal turns out to be just a move
      to a different file or a renaming.

    Once you have the commit for the upstream change, looking at its
    corresponding PR will provide more context if the commit description
    doesn't.[^2]

    [^2]: If you look at the commit on GitHub, it will say in which PR it was
       merged into `main`. Sometimes the linked PR will be "Rollup of n pull
       requests". In that case, that PR's description will contain a list of the
       actual PRs that were rolled up. It is usually fairly obvious which one of
       those contains the commit you were looking at, and you can get to the
       actual PR from there.

    (I don't claim that this is the best way of doing things; it is just what I
    have been doing, and if you find a more efficient way of doing this, feel
    free to contribute to this document!)

    I usually make a separate `mir-json` commit for the changes caused by each
    upstream `rust` commit, and put a link to the `rust` commit in the
    `mir-json` commit description. This way, if it turns out that something was
    fixed in the wrong way, we can easily find the change that did so, and the
    corresponding upstream changes to help figure out the correct fix.

    Most of the compile errors will likely be in `src/analyz`, since those are
    the files that extensively use the `rustc` internal API. There may or may
    not be a few changes needed for files in `bin/`, which will only show up
    once you resolve all the problems in `src/analyz/`.

4. Update dependencies.

    `mir-json` has some Rust dependencies, listed in `Cargo.toml`. At a minimum,
    we need to update the version of the `cargo` library that we use, since
    `mir-json` depends on both the `cargo` binary and the `cargo` library, and
    we want them to match. As far as I can tell, `cargo` library version `0.x`
    corresponds to the `cargo` included with Rust version `1.x`, so update the
    `cargo` library version accordingly. Fix any build errors that result from
    this. This might also require updating versions of other dependencies to
    match `cargo`'s dependencies.

    You are also welcome to update the versions of other unrelated dependencies
    as you see fit.

    Once everything builds properly with updated dependencies, commit the
    changes and run `cargo install --path . --locked` to install the updated
    `mir-json` binaries.

5. Get a copy of the standard libraries for the new toolchain.

    First rename the current `libs` directory to something like `libs-old`. Then
    run `mir-json-translate-libs --copy-sources libs` to save a copy of the new
    standard libraries to `libs`. This is the set of standard libraries for
    targeting your current host triple with the new toolchain. The set of
    standard libraries may vary for different platforms. We want to support
    common desktop platforms (e.g. `aarch64-apple-darwin`,
    `x86_64-unknown-linux-gnu`), as well as `wasm32-unknown-unknown`. At the
    time of writing, the only target out of these whose set of standard
    libraries differs is `wasm32-unknown-unknown`; it includes `dlmalloc` as an
    additional library. So also run `mir-json-translate-libs --copy-sources libs
    --target wasm32-unknown-unknown` to add `dlmalloc` to `libs` (it will skip
    copying any libraries already in `libs`).

6. Copy over our custom libraries.

    In addition to the standard libraries, we also include some custom libraries
    in `mir-json`'s `libs` directory. These include:[^3]

    - `crucible`
    - `crucible_proc_macros`
    - `int512.rs`
    - `bytes.rs`
    - `byteorder`
    - `core/src/crucible`

    Copy these over from `libs-old` to `libs`. Also copy over `Patches.md`.

    [^3]: We plan to [get rid of some of
       these](https://github.com/GaloisInc/mir-json/issues/101) at some point.

    Commit the new `libs` after you do this. (At this point, you may delete
    `libs-old`, or leave it around for now for ease of reference when applying
    patches later. If you leave it around, make sure you don't commit it.)

7. Re-apply the first patch (registering the `core::crucible` module in `core`'s
   `lib.rs`).

    The first patch in `Patches.md` should be "Add reference to `core::crucible`
    module". Re-apply it, since we now have a fresh upstream copy of `core`'s
    `lib.rs` without the reference to our custom `crucible` modules that we just
    copied in. If you `git blame` the line with the "last applied" date, it
    should give you the commit from the last time the patch was applied, in the
    last toolchain upgrade, and you can reference that to make your current
    change. Once you do that, update the "last applied" date and then make a
    single commit with both the `lib.rs` changes and the `Patches.md` change, so
    that the `git blame` method will continue to work in the future.

8. Try running `mir-json-translate-libs`.

    The `libs` directory should now be in a state where
    `mir-json-translate-libs` can run on it. Delete any old `rlibs` and
    `rlibs_real` you may have around, and run `mir-json-translate-libs`. If it
    succeeds, great. If `mir-json` crashes at some point, there is most likely
    an upstream change to the `rustc` API that wasn't caught by the compiler in
    step 3. Debug it, fix it, and commit any changes (similar to step 3, it
    might be good to link to the upstream changes in the commit description).

9. Set up the `crucible` and `saw-script` branches.

    Make a branch in the `crucible` repo. Update `RUST_TOOLCHAIN` in
    `crucible`'s `.github/workflows/crux-mir-build.yml` and
    `.github/Dockerfile-crux-mir` to your new toolchain, and commit.

    Do the same for the `saw-script` repo: update `RUST_TOOLCHAIN` in
    `.github/workflows/ci.yml` and `crux-mir-comp/Dockerfile`, and commit to a
    new branch.

10. Re-apply the rest of the patches.

    Go through the rest of the patches in `mir-json`'s `Patches.md` and try to
    re-apply them. For each patch, there is at least one test in the `crux-mir`
    test suite that tests the thing that the patch claims to fix (that is, the
    test should fail without the patch applied, and succeed with the patch
    applied). So you can run the `crux-mir` tests to check if a patch worked or
    not. Note that you will only be able to test certain patches once certain
    other patches have been applied (e.g. without the patch that fixes
    allocations, all tests involving allocations will result in an error and
    will not test anything that happens after the allocation).

    As with the first patch, use `git blame` to look at the patch for the
    previous toolchain version. For most patches, there should be minimal
    changes required to adapt the patch to the current toolchain version. In a
    few cases, the patch will need to be extended, modified, or entirely redone
    in a different way. If so, make sure you update the patch description in
    `Patches.md` accordingly. There is also the possibility that the patch has
    become obsolete; if the code that the patch is patching is gone entirely,
    you can skip over this patch for now, and if after applying all other
    patches, all the `crux-mir` tests pass, then this patch is not needed
    anymore and can be removed from `Patches.md`.

    Some patches might have an "*Update*" line (or several) after the patch
    description. This means the patch was amended in between the last toolchain
    upgrade and this one. Each "*Update*" line should be linked to some commit
    with Rust changes via `git blame`. You should incorporate all the changes
    from the "*Update*" lines into your current patch, and fold the update
    descriptions into the main patch description, so that the patch will be one
    single commit this time.

    After making the patch changes, check that the patch at least compiles by
    running `mir-json-translate-libs`, run relevant `crux-mir` tests if it is
    easy to do, and then commit the patch. Make sure to update the "last
    applied" date, and **always make a single commit for each patch**, with both
    the `Patches.md` edits and the actual Rust changes. If later on you realize
    some part of the patch needs to be changed, use `git rebase` to edit the
    commit. If it is hard to rebase for some reason, then add an "*Update*" line
    with your new change, again making a single commit containing both the
    "*Update*" line and the code changes.

    After applying all the existing patches, there may still be some `crux-mir`
    test failures. This may mean that new patches are needed. Add new patches to
    the bottom of `Patches.md`, or next to a related patch if one exists,
    following the existing format. For each new patch, make sure there is a
    `crux-mir` test that tests the feature it's patching for. If the need for
    the new patch was only incidentally revealed by the failure of a `crux-mir`
    test case that was mainly testing a different thing, it's best to make a new
    `crux-mir` test for the patched feature specifically, so that even if in the
    future the patch becomes unnecessary for the original test case to work, the
    patch is still tested.

    Creating new patches, or re-doing existing patches, might require changes on
    the `crucible-mir` side. Commit on your `crucible` branch as you make those
    changes.

    As you look at the `crux-mir` test outputs, some tests are marked as
    expected to fail and will say something like "FAIL (expected)" in the test
    output. The test runner only checks that they fail and not *how* they
    failed, so inspect the XFAIL test outputs to make sure that the failure
    matches the reason described and is not some unexpected error.

    Finally, some `crux-mir` test failures under the `symb_eval` directory may
    be due to benign things like changes in line numbers in error messages for
    certain things in the standard library. In that case, simply update the
    `.good` file with the new output and commit.

    After all the `crux-mir` tests pass, it's worth checking that the
    `crux-mir-comp` tests pass as well. If there were any `crucible`-side
    changes, update `saw-script`'s `deps/crucible` submodule to your `crucible`
    branch, and commit the results (if the submodule change isn't committed,
    `saw-script`'s `build.sh` will reset it). Build and run the `crux-mir-comp`
    tests. Make and commit necessary changes in `mir-json`, `crucible`, and/or
    `saw-script` for the `crux-mir-comp` tests to pass.

11. Check `mir-json-translate-libs` for other targets.

    Because the standard libraries have some target-specific
    conditionally-compiled code, make sure `mir-json-translate-libs` works for
    other targets that we care about which are not your host (e.g.
    `aarch64-apple-darwin`, `x86_64-unknown-linux-gnu`,
    `wasm32-unknown-unknown`). This may reveal that some patches need to be
    modified or new patches need to be created. Edit the patch commits and/or
    create new patch commits.

12. Look for TODOs waiting for the toolchain upgrade.

    Occasionally there will be some sort of temporary workaround in `mir-json`
    or `crucible` that is expected to not be needed anymore after a toolchain
    upgrade to a certain Rust version. If there are any of these, check if they
    can be safely removed, and if so, remove and commit.

13. Bump schema version, update changelogs, and update submodules.

    In `mir-json`, bump the schema version in `src/schema_ver.rs` and
    `doc/mir-json-schema.ts`. Make changes to `doc/mir-json-schema.ts` to
    reflect the new schema if anything changed (but still bump the schema
    version if nothing changed). Add the new schema version and a description of
    the changes to `SCHEMA_CHANGELOG.md`. Mention the new toolchain name and
    Rust version in the changelog. Commit the changes.

    When you do this, make sure to not conflict with any schema version changes
    that have happened on the `master` branch since you started working on the
    toolchain upgrade. It's best to merge from or rebase on `master` before
    doing this step.

    In `crucible`, bump the schema version in
    `crucible-mir/src/Mir/ParseTranslate.hs`, `crucible-mir/CHANGELOG.md`,
    `crux-mir/CHANGELOG.md`, and `crux-mir/README.md`. Mention the new supported
    Rust version in `crucible-mir/CHANGELOG.md` and `crux-mir/CHANGELOG.md`.
    Update the `dependencies/mir-json` submodule to the latest commit on your
    `mir-json` branch. Commit the changes.

    In `saw-script`, bump the schema version in `CHANGES.md` and `README.md`.
    Mention the new supported Rust version in `CHANGES.md`. Update the
    `deps/mir-json` and `deps/crucible` submodules to your latest `mir-json` and
    `crucible` commits respectively. Commit the changes. (If you already updated
    the `crucible` submodule earlier, consider amending that commit instead to
    avoid having a bunch of submodule bump commits.)

14. Update `saw-script` test cases for the new schema version.

    Make sure you've installed the most updated version of `mir-json` from your
    branch. In the `saw-script` repo, run `make regen-mir-blobs` in `intTests/`
    and in `saw-python/tests/saw/test-files/` to re-run `mir-json` and produce
    JSON files with the new schema version. Also update the alphanumeric
    identifier disambiguators in
    [`intTests/test_mir_verify_basic/test.saw`](https://github.com/GaloisInc/saw-script/blob/c49bd9b64c701663bdaab87b42b8bb8e51eec3cc/intTests/test_mir_verify_basic/test.saw#L75-L77)
    and
    [`intTests/test2122_typecheck_gap/mir.log.good`](https://github.com/GaloisInc/saw-script/blob/909178acf05c9dd38e643a36cf640670b0ba2ea7/intTests/test2122_typecheck_gap/mir.log.good#L2-L3),
    which will likely have changed (see
    [saw-script#2614](https://github.com/GaloisInc/saw-script/issues/2614)).

15. Create pull requests.

    Create pull requests for the `mir-json`, `crucible`, and `saw-script`
    branches. If you make further changes to `mir-json`, make sure to update the
    `mir-json` submodule in `crucible`. Then update the `mir-json` and
    `crucible` submodules in `saw-script`, and redo step 14. If you make further
    changes to `crucible`, make sure to update the `crucible` submodule in
    `saw-script`. When updating submodules, you can amend and force-push your
    previous submodule update commits from step 13. When redoing step 14, you
    can amend and force-push your previous commit from step 14.

# While working on `mir-json` and `crucible-mir` in between toolchain upgrades

- If you make *any* changes to anything under `mir-json/libs`, there must be an
  accompanying change in `libs/Patches.md`, in the form of either a new patch or
  an "*Update*" line under an existing patch.
- If you make changes to `crucible-mir` that makes an existing `mir-json`
  standard library patch partially or fully obsolete, update the `mir-json` side
  to reflect that. For a fully obsolete patch, you can just undo the patch and
  then delete its section in `Patches.md`, and for a partially obsolete patch,
  undo the now-unnecessary parts of the patch, and then commit those changes
  together with an "*Update*" line in `Patches.md` under the patch in question.
