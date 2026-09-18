ACCEPT-WITH-NOTES

## what the lane claims

The worker claims that `contDiff_dirDeriv` was moved verbatim to a shared leaf and both T12 gradient modules now import it, with no exported theorem changes (`formalization/NSFormalization/Section3/T12/DirDeriv.lean:15-29`, `GradientLSix.lean:185`, `GradientLambdaL3.lean:211`). It also claims registration of `MeanZeroSobolevCalculusAPI` and its nine fields/seven constants (`verification/Bindings/MeanZeroCalculus.lean:49-82`) under `T01.mean_zero_calculus` (`verification/contracts.json`, entry for that id).

## what is in Lean

The shared theorem is general in `{F}` and has the claimed `ContDiff` statement (`formalization/NSFormalization/Section3/T12/DirDeriv.lean:25-29`); the two former duplicate declarations are absent. The contract definitions and bridges are present, including `rfl` bridges for the restated definitions (`verification/Bindings/MeanZeroCalculus.lean:31-72`). The binding assembles the claimed constants and fields directly from the canonical T12 declarations (`verification/Bindings/MeanZeroCalculus.lean:79-108`). The test defines the checked value and runs the axiom checker (`verification/Tests/MeanZeroCalculus.lean:27-31`), with conformance and a concrete non-vacuity witness later in that file.

The cited paper/Spec references are carried in the contract docstrings (`verification/Contracts/V1/MeanZeroCalculus.lean:5-17`, `:30-38`, `:72-80`); no gap claim requiring a missing-tree lemma was made. A whole-tree grep found no second `MeanZeroSobolevCalculusAPI` declaration.

## gaps

One exact documentation fix: the worker report says `research/T12/REPORT_427.md` was not written, but that file is present in the lane and contains the report text. The report also calls the `parent_task` choice a pending judgement (`research/T12/REPORT_427.md`, gaps section), while the committed registry currently uses `T01`; this should be stated as resolved rather than pending. These do not affect Lean correctness or registration.

No silent hypotheses, empty interval assumptions, or `toReal` collapse were found in the inspected contract definitions. No `sorry`, `admit`, `axiom`, or `native_decide` occurs in changed Lean files. `git diff --name-only origin/erenup/integration-section3...HEAD` shows only the expected T12 modules, records, and generated registry/task files; no pre-existing Lean module outside the allowed dedupe edits is modified.

## commands and results

From the worktree, after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6` and `lake` run from `verification/`:

- `LEAN_NUM_THREADS=6 lake build Bindings.MeanZeroCalculus Tests.MeanZeroCalculus` — exit 0; `Build completed successfully (10065 jobs).` The only output is replayed upstream warnings plus `Contract ... checked; standard logical axioms only`.
- The worker’s recorded module build and probe commands in `research/T12/REPORT_427.md` report exit 0 for GradientLSix, GradientLambdaL3, CriticalL3Density, CriticalTrilinear, the T12 probes, and `axioms_u5/u6`; the recorded gates report `make check` OK, mutation suite passed, `check_contracts.py` exit 0 with `registered_contracts: 43` and `base_compatibility_checked: true`.
- Fresh negative probe `research/T12/probes/rev427_negative_constant.lean`, changing the theorem’s `Csix` coefficient to `0`, fails as expected: `Type mismatch ... gradientLSix v hv has type ... ENNReal.ofReal Csix ... but is expected ... ENNReal.ofReal 0 ...`.
- `grep -rn 'MeanZeroSobolevCalculusAPI' formalization/NSFormalization/Section4` finds no missing duplicate declaration.

The lane is acceptable after the two report wording corrections above.
