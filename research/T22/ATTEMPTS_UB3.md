# U-B3 attempts

The lane started with a clean worktree; no partial implementation was present.

Under the pinned Mathlib (Lean v4.34.0-rc2), `#check exists_smooth_tsupport_subset`
and `#check exists_contDiff_one_nhds_of_subset` both fail with `unknown identifier`.
The requested `isCutoffDatum_realizes_zeroExtension` also needs a theorem identifying
integration against the zero extension from `tsupport` hypotheses; no such bridge is
present in the imported T22 modules. I did not add `sorry`, `axiom`, or `native_decide`.
