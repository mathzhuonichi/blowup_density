ACCEPT-WITH-NOTES

## what the lane claims
The report claims concrete T17 transport proofs for the two `eq:derivativebounds` estimates, with constants chosen from the Paper1 existential bounds, and a probe/non-vacuity instance. This matches the requested U5/U6 targets. The cited Paper1 statements are exactly the advertised bounds: `physical_mixed_derivative_bound` at `formalization/NSFormalization/Paper1/CorrectionProfile.lean:291-299` and `physicalForce_spatial_derivative_bound` at `formalization/NSFormalization/Paper1/CorrectionForceProfile.lean:270-277`. The Spec fields are at `research/T17/Spec.lean:878-890` and `:893-901`.

## what is in Lean
`correctionDerivConst` and its nonnegativity theorem are in `formalization/NSFormalization/Section3/T17/CorrectionDeriv.lean:27-43`; the concrete bound is `:50-85`. It rewrites through `correctionData_correction`, selects a single lattice copy, and applies the Paper1 estimate with `ε ∈ Ioc 0 1` derived from `hε₀`.

`forceDerivConst` and nonnegativity are in `formalization/NSFormalization/Section3/T17/ForceDeriv.lean:26-42`; `force_derivative_bound` is `:49-96`. It uses `force_eq`, the support transport, and the Paper1 force estimate. The added `hv`, `hvper`, `δ`, and placement hypotheses are named and used by the cited source/bridge lemmas; none is a vacuous `⊤` or empty-interval assumption. The probe restates both Spec fields and closes them by `exact` (`research/T17/probes/derivative_bounds_closes.lean`), and its nonvacuity declaration is axioms-clean.

## gaps
No missing U5/U6 lemma was found. A whole-tree search of `formalization/NSFormalization/Section4` found no duplicate `physical_mixed_derivative_bound` or `physicalForce_spatial_derivative_bound`; only unrelated `derivative_bound` text occurs. The report correctly records the remaining assembly obligation that supplies global `ContDiff ℝ ∞ v` and `D.ε₀ ≤ 1`. This is a note for downstream assembly, not a defect in these transport theorems.

One exact-note fix: the report says “the six module declarations and three probe declarations” but the shown axioms output contains six module declarations and three probe declarations only after counting the probe fields/nonvacuity; clarify this counting sentence if the report is reused. No code change is required.

The required substantive negative mutation was run in `research/T17/probes/rev385_mutated.lean`, changing the correction exponent from `2*j+m` to `2*j+m+1`. Lean rejected it at line 81 with a type mismatch: the Paper1 result has exponent `2 * j + m` while the mutated goal expects `2 * j + m + 1`.

## commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionDeriv NSFormalization.Section3.T17.ForceDeriv`: success (0 errors; only pre-existing replay linter warnings).
- `lake env lean` on both modules, `research/T17/probes/derivative_bounds_closes.lean`, and `research/T17/axioms_u5u6.lean`: success. Every printed declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- `make check`: success.
- `scripts/gates.sh NSFormalization.Section3.T17.CorrectionDeriv NSFormalization.Section3.T17.ForceDeriv`: `== gates OK`; mutation suite passed and `check_contracts.py --base-ref origin/erenup/integration-section3` reported `base_compatibility_checked: true`.
- Hygiene: `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the two new modules and lane research/report files; no existing module is modified. `rg` over the lane files finds no `sorry`, `admit`, `axiom`, or `native_decide`.
