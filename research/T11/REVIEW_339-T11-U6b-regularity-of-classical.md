ACCEPT-WITH-NOTES

## what the lane claims

The report claims the exact U6b theorem, plus the strengthened force-smooth variant and the four API corollaries. The main declaration at `formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean:1148-1152` has exactly the requested binder order and conclusion. The three fields are assembled at `:1140-1146`; `PeriodicLocalRegularity` itself is the three-field structure at `formalization/NSFormalization/Section3/T11/LocalTheory.lean:79-94`. The API corollaries are stated at `:1155-1210` and match the probe's target shapes.

The manuscript citations are directionally correct: the allowed torus data/force classes are in `paper/sections/02-preliminaries.tex:6-25`, the pressure Poisson identity is at `:75-89`, and the classical local-existence context is `:101-115`. The cited proposition does not itself spell out the Lean `PeriodicLocalRegularity` record, so the report should describe those lines as mathematical context rather than as a verbatim source for the record.

## what is in Lean

`sobolev_smooth_of_classical` constructs `datumPathT` and proves both path obligations at `ClassicalRegularity.lean:1132-1138`; `pressure_poisson_of_classical` supplies the second field at `:1105-1125`; and `classicalSolutionT_projected` supplies the third at `:1143-1146`. The main theorem then uses the smooth-force component `hf.1` at `:1152`, so no extra named input is introduced. The four downstream corollaries are proved by the transport/mean-reduction bridges at `:1155-1210`.

The probe closes all claimed target fields and includes a nonzero constant-flow instance (`research/T11/probes/classical_regularity_closes.lean:101-151`). The mutation probe `research/T11/probes/rev339_mutation.lean` changes `0 < ν` to `0 ≤ ν`; Lean rejects the application at line 12 with: `hν has type 0 ≤ ν but is expected to have type 0 < ν`.

## gaps

No mathematical gap was found, and a whole-tree search found the claimed new theorem only in this module (the pre-existing `PeriodicLocalRegularity` declarations are definitions/field projections in `Section3/T11/LocalTheory.lean` and sibling conditional results). The report's “no existing module modified” claim needs qualification: `git diff --name-only origin/erenup/integration-section3...HEAD` also lists `EnergyIdentity.lean`, `HighOrder.lean`, `MildMomentum.lean`, `PLAN.md`, and other unrelated lane records. These appear inherited lane changes, but they violate the literal hygiene check until the branch is compared against the intended lane base or those changes are separated. This is the one review note.

## commands and results

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ClassicalRegularity` — `Build completed successfully (9998 jobs)` (only pre-existing replay warnings).
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean` — no output, exit 0.
* The same `lake env lean` command on `research/T11/probes/classical_regularity_closes.lean` and `research/T11/axioms_classical_regularity.lean` — no output, exit 0; all 82 guarded declarations report exactly `[propext, Classical.choice, Quot.sound]`.
* `make check` — completed; plan, contracts, policy (13 tests), and work queue passed.
* `bash scripts/gates.sh NSFormalization.Section3.T11.ClassicalRegularity` — `== gates OK`; mutation suite reports `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`.
* `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` — `base_compatibility_checked: true`.
* Hygiene grep over the new module found no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`.

ACCEPT-WITH-NOTES — qualify/separate the unrelated files shown by the integration-base diff before merge.
