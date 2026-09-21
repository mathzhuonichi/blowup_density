ACCEPT-WITH-NOTES

## what the lane claims

The report claims `force_smooth` and `force_support` over raw `U`/`F`, with explicit `0 < τ₀` and (for smoothness) `τ₁ < 1`, and says the report file was not created. The paper/spec fields are the quantified clauses at [research/T24/Spec.lean:1025](research/T24/Spec.lean:1025) and [research/T24/Spec.lean:1032](research/T24/Spec.lean:1032); the raw packet support predicate is [verification/Contracts/V1/Packet.lean:134](verification/Contracts/V1/Packet.lean:134).

## what is in Lean

The implementation exists at [formalization/NSFormalization/Section3/T24/AffineForce.lean:158](formalization/NSFormalization/Section3/T24/AffineForce.lean:158) and [formalization/NSFormalization/Section3/T24/AffineForce.lean:199](formalization/NSFormalization/Section3/T24/AffineForce.lean:199). The theorem bodies quantify `∀ b`, require `AffineAdmissible`, and conclude the claimed global `ContDiff` and `CompactPositiveTimeSupport` predicates. The helper support inclusion is explicit at [AffineForce.lean:181](formalization/NSFormalization/Section3/T24/AffineForce.lean:181), and the cylinder-to-positive-time argument is at [AffineForce.lean:79](formalization/NSFormalization/Section3/T24/AffineForce.lean:79). `#print axioms` for all seven declarations produced only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` occurs in the lane module. `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the new lane module and research records/probes.

The added explicit window hypotheses are mathematically load-bearing for the smoothness proof and are permitted by the brief's explicit-carry route. `force_support` correctly does not inspect `U` and only uses `0 < τ₀`.

## gaps

1. **Minor report inconsistency (documentation):** `REPORT_414.md` says it was not created, but the file exists in the lane. Fix the sentence/report provenance if this report is retained.
2. **Gate-command note:** running `make check` from `verification/` has no `check` target (`make: *** No rule to make target 'check'. Stop.`); the repository-root `make check` succeeds. The lane report should state the working directory for this gate.
3. The report's stated “no gaps” is otherwise supported. A whole-tree grep of `formalization/NSFormalization/Section4` found no missing `force_smooth`/`force_support` theorem corresponding to these T24 declarations.

Negative mutation: `research/T24/probes/rev414_mutation.lean` changed the smoothness window hypothesis from `τ₁ < 1` to `τ₁ < 2`; Lean rejected the attempted proof at line 13 with `linarith failed to find a contradiction` and context `a✝ : 1 ≤ τ₁ ⊢ False`, confirming the substantive constant change breaks the proof.

## commands and results

- `. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineForce`: `Build completed successfully (3008 jobs)`.
- `lake env lean` on `AffineForce.lean`: exit 0, no output.
- `lake env lean` on `axioms_ua4.lean`: seven declarations, each standard three axioms.
- `lake env lean` on `affine_force_closes.lean`: six declarations, standard three axioms.
- `lake env lean` on `affine_force_nonzero.lean`: four declarations, standard three axioms.
- Root `LEAN_NUM_THREADS=6 make check`: exit 0. Verification-directory `make check` was unavailable as noted above.
- `LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T24.AffineForce`: `== gates OK`; mutation suite passed and contract base compatibility was true.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: base compatibility checked true.
- Hygiene grep found no forbidden tokens in the lane module.
