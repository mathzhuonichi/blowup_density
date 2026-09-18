REJECT

## what the lane claims

The report claims coefficientwise Duhamel differentiation (`mild_coeff_hasDerivAt`, `mild_physicalCoeff_hasDerivAt`), a first time derivative of the physical velocity, and `momentum_of_pressure` (report §1; declarations at [MildMomentum.lean:220](/data_8T/ping/blowup_density/.claude/worktrees/327-T11-U9d2b-momentum/formalization/NSFormalization/Section3/T11/MildMomentum.lean:220), [MildMomentum.lean:257](/data_8T/ping/blowup_density/.claude/worktrees/327-T11-U9d2b-momentum/formalization/NSFormalization/Section3/T11/MildMomentum.lean:257), [MildMomentum.lean:1187](/data_8T/ping/blowup_density/.claude/worktrees/327-T11-U9d2b-momentum/formalization/NSFormalization/Section3/T11/MildMomentum.lean:1187)). The report explicitly concedes that the requested joint `ClassicalSolutionT.velocity_smooth` field is not proved (§3, and probe lines 10–17).

## what is in Lean

The coefficient statements do typecheck with the displayed signs and weighted/unweighted terms ([MildMomentum.lean:220-274]). The physical-field derivative theorem is proved only with both `hu : PersistenceInput T u` and `hF : PersistenceInput T F` ([MildMomentum.lean:948-961]); the momentum theorem repeats that extra force-path persistence hypothesis ([MildMomentum.lean:1187-1205]). Thus the lane does not meet the brief's single allowed named input (`PersistenceInput T u`): `PersistenceInput T F` is an additional hypothesis, regardless of being the same predicate. Moreover, the target joint smoothness is knowingly absent, so this is not a complete delivery of (ii).

The nonzero instance is substantive and checks `u 0 ≠ 0` ([MildMomentum.lean:1467-1510]). The report's gap claim was searched across `formalization/NSFormalization/Section4` with `grep -rn`; no declaration named `ClassicalSolutionT.velocity_smooth` or `mild_coeff_hasDerivAt` was found there.

## gaps

1. **Blocking, statement fidelity:** remove the extra `hF : PersistenceInput T F` from the advertised theorem interface, or explicitly record it as the one permitted additional named input with its exact role and update the lane brief/status. Current claims call the result unconditional modulo ordinary data while silently requiring this second persistence input ([MildMomentum.lean:948-961], [MildMomentum.lean:1187-1205]).
2. **Blocking, completeness:** prove the requested `ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico 0 T ×ˢ univ)` field or mark the lane incomplete for (ii); the report and probe explicitly leave it open ([mild_momentum_closes.lean:10-17]).
3. **Negative check:** the original probe has no substantive mutation. I created `research/T11/probes/rev327_mutation.lean`, flipped the diffusion sign, and Lean failed at line 50 with `Type mismatch ... has type ... ↑(-(ν * periodicAngularFrequencySq k)) ... but is expected ... ↑(ν * periodicAngularFrequencySq k)`.

## commands and results

* `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildMomentum`: `Build completed successfully (9987 jobs).` The replay emitted pre-existing warnings from dependency modules; the target itself had no error.
* `lake env lean` on the module, `mild_momentum_closes.lean`, and `axioms_mild_momentum.lean`: each produced no output and exit 0.
* `make check`: architecture checks and contract policy tests passed (`13 tests ... OK`; work queue consistent). The output also reports the repository's pre-existing copied-source `sorry` token and `source_hashes_match: false`.
* `scripts/gates.sh NSFormalization.Section3.T11.MildMomentum`: `== gates OK`; mutation suite passed and `check_contracts` reported `base_compatibility_checked: true`.
* `git diff --name-only origin/erenup/integration-section3...HEAD`: only the new lane module and research records are changed; no existing module is modified. Grep of the new module found no `sorry`, `admit`, `axiom`, or `native_decide`.
* Axioms file checks all declarations against `[propext, Classical.choice, Quot.sound]`.
