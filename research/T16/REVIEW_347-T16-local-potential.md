ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker report is explicitly an honest partial (`research/T16/REPORT_347.md:1-5,60-88`): it does not claim a general proof of `localPotentialStatement`, and it identifies the two residual analytic units.  That scope is permitted by the lane brief's honest-partial rule.  The report claims the canonical helper definitions, the two cutoff constructions, the threshold arithmetic, the complete zero-reference API, and the canonical/spec conversion probe (`research/T16/REPORT_347.md:14-48`).

The requested mathematical interface is the reconciled API in `research/T16/Spec.lean:96-136,145-319,328-336`, matching the paper's cutoff, radial potential, correction, periodicity, support, and cancellation clauses (`paper/sections/03-torus.tex:167-193,196-215`).  The module has the same four helper definitions (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:70-89`), the same `CutoffData` fields (`:96-110`), the same 26 API fields (`:115-162`), and the same main proposition (`:166-174`).

## 2. What is in Lean

The probe copies the Spec declarations and elaborates them (`research/T16/probes/api_on_canonical.lean:29-338`).  The four helper equalities are proved by `rfl` (`:358-370`).  The `CutoffData` structure exception is handled by fieldwise constructors with `rfl` round trips (`:374-388`), and every `LocalPotentialAPI` field is transferred in both directions (`:392-456`).  The module-to-Spec statement bridge has the exact main quantifier order and all premises (`:460-465`).

The proved mathematics is real and non-vacuous:

- `exists_originCutoff` gives smooth compact support, an open plateau containing `K`, a positive radius, support inclusion, and the `[0,1]` range (`formalization/NSFormalization/Section3/T16/LocalPotential.lean:219-240`).
- `exists_timeCutoff` gives the `[0,1]` range, equality on `[-1,1]`, and support in `(-2,2)` (`:245-260`).
- `exists_threshold` proves both strict small-scale inequalities for every `ε ∈ Ioc 0 ε₀` (`:264-287`).
- `localPotential_zero` constructs all 26 API fields for `v = 0`, including the actual cutoffs, threshold, zero potential, and zero correction (`:295-364`).  The transported `v=0,U=0,K={0}` example is in the probe (`research/T16/probes/api_on_canonical.lean:467-485`).

The source has no declaration-form `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` occurrence (anchored scan: no output).  No anonymous instances occur.  `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the new T16 module and research records; no existing module is modified.  The nine audited declarations print only `[propext, Classical.choice, Quot.sound]` (`research/T16/axioms_local_potential.lean:9-17`).

## 3. Gaps and review notes

The missing general theorem is disclosed rather than hidden: there is no `theorem localPotential`; only the proposition definition at `LocalPotential.lean:166-174` and the special-case theorem at `:295-299`.  This is acceptable here as the brief expressly allows an honest partial, but the two following residuals remain open.

1. **Radial potential locality.**  The cited I02 curl theorem requires global spatial smoothness and divergence-freeness on `I ×ˢ univ` (`formalization/NSFormalization/Section4/I02/Reference.lean:86-110`), whereas T16's proposition supplies only `I ×ˢ ball x₀ r` (`research/T16/Spec.lean:328-335`).  The worker's recorded application failure is exact (`research/T16/ATTEMPTS.md:45-58`):

   ```text
   error: Application type mismatch: The argument
     hv
   has type
     ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ Metric.ball x₀ r)
   but is expected to have type
     ContDiffOn ℝ ∞ v (Ioo 0 (T + δ) ×ˢ univ)
   ```

   The proposed ball-local companion statements are concrete (`research/T16/ATTEMPTS.md:68-81`), not a goal alias.  The existing `exists_local_truncation`, `timePotential_contDiffOn`, and `spatialCurl_timePotential_on` are global-domain lemmas (`Reference.lean:68-110`), and `exists_prescribed_cutoff` is only the cutoff construction (`Prescribed.lean:39-55`).  Whole-tree searches found no `timePotential_contDiffOn_ball` or `spatialCurl_timePotential_on_ball` declaration.

2. **Periodic correction.**  The API genuinely requires a periodic lift and periodic support (`LocalPotential.lean:148-162`), so the worker correctly does not pretend that a compact chart correction is already enough.  The residual lift, local-finiteness, smoothness, periodicity, support, divergence, chart formula, and cancellation obligations are listed concretely in `research/T16/ATTEMPTS.md:91-125` and `research/T16/SPEC_ISSUES.md:38-50`.  The required whole-tree searches found no corresponding Section 4 lift theorem, no T10 lattice-translate bridge, and no periodic-set invariance theorem; the vendor only has an unrelated `tsum_eq_single` use (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:240`).

3. **Reviewer negative check.**  The added probe changes the main API support window from `2 * ε ^ 2` to `3 * ε ^ 2` while retaining every argument (`research/T16/probes/rev347_negative.lean:6-15`).  It fails substantively, not by argument dropping:

   ```text
   ../research/T16/probes/rev347_negative.lean:15:2: error: Type mismatch
     hD.correction_support ε hε
   has type
     tsupport (D.correction ε) ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ univ
   but is expected to have type
     tsupport (D.correction ε) ⊆ Ioo (T - 3 * ε ^ 2) (T + 3 * ε ^ 2) ×ˢ univ
   ```

4. **Current-base gate.**  The lane does not touch `verification/`, so the base-compatibility gate is conditional in the brief.  For completeness, I ran it.  The current `origin/erenup/integration-section3` is newer than this lane's merge base and contains `verification/Contracts/V1/TorusLocalTheory.lean`; this checkout predates that stable file.  Therefore the current-base check and the final `scripts/gates.sh` phase fail with the stale-base error below.  Against the merge-base commit `e1efac7a92f16296c91c367e6680ccdaac86ecf1`, the same checker ends with `"base_compatibility_checked": true`.  Before merge, synchronize the lane with the current integration branch and rerun the gate.

5. **Report-only exact fixes.**  `research/T16/REPORT_347.md:14-16` says “All 6 Spec objects” but lists seven declarations (including `localPotentialStatement`); change it to “All 7 Spec declarations”.  `research/T16/REPORT_347.md:83-88` says “all eight `correction_*` fields”, but the API has seven (`:140-162`); change “eight” to “seven”.  The zero-case theorem's `_hr2` and `_hU` binders are explicitly named but unused (`LocalPotential.lean:295-299`); either remove those two premises or add one sentence documenting that the zero construction is independent of them.

## 4. Commands and results

All Lake commands below used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran from `verification/`; Lake was run one command at a time.

| Command | Result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LocalPotential` | exit 0; final line `Build completed successfully (9357 jobs).`  The output also replayed pre-existing dependency linter warnings; none named `T16/LocalPotential.lean`. |
| `LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T16/LocalPotential.lean` | exit 0, no output |
| `LEAN_NUM_THREADS=6 lake env lean ../research/T16/probes/api_on_canonical.lean` | exit 0; exactly six lines, each ending `depends on axioms: [propext, Classical.choice, Quot.sound]` (the declarations are `localPotential_zero`, `specStatement_of_module`, `api_toModule`, `api_ofModule`, `latticeVector_eq`, `periodicScaledPacket_eq`) |
| `LEAN_NUM_THREADS=6 lake env lean ../research/T16/axioms_local_potential.lean` | exit 0; exactly nine lines, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/T16/probes/rev347_negative.lean` | expected exit 1 with the substantive `2 * ε ^ 2` versus `3 * ε ^ 2` type error reproduced in §3 |
| `make check` | exit 0; `test_contract_policy.py` prints `.............` then `OK`; `check_work_queue.py` prints `45 work items: ownership, contract registration and task cards consistent.`  The architecture scan reports the pre-existing copied-source `BoundaryCorollary.lean:90` token and `source_hashes_match: false`, outside this lane. |
| `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T16.LocalPotential` | exit 1 only at the current-base check.  The preceding mutation tail is exact: `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed. This is an infrastructure check, not a PDE proof.` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` | exit 1: `AssertionError: Removed stable specification: verification/Contracts/V1/TorusLocalTheory.lean` |
| `python3 experiments/check_contracts.py --base-ref e1efac7a92f16296c91c367e6680ccdaac86ecf1` | exit 0; final JSON has `"base_compatibility_checked": true` |

The required cited-paper lines were opened with `sed -n '155,220p' paper/sections/03-torus.tex`; the cited I02 declarations were opened with `sed -n` at `Reference.lean:68-110`, `Prescribed.lean:39-55`, and `Support.lean:26-91`.  The whole-tree missing-lemma searches returned no ball-local potential declarations or periodic-lift bridge declarations.

Fixes: correct the two report counts, remove/document the two unused zero-case premises, and update the lane to the current integration base before rerunning the current-base gate.  The mathematical residuals should remain in the follow-up lanes rather than being hidden in this report.
