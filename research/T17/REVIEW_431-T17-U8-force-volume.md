REJECT

## what the lane claims

The report claims U8 is complete: an explicit constant `spatialVolumeConst θR = (4/3)π θR^3`, its nonnegativity, and concrete `correctionData` bounds for spatial torus support and temporal support (`research/T17/REPORT_431.md:7-31`). It also claims the only extra regularity premise is the documented G1 `hv` (`research/T17/REPORT_431.md:48-50`).

## what is in Lean

The constant is defined as `Real.pi * 4 / 3 * θR ^ 3` at `formalization/NSFormalization/Section3/T17/ForceVolume.lean:307-309`, with nonnegativity requiring `hθR` at `:313-316`. The spatial theorem has an additional explicit premise `(hθR : 0 ≤ θR)` at `:330`; its conclusion is the expected `ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3)` bound at `:332-336`. The temporal theorem has the expected `4 * ε ^ 2` conclusion at `:357-360`.

The canonical API fields are quantified over only their record data and epsilon (`formalization/NSFormalization/Section3/T17/Correction.lean:182-188`), and the spec repeats those field shapes (`research/T17/Spec.lean:861-868`). The probe confirms the record-field shape by `A.force_spatial_volume` and `A.force_time_length` (`research/T17/probes/force_volume_closes.lean:39-53`), but it does not remove the extra `hθR` from the new concrete theorem.

## gaps

1. **Blocking statement-fidelity error:** `hθR : 0 ≤ θR` is a second extra premise in `force_spatial_volume` (`ForceVolume.lean:330`), while the lane ground rules allow only documented G1 `hv` as an extra premise. The report openly acknowledges this extra premise (`REPORT_431.md:48-50`). Fix by obtaining nonnegativity from the canonical data without adding a theorem premise, or revise the canonical contract/brief before reimplementing; an exact one-line documentation fix cannot make the present theorem satisfy the stated target.
2. The report's statement that the theorem fields are “literally” canonical is therefore overstated: the probe's `A.force_*` examples are canonical, but the delivered theorems are concrete restatements with additional hypotheses (`ForceVolume.lean:321-365`, probe `:65-128`).
3. No missing Section 4 analogue was found: `grep -rn` for `force_spatial_volume`/`force_time_length` under `formalization/NSFormalization/Section4` returned no matches.

## commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceVolume`: completed successfully (10018 jobs, 0 errors; inherited dependency warnings were emitted).
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T17/ForceVolume.lean`: 0 module errors.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T17/probes/force_volume_closes.lean`: 0 errors.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T17/axioms_u8.lean`: all 25 declarations reported exactly `[propext, Classical.choice, Quot.sound]`.
- `scripts/gates.sh NSFormalization.Section3.T17.ForceVolume`: build, `make test`, mutation suite, and contract checks ran; `make check` reported its normal plan/source-hash diagnostics and completed the listed checks.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: **failed** with `AssertionError: Removed stable specification: verification/Contracts/V1/AffineVariation` (base compatibility/infrastructure mismatch).
- Hygiene grep over `ForceVolume.lean` found no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`.
- Negative probes were run as reported: wrong volume exponent failed with expected type mismatch (`research/T17/probes/rev431_wrong_volume_exponent.lean`), and wrong temporal constant failed with expected type mismatch (`research/T17/probes/rev431_wrong_time_length.lean`).

REJECT — fixes: remove the unauthorized `hθR` premise (or first change the governing contract/brief), then rerun the reviewer gates including the base-ref contract check.
