ACCEPT-WITH-NOTES

## what the lane claims

The report claims the stronger `IsPeriodicSpatial` plus `MemLp` bridge, the requested smooth corollary, and a finiteness corollary. These are the declarations actually present at `formalization/NSFormalization/Section3/T15/ParsevalZero.lean:28-39`, `:52-54`, and `:56-59`. The order-zero norm is the stated infimum over representing data (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:116-120`); the cited supporting lemmas have the claimed hypotheses: reverse Parseval requires periodicity and `MemLp` (`formalization/NSFormalization/Section3/T10/Parseval.lean:59-63`), forward Parseval requires a representing datum and `MemLp` (`:115-119`), and uniqueness applies to two representing data (`formalization/NSFormalization/Section3/T10/DatumBasics.lean:128-137`). No vacuous hypothesis or unused named input was found.

## what is in Lean

The proof constructs a datum with `parseval_backward`, collapses the infimum using `iInf_le_of_le`, `le_iInf`, and `datum_unique`, then applies `parseval_forward` (`ParsevalZero.lean:32-39`). The smooth helper obtains vector `MemLp` componentwise (`:43-50`), and the probe supplies a nonzero constant mode (`research/T15/probes/parseval_zero_closes.lean:18-35`). No `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` occurs in the lane files. `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the lane module and research records/probe.

## gaps

No mathematical gap was found, and `grep -rn` over `formalization/NSFormalization/Section4` found no competing `periodicSobolevENorm_zero` declaration. The report should add the negative mutation result and hygiene scan to its verification section. It should also correct the gate command bookkeeping: `make check` from `verification/` exits `2` with `make: *** No rule to make target 'check'. Stop.`, while `scripts/gates.sh NSFormalization.Section3.T15.ParsevalZero` passes; `check_contracts.py` is at `experiments/check_contracts.py` (the attempted repository-root path does not exist). These are one-line report fixes and do not affect the Lean proof.

## commands and results

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.ParsevalZero`: `Build completed successfully (9361 jobs).`
* `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/ParsevalZero.lean`: exit `0`, no output.
* Probe and axiom audit both exit `0`; the audit prints exactly `[propext, Classical.choice, Quot.sound]` for all three public declarations.
* Negative probe changing the RHS to `eLpNorm ... + 1` fails with `unsolved goals` and `eLpNorm ... = eLpNorm ... + 1`.
* `scripts/gates.sh NSFormalization.Section3.T15.ParsevalZero`: `== gates OK` (including mutation suite and contract check).
* `make check`: unavailable in this checkout, exact output recorded above.

ACCEPT-WITH-NOTES — fixes: add the negative/hygiene results to `REPORT_363.md`; record the unavailable `make check` target and use `experiments/check_contracts.py` if rerunning that standalone command.
