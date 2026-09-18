REJECT

## what the lane claims

The report claims `nonisolated` proves the Ua8 field from `Spec.lean:1104-1111`, with raw `U,F`, explicit `0 < τ₀` and `τ₁ < 1`, and convergence of the `ℝ≥0∞` `affineCkSeminorm` for velocity and force differences. The paper statement is `paper/sections/03-torus.tex:692-696`. The exact theorem is at `formalization/NSFormalization/Section3/T24/AffineNonisolated.lean:197-207`.

## what is in Lean

The theorem and helper declarations compile. `AffineBasics.lean:50` defines the registered seminorm used by the theorem. The Spec field has the same quantifier order and two `Tendsto` conclusions (`research/T24/Spec.lean:1104-1111`). The probe supplies the contract bridge and a nonzero witness (`research/T24/probes/affine_nonisolated_closes.lean:258-342`). No existing module outside the lane was modified: `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the lane module, report/attempt/status records, probe, and axioms file.

## gaps

The mandatory negative check is missing. `research/T24/ATTEMPTS_UA8.md:71-98` records only Lean spelling/elaboration failures (for example `mul_const`, casts, and an auto-implicit type), while the report explicitly says the failed approaches are “Lean-spelling traps” (`research/T24/REPORT_424.md:52`). Neither file records a scratch mutation changing a substantive main statement (such as replacing `λ²−λ`, flipping a sign, or widening an interval) and the resulting proof-breaking error. The non-vacuity check is present, so this is the sole blocking finding.

The “not in the tree” search requirement is satisfied for the claimed seminorm helper/nonisolated names: `grep -rnE 'nonisolated|ckSeminorm_lt_top_of_contDiff_compact' formalization/NSFormalization/Section4` returned no matching declaration.

## commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineNonisolated` — `Build completed successfully (3009 jobs).`
- `cd verification && lake env lean ../formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` — no output, exit 0.
- Probe and axioms file — exit 0; every printed declaration has exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — exit 0 (`Ran 13 tests ... OK`; `45 work items ... consistent`).
- `scripts/gates.sh NSFormalization.Section3.T24.AffineNonisolated` — build and registered tests completed successfully.
- `python3 check_contracts.py --base-ref origin/erenup/integration-section3` — completed architecture checks; no contract-policy failure.
- Hygiene grep over the new Lean/probe/axioms files found no `sorry`, `admit`, `native_decide`, or declaration-level `axiom`; no `maxHeartbeats` is present.

Fix: add one genuine scratch mutation of a principal constant/sign/interval in the theorem or its force identity, rerun Lean, and record the exact expected error in `ATTEMPTS_UA8.md` (then rerun the probe/gates if the source is restored).
