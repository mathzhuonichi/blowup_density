ACCEPT-WITH-NOTES

## What the lane claims

The report claims Ua7 is proved with `∃ b : ℕ → VelocityField, (∀ n, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b`, under `0 < r` and `τ₀ < τ₁` [research/T24/REPORT_417.md:7-18]. This matches the Spec field, including quantifier order and conclusion [research/T24/Spec.lean:1085-1087], and the paper's countable disjoint-ball construction [paper/sections/03-torus.tex:688-691].

## What is in Lean

`infinite_dimensional` has exactly that statement [formalization/NSFormalization/Section3/T24/AffineFamily.lean:247-253]. The witness library proves smoothness, compact support, support containment, divergence-free curl, admissibility, and nonzeroness [formalization/NSFormalization/Section3/T24/AffineWitness.lean:94-130,141-146]. The family geometry and disjoint-support linear-independence proof are present [formalization/NSFormalization/Section3/T24/AffineFamily.lean:145-235]. The Spec/contract spelling bridges and non-vacuity checks typecheck in the probe [research/T24/probes/affine_family_closes.lean:61-76,78-100]. `grep -rn` over `formalization/NSFormalization/Section4` found no competing `infinite_dimensional` lemma.

## Gaps

One exact reporting fix: the report says `make check` was run successfully [research/T24/REPORT_417.md:55], but running `make check` from the worktree root gives `make: *** No rule to make target 'check'. Stop.` The command must be recorded as `cd verification && make check`; that command is covered by the successful gates run. The separate command `python3 scripts/check_contracts.py` is also an invalid path (no such root-level file); the valid command is `cd verification && python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`, which returned `"base_compatibility_checked": true`.

The required substantive mutation is documented and reproduces the expected failures: changing `ballRadius` to `r * scale n / 2` yields `linarith failed to find a contradiction` at the containment and separation proofs [research/T24/REPORT_417.md:42]. No additional mathematical gap was found. The unrefactored older probe is a scope/de-duplication note, not a correctness defect [research/T24/REPORT_417.md:32-34].

## Commands and results

From `verification/`, after `. scripts/lean-env.sh` and with `LEAN_NUM_THREADS=6`:

- `lake build NSFormalization.Section3.T24.AffineFamily`: `Build completed successfully (3035 jobs).`
- `lake env lean` on `AffineFamily.lean` and `AffineWitness.lean`: no output.
- `lake env lean` on the probe: only standard axioms, `[propext, Classical.choice, Quot.sound]`.
- `lake env lean` on `axioms_ua7.lean`: all 42 declarations report exactly `[propext, Classical.choice, Quot.sound]`.
- `cd verification && make check`: `13 tests ... OK`; `45 work items ... consistent.`
- `bash scripts/gates.sh NSFormalization.Section3.T24.AffineWitness NSFormalization.Section3.T24.AffineFamily`: `Mutation suite passed`; `base_compatibility_checked: true`; `gates OK`.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`: completed with `base_compatibility_checked: true`.
- Forbidden-token grep over the new Lean files: no `sorry`, `admit`, `axiom`, or `native_decide`; no `maxHeartbeats`.
- `git diff --name-only origin/erenup/integration-section3...HEAD` lists only the two new modules and lane research/report files; no existing module is modified.
