# Lane 207-A01-tame-assembly — finish `SmoothCylinderCoordinateTame`: opposite-orientation mixed product, Leibniz word identification, combinatorial summation (route A, cylinder)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/207-A01-tame-assembly` (git branch `erenup/207-A01-tame-assembly`, based on branch `erenup/206-A01-smooth-tame`
= `origin/erenup/integration` + lane 205's `CoordinateTame.lean` (`def SmoothCylinderCoordinateTame q hq C`, smooth Leibniz `cylinderLeibniz_eq`/`cylinderCommutatorLeibniz_eq`/
`cylinderCoordinateLeibniz_sign`, transfer `cylinderCoordinateTame`) + lane 206's `SmoothTame.lean` (`cylinderWordMaximum`, `cylinderWordMaximum_logconvex`,
`cylinderWordMaximum_product_le_gradient` with constant 1, `cylinderMixedProduct_left` with constant `‖L‖·sobolevEmbeddingConstant 1 3`)). On integration: lanes 202
(`CommutatorBound.lean`), 200 (`ForcingFamilyBound.lean`), 204 (`SignedPassage.lean`), 196, 193, and the constructor pipeline (`PressureRegularity.lean`,
`ConstructorAssembly.lean`, probe `research/A01/probes/a01_constructor_pipeline.lean`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7,
`research/A01/REPORT_206.md` (§1 exact statements, §3 the three remaining steps), `research/A01/ATTEMPTS_SMOOTH_TAME.md`, `research/A01/REPORT_205.md` §3,
`research/A01/REVIEW_200-A01-forcing-bound.md` §3, and the top 40 lines of `logs/LESSONS.md`. (If `research/A01/REVIEW_206-A01-smooth-tame.md` exists on this branch, read it
first: if it recommends the invariant re-cut route (B) as shorter, follow it instead and say so.)

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data (never as certification of a general premise).
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement.

## Goal
`theorem smoothCylinderCoordinateTame : SmoothCylinderCoordinateTame q hq (C q)` with an **explicit** `C q` (from `sobolevEmbeddingConstant 1 3`, word multiplicities and
lane 196's `mildNormConstant`), hence `cylinderCoordinateTame_exists` unconditional, `CylinderCommutatorBound q hq (…)` (lane 202, with the re-cut constant if `C q > 4·A q`:
prove the one-line lemma that lane 200's chain accepts the larger constant), `forcingFamilyBound_of_cylinder'` unconditional, and — composing with 204/203/201/199/196/193 —
`finiteMildEnergy'`, `hb_of_base''` (the all-order a-priori bound family with no analytic input). Then the **A01 milestone probe** `research/A01/probes/a01_constructor_unconditional.lean`:
import the landed pipeline and state `∃ velocity, ∃ w : ClassicalSolutionR ν (velocity(0,·)) f S, w.velocity = velocity` from `hf`, `ha`, positivity **only**.

## The three remaining steps (lane 206, §3)
1. **Opposite orientation**: the mixed-product estimate with the bounded word block on the transported factor (`cylinderMixedProduct_right`): either by symmetry of `scalarProduct`
   after swapping the roles (check `scalarProduct`'s definition and `transportL2Bilinear_apply`), or by the same `H³ ↪ L^∞` embedding (`sobolevEmbeddingConstant 1 3`) on the
   other factor; keep the constant explicit.
2. **Leibniz word identification**: lane 205's smooth expansion `cylinderCommutatorLeibniz_eq` is stated for smooth `f`; the target quantifies smooth `f` a.e.-equal to `value 1 V`
   — identify each expanded word term with the corresponding `word`/`boundedWordBlock` element of `V` (a.e. identification through `value`, then equality in `LiftL2` — lanes
   153/161's descent/identification lemmas, `value_restrictOperator`, `word_descent_ae_*`).
3. **Combinatorial summation**: sum the mixed-product bounds over all words of the commutator expansion (multiplicities from the recursive Leibniz rule — count them explicitly:
   a word of length `n` expands into at most `2^n` terms, or use the sum-of-`familyNorm` triangle inequality with `Finset.card`), collect into `C q · ‖V|₇‖ · cylinderWordGradient V`
   using `cylinderWordMaximum_product_le_gradient`. Make `C q` a `def` with a docstring deriving it.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/TameAssembly.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_TAME_ASSEMBLY.md`, update `research/A01/A3_SPLIT.md` (A3-M2 rows → DONE if closed), conformance `research/A01/axioms_tame_assembly.lean`,
   the milestone probe.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.TameAssembly` (silent), `lake env lean` on the module (0 output), the axioms file, the probe,
`make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with error text / commands). Also write it to `research/A01/REPORT_207.md`.
