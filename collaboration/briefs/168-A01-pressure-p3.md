# Lane 168-A01-pressure-p3 — A01 constructor rows c4/c9: the pressure of the constructed solution (HANDOFF P7c)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/168-A01-pressure-p3` (git branch
`erenup/168-A01-pressure-p3`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 (rules) and §2 P7 (P7c), and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree. Never touch the root checkout or any other worktree. Never
  `git push`, never merge, never rebase. Committing on your own branch is allowed.
- Lean: `. scripts/lean-env.sh` in every shell; `lake` ONLY from `verification/`
  (`cd verification && LEAN_NUM_THREADS=6 lake build …`); drafts via `lake env lean ../research/A01/<file>.lean`.
- No `sorry`, `admit`, `axiom`, `native_decide`; `set_option maxHeartbeats N in` only per declaration,
  `N ≤ 400000`, commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of
  `formalization/NSFormalization/Section4/{D01,A03,A04,A01,C01}`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
The mild ⇒ classical constructor (`research/A01/REVIEW_SLICE_WIRING.md` §3(b) `CarrierConstructorFull`;
`research/A01/A01_SPLIT.md` rows c1–c9 at `:102-110`, unit **P3**) must produce a pressure
`p : SpaceTimeScalar` with the `ClassicalSolutionR` fields (`Section4/A02/SolutionClass.lean`):
`pressure_smooth : ContDiffOn ℝ ∞ p (Ico 0 T ×ˢ univ)`, `pressure_gradient : ∀ t ∈ Ico 0 T, MemLp (∇p(t,·)) 2 volume`,
and `momentum` (eq:NS residual `= f`), where the pressure is recovered from the velocity by the
Leray projection: `∇p(t,·) = (I − P)(f − (u·∇)u + νΔu)(t,·)` (the tree's `D01.Leray.lerayComplement`,
`Section4/D01/LerayDatum.lean:255`, and the pin `D01.isSobolevDatum_pressureGradient_lerayComplement`,
`Section4/D01/PressureJets.lean:91`, which lane 148 used in `C01/PressureJetPath.lean`).
`A01_SPLIT.md` §d and lane 093/E1: `navierStokesResidual_eq_iff_projected` (grep `Section4/A01`)
turns the projected equation + pressure recovery into the `momentum` field.

What exists for the *given* solution direction: `Section4/D01/Pressure*.lean`, `PressureJets.lean`,
`A04/PressureDrop.lean` (pressure gradient jets from the momentum residual), `C01/PressureJetPath.lean`
(time-continuous `∇p` jets). What is missing is the **construction**: given the candidate velocity
slices (smooth, with all-order data — take as hypotheses a `velocity : SpaceTimeField` with
`hsmooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` and `hslice`/datum facts exactly as in
`research/A01/CONSTRUCTOR_SPLIT.md` if present in this worktree, else as in `REVIEW_SLICE_WIRING.md`),
define `p` and prove the three fields.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean`
   (namespace `NSFormalization.Section4.A01`):
   - `pressureOfVelocity (ν) (f) (velocity) : SpaceTimeScalar` — a potential whose spatial gradient
     is `lerayComplement` of the momentum residual at each time (Helmholtz: find the tree's scalar
     potential construction — grep `potential`, `RadialPotential`, `Helmholtz`, `gradient_of_curlFree`
     in `Section4/A01/RadialPotential.lean`, `D01/OrderZeroCurl.lean`, `B02/`), with a fixed gauge
     (e.g. `p(t,·)` chosen so that the tree's `pressure_normalization` of A02 holds — check
     `Section4/A02/Restrict.lean`);
   - `pressureGradient_pressureOfVelocity`: `∇(pressureOfVelocity …)(t,·) =ᵐ (I − P)(residual)(t,·)`
     (or pointwise for smooth data), then `pressure_gradient_memLp`;
   - `pressure_smooth_of_velocity_smooth`: `ContDiffOn ℝ ∞ p (Ico 0 T ×ˢ univ)` — if joint time
     smoothness needs the same B1-strength input as the velocity, isolate it as a named hypothesis
     and prove the spatial smoothness at each time unconditionally;
   - `momentum_of_projected`: the `momentum` field from the projected equation via
     `navierStokesResidual_eq_iff_projected`.
2. Records: `research/A01/ATTEMPTS_PRESSURE_P3.md`; conformance `research/A01/axioms_pressure_p3.lean`
   (non-vacuity on the zero velocity/zero force: `p = 0`); append a lane-168 note to
   `research/A01/A3_SPLIT.md` row (i) / P3.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorPressure`
(silent), `lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch and end with a four-part report: 1. theorems proved (names, exact statements);
2. what is in Lean now; 3. gaps (named hypotheses, exact statements, error text); 4. commands and results.
Also write it to `research/A01/REPORT_168.md`.
