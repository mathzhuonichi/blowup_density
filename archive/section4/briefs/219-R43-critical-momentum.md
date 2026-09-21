# Lane 219-R43-critical-momentum — close lane 216's `CriticalDatumInputs` (time smoothness + datum-level momentum identity of the half-order velocity path) for an arbitrary classical solution, making eq:Rcritical1 unconditional

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/219-R43-critical-momentum` (git branch `erenup/219-R43-critical-momentum`, based on lane 216's branch `erenup/216-R43-critical-datum-path`
= `origin/erenup/integration` + `Section4/R43/CriticalDatumPath.lean`). Read that module first (`ofSobolevScalar`/`ofSobolevVector` — the Bessel-to-homogeneous multiplier
`|ξ|^s (1+|ξ|²)^(-s/2)`; `chosenHomogeneousDatum`; the six `critical*Half` paths; `structure CriticalDatumInputs` `:701-710` — exactly two fields; `criticalDatumPath`,
`exists_criticalDatumPath`, `rcritical1_of_classical`), then `research/R43/REPORT_216.md` §3, `research/R43/ATTEMPTS_CRITICAL_DATUM.md`, and the landed pieces this lane must combine:
- **lane 215** `Section4/A04/RestartFixedForce.lean:146-186` `classical_hasSmoothSobolevPath`: for an ARBITRARY classical solution, the integer-order datum path is `C^∞` in time on
  `Ico 0 T` — proved by covering each time by a local-carrier window (`exists_carrier_window`), `velocity_unique_core` on `shiftedSolution w b` vs the carrier `c.w`, datum uniqueness
  `D01.isSobolevDatum_unique`, and the carrier's `c.regularity.sobolev_smooth m`. **Copy this pattern.**
- **lane 211** `Section4/A01/LocalTheoryBundle.lean` `LocalCarrier` (`hpaths` smooth datum paths of the Duhamel carrier `U`; `G`/`hG_int`: the pressure gradient field
  `pressureGradientOfVelocity ν f velocity`; `w`, `velocity_eq`), `localCarrier`, `ManuscriptLocalRegularity` (`research/A01/Spec.lean:167-230`: which time-derivative/momentum clauses
  it carries at datum level — grep `momentum`/`deriv` there and in `Section4/A01/ManuscriptRegularity.lean`, `LocalSolution.lean`).
- **lane 169** `Section4/A01/DatumPathDeriv.lean:402-432` `exists_differentiable_datumPath`: on the Duhamel carrier the order-`m` datum path (`m ≤ q-1`) has derivative the datum of the
  **projected residual** `projectedResidualOrdinaryPath` at every interior time; lanes 189/195/197 (`A01/PressureRegularity.lean`, `InteriorMomentum.lean`, `LerayBridge.lean`,
  `momentum_of_projected`) identify the projected residual with `νΔu − (u·∇)u − ∇p + f` (the Leray complement of `−(u·∇)u + f` is `∇p`).
- **D01** `Section4/D01/HalfOrder.lean:79-110` `lowerDatumL`/`lowerVectorL s r (hrs : r ≤ s) : RealVectorSobolev s →L[ℝ] RealVectorSobolev r` (continuous linear order lowering);
  `D01/LerayLowering.lean`, `D01/RealPairing.lean`; `IsSobolevDatum` uniqueness; D01's Fourier-symbol lemmas for `Δ`, `∂_j`.
Also `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P5, `research/A01/REPORT_169.md`, `research/A01/REPORT_215.md` (215 is `research/A04/REPORT_215.md`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`, `f = 0`).
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero solutions; consumers copy your binders.

## Goal
`theorem criticalDatumInputs_of_classical (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T) : CriticalDatumInputs w hf`, hence
`exists_criticalDatumPath' : Nonempty (CriticalDatumPath w hf)` and `rcritical1_of_classical' : …` (214's eq:Rcritical1) with **no** `CriticalDatumInputs` binder. Route:
1. **Canonical vs chosen.** `criticalVelocityHalf w t = chosenHomogeneousDatum (1/2) (u(t,·))` is a per-time choice. Prove uniqueness of the homogeneous slice datum
   (`IsHomogeneousSliceDatum s z D₁ → IsHomogeneousSliceDatum s z D₂ → D₁ = D₂`, from a.e. equality of the angular Fourier data — check how 216's `IsHomogeneousSliceDatum` is spelled
   and whether `RealVectorSobolev s` elements are determined by their `FourierData`), so that on `Ico 0 T`: `criticalVelocityHalf w t = ofSobolevVector (1/2) _ (lowerVectorL 1 (1/2) _ (G₁ t))`
   where `G₁` is 215's smooth order-`1` datum path (`classical_hasSmoothSobolevPath` at `m = 1`, or directly the carrier path on each window). Similarly for the other five paths where needed.
2. **Smoothness.** `ofSobolevVector (1/2) _` is (prove it) a continuous linear map `RealVectorSobolev (1/2) →L[ℝ] RealVectorSobolev (1/2)` (bounded multiplier `|ξ|^{1/2}(1+|ξ|²)^{-1/4} ≤ 1`);
   compose with `lowerVectorL` and the smooth path ⇒ `ContDiffOn ℝ ∞ (criticalVelocityHalf w) (Ico 0 T)` (via the pointwise identity of step 1 and `ContDiffOn.congr`).
3. **Momentum.** On each local-carrier window (215's covering), the integer-order path's derivative is the datum of the momentum residual: obtain it from 169's
   `exists_differentiable_datumPath` (derivative = projected residual datum) + the Leray identification (189/195/197) **or** from whatever `ManuscriptLocalRegularity`/`LocalCarrier` already
   exports at datum level (grep first — 211's report lists a "momentum at datum level" clause; if it exists, use it). Then push the identity through `lowerVectorL` and `ofSobolevVector`
   (both CLMs commute with `deriv` and are additive/homogeneous), and match each term with 216's chosen paths by uniqueness (step 1) and 216's symbol lemmas
   (`criticalLaplacian_symbol`, `criticalVelocity_order_shift`). Datum uniqueness of the time derivative: use `HasDerivAt.unique` on the Hilbert carrier.
4. Assembly: `criticalDatumInputs_of_classical`, `exists_criticalDatumPath'`, `rcritical1_of_classical'`.
If step 3 does not close, ship steps 1–2 (closing `velocityHalf_smooth`) and isolate the momentum identity in its **integer-order inhomogeneous** form as ONE named hypothesis
(the smallest statement that a follow-up can prove from 169), with `rcritical1_of_classical'` conditional on it alone.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/CriticalMomentum.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_CRITICAL_MOMENTUM.md`, update `R43_SPLIT.md` (S1 status; G3 slicewise note from 216 stays), conformance `research/R43/axioms_critical_momentum.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.CriticalMomentum` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_219.md`.
