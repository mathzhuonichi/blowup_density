import NSFormalization.Source.OrdinaryForcedLocal
import Euler.BoundedMildContinuation
import Euler.CorrectionContinuation

/-!
(b) invariance PORT — the `[0,S]`-global covariance/uniqueness argument (a fork of
`Source/ForcedCylinderInvariant.lean:30`), CONDITIONAL on the contraction hypothesis
`hsmall : kernelMass S · L < 1`.  Compiles at `maxHeartbeats 300000` (200000/250000 fail;
the cited source runs at 800000, but 300000 = 1.5× the default suffices for this fork).
`set_option maxHeartbeats` is NOT forbidden in this repo — ten merged modules use it
(`REVIEW_A2B.md` §F6a); the earlier "800000 forbidden" gap note was wrong.  The `hfree`
goal is closed by `rfl` because `freeHeatPath … s` is *defined* as `heatOperator … u₀`
(`Euler/SobolevHeatVolterra.lean:50-53`) — the earlier "unsolved goals" was a missing `rfl`.

The `hsmall` hypothesis here need NOT be assumed globally: it is DISCHARGED on every window
`≤ δ` of the continuation (`exists_positive_time_budget` guarantees `kernelMass δ · L < 1`,
`Euler/UniformHeatLocal.lean:42-54`).  See the sibling probes `probe_window_invariance.lean`
and `probe_restart_window_invariance.lean` for the unconditional per-window versions
(reviewer, `REVIEW_A2B.md` §F6b).  This `[0,S]` shape is kept for the record.
-/
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open scoped Topology ContDiff

noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

set_option maxHeartbeats 300000 in
/-- (b) attempt: angle invariance of a global forced mild solution, CONDITIONAL on the
global-window contraction bound `hsmall`.  This localizes the (b) gap to exactly `hsmall`,
which fails for large `S` (kernelMass grows without bound). -/
theorem forced_mild_invariant_of_contraction {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hR : 0 ≤ R) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) (hu : ‖u‖ ≤ R)
    (hsol : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)
    (hsmall : kernelMass S (parabolicKernelBound ν) *
        (coefficients 1 hq (sobolevPath F hF q)).ballLipschitz R < 1) :
    ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set u₀ := ordinarySobolev (q + 1) a.toLp a.translation_contDiff with hu₀def
  set C := coefficients 1 hq (sobolevPath F hF q) with hCdef
  set G := (C.comp (timeInclusion (le_rfl : S ≤ S))).apply with hGdef
  have hG : Continuous (fun p : Icc (0 : ℝ) S × SobolevSpace 1 (q + 1) => G p.1 p.2) :=
    (C.comp (timeInclusion le_rfl)).continuous
  have hf : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 q (0, θ) ((sobolevPath F hF q) t) = (sobolevPath F hF q) t :=
    fun θ t => ordinarySobolev_angle q (F t).toLp (F t).translation_contDiff θ
  have hi : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀ :=
    fun θ => ordinarySobolev_angle (q + 1) a.toLp a.translation_contDiff θ
  have hFL : ∀ (t : Icc (0 : ℝ) S) (x y : SobolevSpace 1 (q + 1)),
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖G t x - G t y‖ ≤ C.ballLipschitz R * ‖x - y‖ :=
    fun t x y hx hy => C.apply_sub_bound R hR (timeInclusion le_rfl t) x y hx hy
  -- rewrite hsol into the free-heat + convolution form (defeq)
  have hsolF : ∀ t : Icc (0 : ℝ) S,
      u t = freeHeatPath 1 (q + 1) ν S u₀ t +
        ∫ r in (0 : ℝ)..t.val, heatKernel 1 q ν hν r
          (G (projIcc 0 S hS.le (t.val - r)) (u (projIcc 0 S hS.le (t.val - r)))) := hsol
  intro θ t
  let A := sobolevTranslation 1 (q + 1) (0, θ)
  let v : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)) :=
    ⟨fun s => A (u s), A.continuous.comp u.continuous⟩
  have hv : ‖v‖ ≤ R := by
    apply (ContinuousMap.norm_le _ hR).mpr
    intro s
    change ‖sobolevTranslation 1 (q + 1) (0, θ) (u s)‖ ≤ R
    rw [sobolevTranslation_norm]
    exact (ContinuousMap.norm_coe_le_norm u s).trans hu
  have hcov : ∀ (s : Icc (0 : ℝ) S) (w : SobolevSpace 1 (q + 1)),
      G s (A w) = sobolevTranslation 1 q (0, θ) (G s w) :=
    fun s w => source_translation 1 hq (sobolevPath F hF q) (0, θ) (hf θ) (timeInclusion le_rfl s) w
  have hsolv : ∀ s : Icc (0 : ℝ) S,
      v s = freeHeatPath 1 (q + 1) ν S u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 S hS.le (s.val - r)) (v (projIcc 0 S hS.le (s.val - r)))) := by
    intro s
    change A (u s) = _
    rw [hsolF s, map_add]
    have hfree : A (freeHeatPath 1 (q + 1) ν S u₀ s) = freeHeatPath 1 (q + 1) ν S u₀ s := by
      change sobolevTranslation 1 (q + 1) (0, θ) (heatOperator 1 (q + 1) (2 * ν * s.val).toNNReal u₀) = _
      rw [← heatOperator_translation, hi θ]
      rfl
    rw [hfree]
    congr 1
    change (translationIsometry 1 (q + 1) (0, θ))
      (∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
        (G (projIcc 0 S hS.le (s.val - r)) (u (projIcc 0 S hS.le (s.val - r))))) = _
    rw [← (translationIsometry 1 (q + 1) (0, θ)).intervalIntegral_comp_comm]
    apply intervalIntegral.integral_congr
    intro r _
    change A (heatKernel 1 q ν hν r (G _ (u _))) = heatKernel 1 q ν hν r (G _ (A (u _)))
    rw [hcov, heatKernel_translation]
  have huv := mild_solution_unique S hS.le (heatKernel 1 q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous 1 q ν hν) (parabolicKernelBound_integrable ν S hS.le)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y)
    (freeHeatPath 1 (q + 1) ν S u₀) G hG R (C.ballLipschitz R)
    (C.ballLipschitz_nonneg R hR) hFL hsmall v u hv hu hsolv hsolF
  exact congrArg (fun w : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)) => w t) huv
