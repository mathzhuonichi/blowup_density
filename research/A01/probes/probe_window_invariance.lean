import NSFormalization.Source.OrdinaryForcedLocal
import Euler.BoundedMildContinuation
set_option maxHeartbeats 400000
/-!
Reviewer probe (lane 126 review, `research/A01/REVIEW_A2B.md` §F6b, Probe 1), preserved
verbatim and credited to the reviewer.  Angle-invariance of EVERY `R`-bounded forced mild
solution on EVERY window `≤ δ`, with the contraction `hsmall` DISCHARGED (not assumed): the
window length `δ` from `exists_positive_time_budget` guarantees `kernelMass δ · L < 1`
(`Euler/UniformHeatLocal.lean:42-54`), so the continuation's own windows are the uniqueness
regime.  Needs `maxHeartbeats 400000` (300000 fails); ~5 s; standard three axioms.
-/
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerSmoothFieldSobolevTime EulerQuadraticSource
open EulerSobolevHeat EulerVolterraConvolution EulerUniformHeatLocal
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff
noncomputable section
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem probe_window_invariance {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace 1 (q + 1),
          (∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u₀ = u₀) →
          ∀ u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)), ‖u‖ ≤ R →
            (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
              (coefficients 1 hq (sobolevPath F hF q)) u₀ u t) →
            ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  set f := sobolevPath F hF q with hfdef
  set C := coefficients 1 hq f with hCdef
  obtain ⟨δ, hδ, hδS, _, hl⟩ :=
    exists_positive_time_budget ν (C.ballBound R) (C.ballLipschitz R) 1 S (by norm_num) hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro T hT hTS hTδ u₀ hi u hu hsol θ t
  have hsmall : kernelMass T (parabolicKernelBound ν) * C.ballLipschitz R < 1 := by
    have hmass := EulerUniformHeatLocal.parabolic_mass_mono ν T δ hTδ
    have hL := C.ballLipschitz_nonneg R hR
    have := mul_le_mul_of_nonneg_right hmass hL
    simpa only [kernelMass, parabolicKernelBound_integral ν T hT] using this.trans_lt hl
  set G := (C.comp (timeInclusion hTS)).apply with hGdef
  have hG : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace 1 (q + 1) => G p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hf : ∀ (θ : AddCircle (1 : ℝ)) s, sobolevTranslation 1 q (0, θ) (f s) = f s :=
    fun θ s => ordinarySobolev_angle q (F s).toLp (F s).translation_contDiff θ
  have hFL : ∀ (s : Icc (0 : ℝ) T) (x y : SobolevSpace 1 (q + 1)),
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖G s x - G s y‖ ≤ C.ballLipschitz R * ‖x - y‖ :=
    fun s x y hx hy => C.apply_sub_bound R hR (timeInclusion hTS s) x y hx hy
  have hsolF : ∀ s : Icc (0 : ℝ) T,
      u s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r)))) := hsol
  let A := sobolevTranslation 1 (q + 1) (0, θ)
  let v : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) :=
    ⟨fun s => A (u s), A.continuous.comp u.continuous⟩
  have hv : ‖v‖ ≤ R := by
    apply (ContinuousMap.norm_le _ hR).mpr
    intro s
    change ‖sobolevTranslation 1 (q + 1) (0, θ) (u s)‖ ≤ R
    rw [sobolevTranslation_norm]
    exact (ContinuousMap.norm_coe_le_norm u s).trans hu
  have hcov : ∀ (s : Icc (0 : ℝ) T) (w : SobolevSpace 1 (q + 1)),
      G s (A w) = sobolevTranslation 1 q (0, θ) (G s w) :=
    fun s w => source_translation 1 hq f (0, θ) (hf θ) (timeInclusion hTS s) w
  have hsolv : ∀ s : Icc (0 : ℝ) T,
      v s = freeHeatPath 1 (q + 1) ν T u₀ s +
        ∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
          (G (projIcc 0 T hT (s.val - r)) (v (projIcc 0 T hT (s.val - r)))) := by
    intro s
    change A (u s) = _
    rw [hsolF s, map_add]
    have hfree : A (freeHeatPath 1 (q + 1) ν T u₀ s) = freeHeatPath 1 (q + 1) ν T u₀ s := by
      change sobolevTranslation 1 (q + 1) (0, θ)
        (heatOperator 1 (q + 1) (2 * ν * s.val).toNNReal u₀) = _
      rw [← heatOperator_translation, hi θ]
      rfl
    rw [hfree]
    congr 1
    change (translationIsometry 1 (q + 1) (0, θ))
      (∫ r in (0 : ℝ)..s.val, heatKernel 1 q ν hν r
        (G (projIcc 0 T hT (s.val - r)) (u (projIcc 0 T hT (s.val - r))))) = _
    rw [← (translationIsometry 1 (q + 1) (0, θ)).intervalIntegral_comp_comm]
    apply intervalIntegral.integral_congr
    intro r _
    change A (heatKernel 1 q ν hν r (G _ (u _))) = heatKernel 1 q ν hν r (G _ (A (u _)))
    rw [hcov, heatKernel_translation]
  have huv := mild_solution_unique T hT (heatKernel 1 q ν hν) (parabolicKernelBound ν)
    (heatKernel_joint_continuous 1 q ν hν) (parabolicKernelBound_integrable ν T hT)
    (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
    (fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y)
    (freeHeatPath 1 (q + 1) ν T u₀) G hG R (C.ballLipschitz R)
    (C.ballLipschitz_nonneg R hR) hFL hsmall v u hv hu hsolv hsolF
  exact congrArg (fun w : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)) => w t) huv
