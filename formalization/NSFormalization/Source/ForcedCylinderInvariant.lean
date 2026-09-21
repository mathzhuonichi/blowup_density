import NSFormalization.Source.ForcedCylinderTranslation

/-! Positive-time forced cylinder solutions fixed by every auxiliary-angle translation. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NSFormalization.Source.ForcedCylinderLocal
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerQuadraticSource EulerSobolevHeat EulerDivergenceFreeHeat EulerVolterraConvolution
open scoped Topology
variable (period : ℝ) [Fact (0 < period)]

/-- The source translation, packaged with its already-proved norm preservation. -/
def translationIsometry (q : ℕ) (a : LiftDomain period) :
    SobolevSpace period q →ₗᵢ[ℝ] SobolevSpace period q where
  toLinearMap := (sobolevTranslation period q a).toLinearMap
  norm_map' := sobolevTranslation_norm period a

/-- A fixed forcing makes the actual projected nonlinear source covariant. -/
theorem source_translation {q : ℕ} (hq : 6 ≤ q) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace period q)) (a : LiftDomain period)
    (hf : ∀ t, sobolevTranslation period q a (f t) = f t)
    (t : Icc (0 : ℝ) S) (u : SobolevSpace period (q + 1)) :
    (coefficients period hq f).apply t (sobolevTranslation period (q + 1) a u) =
      sobolevTranslation period q a ((coefficients period hq f).apply t u) := by
  rw [source_eq, source_eq, advection_translation, ← leray_translation]
  simp only [map_sub, hf]

/-- The existing local solver and its retained contraction budget yield an actual
angle-invariant forced mild solution, with the original divergence constraint. -/
theorem exists_local_forced_mild_invariant {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace period (q + 1))
    (hu₀ : value period u₀ ∈ divergenceFreeSpace period 1 0)
    (f : C(Icc (0 : ℝ) S, SobolevSpace period q))
    (hi : ∀ θ : AddCircle period, sobolevTranslation period (q + 1) (0, θ) u₀ = u₀)
    (hf : ∀ (θ : AddCircle period) t, sobolevTranslation period q (0, θ) (f t) = f t) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)),
        ‖u‖ ≤ ‖u₀‖ + 1 ∧ u ⟨0, le_rfl, hT.le⟩ = u₀ ∧
        (∀ t, value period (u t) ∈ divergenceFreeSpace period 1 0) ∧
        (∀ t, u t = quadraticDuhamel period ν hν hT.le hTS
          (coefficients period hq f) u₀ u t) ∧
        ∀ (θ : AddCircle period) t, sobolevTranslation period (q + 1) (0, θ) (u t) = u t := by
  let C := coefficients period hq f
  let R := ‖u₀‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨T, hT, hTS, hb, hs⟩ := exists_positive_time_budget ν (C.ballBound R) (C.ballLipschitz R) 1 S (by norm_num) hS
  let F := (C.comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q + 1) => F p.1 p.2) :=
    (C.comp (timeInclusion hTS)).continuous
  have hFM (t : Icc (0 : ℝ) T) (u : SobolevSpace period (q + 1)) (hu : ‖u‖ ≤ R) :
      ‖F t u‖ ≤ C.ballBound R := C.apply_bound R hR (timeInclusion hTS t) u hu
  have hFL (t : Icc (0 : ℝ) T) (u v : SobolevSpace period (q + 1)) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
      ‖F t u - F t v‖ ≤ C.ballLipschitz R * ‖u - v‖ :=
    C.apply_sub_bound R hR (timeInclusion hTS t) u v hu hv
  have hbudget : ‖u₀‖ + (T + 2 * parabolicConstant ν * Real.sqrt T) * C.ballBound R ≤ R :=
    add_le_add (le_refl ‖u₀‖) hb.le
  obtain ⟨u, hu, hsol⟩ := exists_viscous_mild_solution period q ν hν T hT.le u₀ F hF R
    (C.ballBound R) (C.ballLipschitz R) hR (C.ballBound_nonneg R hR)
    (C.ballLipschitz_nonneg R hR) hFM hFL hbudget hs
  refine ⟨T, hT, hTS, u, hu, ?_, ?_, hsol, ?_⟩
  · have hzero := hsol ⟨0, le_rfl, hT.le⟩
    simpa only [mul_zero, Real.toNNReal_zero, heatOperator_zero, intervalIntegral.integral_same, add_zero] using hzero
  · have hz := mild_solution_preserves_gradient_zero period 1 0 ν hν T hT.le u₀
      ((gradientEvaluation_zero_iff period 1 0 u₀).mpr hu₀) F hF
      (fun t v => by
        change gradientProjection period 1 0 (value period (C.apply (timeInclusion hTS t) v)) = 0
        rw [source_eq]
        exact leray_gradient_zero period _) u hsol
    exact fun t => (gradientEvaluation_zero_iff period 1 0 (u t)).mp (hz t)
  · intro θ t
    let A := sobolevTranslation period (q + 1) (0, θ)
    let v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)) :=
      ⟨fun s => A (u s), A.continuous.comp u.continuous⟩
    have hv : ‖v‖ ≤ R := by
      apply (ContinuousMap.norm_le _ hR).mpr
      intro s
      change ‖sobolevTranslation period (q + 1) (0, θ) (u s)‖ ≤ R
      rw [sobolevTranslation_norm]
      exact (ContinuousMap.norm_coe_le_norm u s).trans hu
    have hcov (s : Icc (0 : ℝ) T) (w : SobolevSpace period (q + 1)) :
        F s (A w) = sobolevTranslation period q (0, θ) (F s w) :=
      source_translation period hq f (0, θ) (hf θ) (timeInclusion hTS s) w
    have hsolv (s : Icc (0 : ℝ) T) :
        v s = heatOperator period (q + 1) (2 * ν * s.val).toNNReal u₀ +
          ∫ r in (0 : ℝ)..s.val, heatKernel period q ν hν r
            (F (projIcc 0 T hT.le (s.val - r)) (v (projIcc 0 T hT.le (s.val - r)))) := by
      change A (u s) = _
      rw [hsol s, map_add]
      have hfree : A (heatOperator period (q + 1) (2 * ν * s.val).toNNReal u₀) =
          heatOperator period (q + 1) (2 * ν * s.val).toNNReal u₀ := by
        dsimp [A]
        rw [← heatOperator_translation, hi θ]
      rw [hfree]
      congr 1
      change (translationIsometry period (q + 1) (0, θ))
        (∫ r in (0 : ℝ)..s.val, heatKernel period q ν hν r
          (F (projIcc 0 T hT.le (s.val - r)) (u (projIcc 0 T hT.le (s.val - r))))) = _
      rw [← (translationIsometry period (q + 1) (0, θ)).intervalIntegral_comp_comm]
      apply intervalIntegral.integral_congr
      intro r _
      change A (heatKernel period q ν hν r (F _ (u _))) = heatKernel period q ν hν r (F _ (A (u _)))
      rw [hcov, heatKernel_translation]
    have hsmall : kernelMass T (parabolicKernelBound ν) * C.ballLipschitz R < 1 := by
      simpa only [kernelMass, parabolicKernelBound_integral ν T hT.le] using hs
    have huv := mild_solution_unique T hT.le (heatKernel period q ν hν) (parabolicKernelBound ν)
      (heatKernel_joint_continuous period q ν hν) (parabolicKernelBound_integrable ν T hT.le)
      (fun r hr => parabolicKernelBound_nonneg ν r hr.1)
      (fun r hr y => heatKernel_bound period q ν hν r hr.1 y)
      (freeHeatPath period (q + 1) ν T u₀) F hF R (C.ballLipschitz R)
      (C.ballLipschitz_nonneg R hR) hFL hsmall v u hv hu hsolv hsol
    exact congrArg (fun w : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)) => w t) huv

end NSFormalization.Source.ForcedCylinderLocal
