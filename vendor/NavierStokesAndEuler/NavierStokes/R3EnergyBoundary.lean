import NavierStokes.R3EnergyNorms

/-!
# Diffusion and transport boundary estimates

Only the undifferentiated velocity needs a global `L²` bound. Every
derivative in these estimates is multiplied by a compact cutoff.
-/

noncomputable section
namespace NavierStokes.R3EnergyBoundary

open Set Filter MeasureTheory ProblemStatement InnerProductSpace
open R3CompactEnergy R3CutoffSobolev R3WeightedLp R3EnergyNorms
open scoped ContDiff RealInnerProductSpace ENNReal

theorem derivative_eighth {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : Space) :
    fderiv ℝ (fun y => φ y ^ 8) x v = 8 * φ x ^ 7 * fderiv ℝ φ x v := by
  rw [((hφ.differentiable (by simp) x).hasFDerivAt.pow 8).fderiv]
  simp

theorem derivative_eighth_bound {φ : Space → ℝ} {D : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (x v : Space) :
    |fderiv ℝ (fun y => φ y ^ 8) x v| ≤ 8 * φ x ^ 7 * D * ‖v‖ := by
  have hφ0 := (hr x).1
  rw [derivative_eighth hφ, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 8 * φ x ^ 7)]
  have h := (fderiv ℝ φ x).le_opNorm v
  rw [Real.norm_eq_abs] at h
  exact (mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg v)))
    (by positivity)).trans_eq (by ring)

theorem diffusionFlux_le {φ : Space → ℝ} {w : Space → Space} {D : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (hw₂ : MemLp w 2) :
    |diffusionFlux (fun x => φ x ^ 8) w| ≤
      24 * D * lpNorm (weightedDerivativeNorm φ w) 2 volume * lpNorm w 2 volume := by
  have hA := weightedDerivativeNorm_memLp (hφ.of_le (by simp)) hc (hw.of_le (by simp))
  have hAW : Integrable (fun x => weightedDerivativeNorm φ w x * ‖w x‖) :=
    memLp_one_iff_integrable.mp (hw₂.norm.mul' hA)
  have hbound (i : Fin 3) (x : Space) :
      ‖PeriodicIntegration.spatialPartial i (fun y => φ y ^ 8) x *
        ⟪w x, PeriodicIntegration.spatialPartial i w x⟫_ℝ‖ ≤
      8 * D * (weightedDerivativeNorm φ w x * ‖w x‖) := by
    have hφ0 := (hr x).1
    have hi : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
    have hder : ‖PeriodicIntegration.spatialPartial i w x‖ ≤ ‖fderiv ℝ w x‖ := by
      simpa only [PeriodicIntegration.spatialPartial, hi, mul_one] using (fderiv ℝ w x).le_opNorm (coordinateVector i)
    have hφder := derivative_eighth_bound hφ hr hb x (coordinateVector i)
    rw [hi, mul_one] at hφder
    have hpow : φ x ^ 7 ≤ φ x ^ 4 := pow_le_pow_of_le_one (hr x).1 (hr x).2 (by norm_num)
    rw [Real.norm_eq_abs, abs_mul]
    have hinner := (abs_real_inner_le_norm (w x) (PeriodicIntegration.spatialPartial i w x)).trans
      (mul_le_mul_of_nonneg_left hder (norm_nonneg _))
    have hh := mul_le_mul hφder hinner (abs_nonneg _) (by positivity : 0 ≤ 8 * φ x ^ 7 * D)
    have hp := mul_le_mul_of_nonneg_right hpow
      (by positivity : 0 ≤ 8 * D * ‖w x‖ * ‖fderiv ℝ w x‖)
    dsimp only [weightedDerivativeNorm]
    change |(fderiv ℝ (fun y => φ y ^ 8) x) (coordinateVector i)| *
      |⟪w x, PeriodicIntegration.spatialPartial i w x⟫_ℝ| ≤ _
    nlinarith only [hh, hp]
  have hint (i : Fin 3) : |∫ x : Space,
      PeriodicIntegration.spatialPartial i (fun y => φ y ^ 8) x *
        ⟪w x, PeriodicIntegration.spatialPartial i w x⟫_ℝ| ≤
      8 * D * lpNorm (weightedDerivativeNorm φ w) 2 volume * lpNorm w 2 volume := by
    have h := norm_integral_le_of_norm_le (hAW.const_mul (8 * D)) (Eventually.of_forall (hbound i))
    rw [Real.norm_eq_abs, integral_const_mul] at h
    have hh := integral_mul_le hA hw₂.norm (fun x => by
      exact mul_nonneg (by positivity) (norm_nonneg _)) (fun x => norm_nonneg _)
    rw [lpNorm_norm hw₂.1] at hh
    exact h.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))
  unfold diffusionFlux
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => hint i)).trans_eq
  simp
  ring

theorem transportFlux_le {φ : Space → ℝ} {w v : Space → Space} {D U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hr : ∀ x, φ x ∈ Icc (0 : ℝ) 1) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hb : ∀ x, ‖fderiv ℝ φ x‖ ≤ D) (hw₂ : MemLp w 2)
    (hv : ∀ x, ‖v x‖ ≤ ‖w x‖ + U) :
    |transportFlux (fun x => φ x ^ 8) w v| ≤
      8 * D * (lpNorm (fourthWeight φ (fun x => ‖w x‖)) 6 volume ^ (3 / 2 : ℝ) *
        lpNorm w 2 volume ^ (3 / 2 : ℝ) + U * lpNorm w 2 volume ^ 2) := by
  have hpc : HasCompactSupport (fun x => φ x ^ 7) := hc.comp_left (g := fun r : ℝ => r ^ 7) (by norm_num)
  have hQ : Integrable (fun x => φ x ^ 7 * ‖w x‖ ^ 3) :=
    R3CompactIntegration.integrable_mul (hφ.continuous.pow 7) (hw.continuous.norm.pow 3) hpc
  have hW : Integrable (fun x => ‖w x‖ ^ 2) := (memLp_two_iff_integrable_sq hw₂.norm.1).mp hw₂.norm
  have hbound (x : Space) : ‖fderiv ℝ (fun y => φ y ^ 8) x (v x) * ‖w x‖ ^ 2‖ ≤
      8 * D * (φ x ^ 7 * ‖w x‖ ^ 3 + U * ‖w x‖ ^ 2) := by
    have h := derivative_eighth_bound hφ hr hb x (v x)
    have hφ7 : 0 ≤ φ x ^ 7 := pow_nonneg (hr x).1 _
    have hφ1 : φ x ^ 7 ≤ 1 := pow_le_one₀ (hr x).1 (hr x).2
    have hv' := mul_le_mul_of_nonneg_left (hv x) (by positivity : 0 ≤ 8 * φ x ^ 7 * D)
    have hh := mul_le_mul_of_nonneg_right (h.trans hv') (sq_nonneg ‖w x‖)
    have hl := mul_le_mul_of_nonneg_right hφ1 (by positivity : 0 ≤ 8 * D * U * ‖w x‖ ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖w x‖)]
    nlinarith only [hh, hl]
  have hmajor : Integrable (fun x => 8 * D * (φ x ^ 7 * ‖w x‖ ^ 3 + U * ‖w x‖ ^ 2)) :=
    (hQ.add (hW.const_mul U)).const_mul (8 * D)
  have h := norm_integral_le_of_norm_le hmajor (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs, integral_const_mul, integral_add hQ (hW.const_mul U), integral_const_mul,
    ← lpNorm_two_sq hw₂.1] at h
  have hB : MemLp (fourthWeight φ (fun x => ‖w x‖)) 6 := by
    have hpc4 : HasCompactSupport (fun x => φ x ^ 4 * ‖w x‖) :=
      (hc.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num)).mul_right
    exact ((hφ.continuous.pow 4).mul hw.continuous.norm).memLp_of_hasCompactSupport
      hpc4
  have hQbound := cubic_lpNorm hφ.continuous.measurable hw.continuous.norm.measurable hr
    (fun x => norm_nonneg _) hw₂.norm hB
  rw [lpNorm_norm hw₂.1, lpNorm_one_eq_integral_norm hQ.1] at hQbound
  have he (x : Space) : ‖φ x ^ 7 * ‖w x‖ ^ 3‖ = φ x ^ 7 * ‖w x‖ ^ 3 :=
    Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hr x).1 _) (by positivity))
  simp only [he] at hQbound
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hQbound le_rfl) (by positivity))

end NavierStokes.R3EnergyBoundary
