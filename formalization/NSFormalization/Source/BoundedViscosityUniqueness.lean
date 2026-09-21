import NSFormalization.Source.BoundedReferenceUniqueness
import NSFormalization.Source.ViscosityPacket

/-! Positive-viscosity uniqueness by spatial scaling, without changing time. -/
noncomputable section
namespace NSFormalization.Source.BoundedViscosityUniqueness
open Set MeasureTheory NavierStokesR3 NavierStokesR3.ProblemStatement
open NavierStokes.ProblemStatement (spatialDerivative spatialDivergence)
open scoped ContDiff

theorem viscosity_residual_general {a : ℝ} (ha : a ≠ 0) (ν : ℝ)
    (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    residual (a ^ 2 * ν) (viscosityVelocity a u) (viscosityPressure a p) t x =
      a • residual ν u p t (a⁻¹ • x) := by
  simp only [residual, viscosityVelocity, viscosityPressure,
    dilate_temporalDerivative, dilate_advection, dilate_laplacian, dilate_gradient,
    mul_one, sub_zero, one_mul]
  have h₁ : a ^ 2 * a⁻¹ = a := by field_simp
  have h₂ : (a ^ 2 * ν) * (a * (a⁻¹) ^ 2) = a * ν := by field_simp
  rw [h₁]
  simp only [smul_smul, h₂, one_smul, smul_add, smul_sub]

theorem classical_uniqueness_on_Icc {T ν B G : ℝ} (hT : 0 < T) (hν : 0 < ν)
    {u v : VelocityField} {p q : PressureField}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (heu : UniformFiniteEnergy (Icc (0 : ℝ) T) u)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖u (t,x)‖ ≤ B)
    (hG0 : 0 ≤ G) (hG : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖spatialDerivative u t x‖ ≤ G)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν u p t x = residual ν v q t x)
    (hzero : ∀ x, u (0,x) = v (0,x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t,x) = v (t,x) := by
  let a := (Real.sqrt ν)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hν)
  have haν : a ^ 2 * ν = 1 := by
    dsimp [a]
    rw [inv_pow, Real.sq_sqrt hν.le, inv_mul_cancel₀ hν.ne']
  have hBu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖viscosityVelocity a u (t,x)‖ ≤ a * B := by
    intro t ht x
    simpa only [viscosityVelocity, dilateField, mul_one, one_mul, sub_zero,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha] using
      mul_le_mul_of_nonneg_left (hB t ht (a⁻¹ • x)) ha.le
  have hGu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖spatialDerivative (viscosityVelocity a u) t x‖ ≤ G := by
    intro t ht x
    simpa only [viscosityVelocity, dilate_spatialDerivative, mul_inv_cancel₀ ha.ne',
      one_smul, one_mul, sub_zero] using hG t ht (a⁻¹ • x)
  have hNS' : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 (viscosityVelocity a u) (viscosityPressure a p) t x =
      navierStokesResidual 1 (viscosityVelocity a v) (viscosityPressure a q) t x := by
    intro t ht x
    change residual 1 _ _ _ _ = residual 1 _ _ _ _
    rw [← haν, viscosity_residual_general ha.ne', viscosity_residual_general ha.ne', hNS t ht]
  have hz : ∀ x, viscosityVelocity a u (0,x) = viscosityVelocity a v (0,x) := by
    intro x
    simp only [viscosityVelocity, dilateField, sub_zero, one_mul, hzero]
  have heq := BoundedReferenceUniqueness.classical_uniqueness_on_Icc hT
    (spatial_rescale_smooth a a hu) (spatial_rescale_smooth a a hv)
    (spatial_rescale_smooth a (a^2) hp) (spatial_rescale_smooth a (a^2) hq)
    (viscosity_uniform_energy ha heu) (mul_nonneg ha.le hB0) hBu hG0 hGu
    (viscosity_uniform_energy ha hev)
    (fun t ht x => by
      change spatialDivergence (viscosityVelocity a u) t x = 0
      rw [viscosity_divergence ha.ne', hdu t ht])
    (fun t ht x => by
      change spatialDivergence (viscosityVelocity a v) t x = 0
      rw [viscosity_divergence ha.ne', hdv t ht]) hNS' hz
  intro t ht x
  have he := heq t ht (a • x)
  have he' : a • u (t,x) = a • v (t,x) := by
    simpa only [viscosityVelocity, dilateField, one_mul, sub_zero,
      smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using he
  exact (smul_right_injective _ ha.ne') he'
end NSFormalization.Source.BoundedViscosityUniqueness
