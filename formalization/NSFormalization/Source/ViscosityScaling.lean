import NSFormalization.Source.ParabolicScaling
import NavierStokes.R3CompactCandidate

/-!
# Converting the unit-viscosity source without moving its blowup time

For positive `a`, velocity and force have amplitude `a`, pressure amplitude
`a^2`, and space is evaluated at `x/a`. The new viscosity is `a^2`; time is
unchanged. This conversion is separate from parabolic concentration, which
preserves the viscosity.
-/

noncomputable section
namespace NSFormalization.Source
open NavierStokes NavierStokes.ProblemStatement Set
open scoped ContDiff

def viscosityVelocity (a : ℝ) (u : VelocityField) : VelocityField :=
  dilateField a 1 a⁻¹ 0 0 u

def viscosityPressure (a : ℝ) (p : PressureField) : PressureField :=
  dilateField (a ^ 2) 1 a⁻¹ 0 0 p

theorem viscosity_residual {a : ℝ} (ha : a ≠ 0)
    (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    residual (a ^ 2) (viscosityVelocity a u) (viscosityPressure a p) t x =
      a • residual 1 u p t (a⁻¹ • x) := by
  simp only [residual, viscosityVelocity, viscosityPressure,
    dilate_temporalDerivative, dilate_advection, dilate_laplacian, dilate_gradient,
    mul_one, sub_zero, one_mul]
  have h₁ : a ^ 2 * a⁻¹ = a := by field_simp
  have h₂ : a ^ 2 * (a * (a⁻¹) ^ 2) = a := by field_simp
  rw [h₁]
  simp only [smul_smul, h₂, one_smul, smul_add, smul_sub]

theorem viscosity_equation {a : ℝ} (ha : a ≠ 0)
    (u : VelocityField) (p : PressureField) (f : VelocityField) (t : ℝ) (x : Space)
    (h : navierStokesResidual u p t (a⁻¹ • x) = f (t, a⁻¹ • x)) :
    residual (a ^ 2) (viscosityVelocity a u) (viscosityPressure a p) t x =
      viscosityVelocity a f (t, x) := by
  rw [viscosity_residual ha, residual_one, h]
  simp [viscosityVelocity, dilateField]

theorem viscosity_divergence {a : ℝ} (ha : a ≠ 0)
    (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (viscosityVelocity a u) t x =
      spatialDivergence u t (a⁻¹ • x) := by
  simp [viscosityVelocity, dilate_divergence, ha]

theorem viscosity_speed_unbounded {a : ℝ} (ha : 0 < a)
    {u : VelocityField} (hu : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (viscosityVelocity a u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hu (M / a) (div_pos hM ha) δ hδ
  refine ⟨t, a • x, ht, hnear, ?_⟩
  simpa [viscosityVelocity, dilateField, smul_smul, ha.ne', norm_smul,
    Real.norm_eq_abs, abs_of_pos ha, mul_comm] using (div_lt_iff₀ ha).mp hlarge

theorem spatial_rescale_support {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    (b : ℝ) {a : ℝ} (ha : a ≠ 0) (f : SpaceTime → V) {K : Set Space}
    (hK : IsCompact K) {I : Set ℝ}
    (hf : ∀ t ∈ I, ∀ x, x ∉ K → f (t, x) = 0) :
    ∃ K' : Set Space, IsCompact K' ∧ ∀ t ∈ I, ∀ x, x ∉ K' →
      dilateField b 1 a⁻¹ 0 0 f (t, x) = 0 := by
  refine ⟨(fun x : Space => a • x) '' K, hK.image (by fun_prop), ?_⟩
  intro t ht x hx
  have hy : a⁻¹ • x ∉ K := by
    intro hy
    exact hx ⟨a⁻¹ • x, hy, by simp [smul_smul, ha]⟩
  simp [dilateField, hf t ht _ hy]

theorem spatial_rescale_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : ℝ) {f : SpaceTime → V} {I : Set ℝ}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (dilateField b 1 a⁻¹ 0 0 f) (I ×ˢ (univ : Set Space)) := by
  have hc : ContDiff ℝ ∞ (fun z : SpaceTime => (z.1, a⁻¹ • z.2)) := by fun_prop
  have hm : MapsTo (fun z : SpaceTime => (z.1, a⁻¹ • z.2))
      (I ×ˢ (univ : Set Space)) (I ×ˢ (univ : Set Space)) :=
    fun z hz => ⟨hz.1, mem_univ _⟩
  have hd := hf.comp hc.contDiffOn hm
  convert (contDiffOn_const (c := b)).smul hd using 1
  funext z
  simp [dilateField]

/-- The source equation is available at every prescribed positive viscosity,
with exactly the same terminal time and genuine speed blowup. -/
theorem compact_candidate_at_viscosity {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : R3CompactCandidate.Properties u p f)
    {ν : ℝ} (hν : 0 < ν) :
    let a := Real.sqrt ν
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      residual ν (viscosityVelocity a u) (viscosityPressure a p) t x =
        viscosityVelocity a f (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ x,
      spatialDivergence (viscosityVelocity a u) t x = 0) ∧
    (∀ x, viscosityVelocity a u (0, x) = 0) ∧
    SpeedUnboundedAtOne (viscosityVelocity a u) := by
  dsimp only
  have ha : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  refine ⟨?_, ?_, ?_, viscosity_speed_unbounded ha h.speed_unbounded⟩
  · intro t ht x
    have he := viscosity_equation ha.ne' u p f t x (h.navier_stokes t ht _)
    simpa only [Real.sq_sqrt hν.le] using he
  · intro t ht x
    rw [viscosity_divergence ha.ne', h.divergence_free t ht]
  · intro x
    simp [viscosityVelocity, dilateField, h.zero_initial_velocity]

end NSFormalization.Source
