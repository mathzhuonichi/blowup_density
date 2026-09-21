import NSFormalization.Source.Insertion
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Parabolic scaling of the actual Navier--Stokes differential operators

The parameter k is the inverse spatial length. Velocity scales by k, pressure
by k^2, force by k^3, and time by k^2. The viscosity is unchanged. All maps
below act on the source library's Euclidean spacetime fields.
-/

noncomputable section

namespace NSFormalization.Source

open NavierStokes.ProblemStatement MeasureTheory
open scoped ContDiff

def dilateField {V : Type*} [SMul ℝ V] (a c d t₀ : ℝ) (x₀ : Space)
    (f : SpaceTime → V) : SpaceTime → V :=
  fun z => a • f (c * (z.1 - t₀), d • (z.2 - x₀))

theorem fderiv_dilate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Space → V) (a d : ℝ) (x₀ x : Space) :
    fderiv ℝ (fun y => a • f (d • (y - x₀))) x =
      (a * d) • fderiv ℝ f (d • (x - x₀)) := by
  rw [show (fun y => a • f (d • (y - x₀))) =
    a • (fun y => f (d • (y - x₀))) from rfl,
    fderiv_const_smul_field]
  simp only [Pi.smul_apply]
  rw [fderiv_comp_sub (f := fun y => f (d • y)) x₀, fderiv_comp_smul d, smul_smul]

theorem dilate_spatialDerivative (a c d t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDerivative (dilateField a c d t₀ x₀ u) t x =
      (a * d) • spatialDerivative u (c * (t - t₀)) (d • (x - x₀)) := by
  exact fderiv_dilate (fun y => u (c * (t - t₀), y)) a d x₀ x

theorem dilate_divergence (a c d t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (t : ℝ) (x : Space) :
    spatialDivergence (dilateField a c d t₀ x₀ u) t x =
      (a * d) * spatialDivergence u (c * (t - t₀)) (d • (x - x₀)) := by
  simp [spatialDivergence, dilate_spatialDerivative, Finset.mul_sum]

theorem dilate_advection (a c d t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (t : ℝ) (x : Space) :
    advection (dilateField a c d t₀ x₀ u) t x =
      (a ^ 2 * d) • advection u (c * (t - t₀)) (d • (x - x₀)) := by
  simp only [advection, dilate_spatialDerivative, dilateField,
    smul_apply, map_smul, smul_smul]
  congr 1
  ring

theorem dilate_gradient (a c d t₀ : ℝ) (x₀ : Space)
    (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (dilateField a c d t₀ x₀ p) t x =
      (a * d) • pressureGradient p (c * (t - t₀)) (d • (x - x₀)) := by
  unfold pressureGradient dilateField
  dsimp only
  rw [fderiv_dilate (fun y => p (c * (t - t₀), y)) a d x₀ x]
  simp only [smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem dilate_laplacian (a c d t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (t : ℝ) (x : Space) :
    spatialLaplacian (dilateField a c d t₀ x₀ u) t x =
      (a * d ^ 2) • spatialLaplacian u (c * (t - t₀)) (d • (x - x₀)) := by
  simp only [spatialLaplacian, dilate_spatialDerivative, smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_dilate
    (fun y => spatialDerivative u (c * (t - t₀)) y (coordinateVector i))
    (a * d) d x₀ x]
  simp only [smul_apply]
  congr 1
  ring

theorem dilate_temporalDerivative (a c d t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (t : ℝ) (x : Space) :
    temporalDerivative (dilateField a c d t₀ x₀ u) t x =
      (a * c) • temporalDerivative u (c * (t - t₀)) (d • (x - x₀)) := by
  unfold temporalDerivative dilateField
  have he : (fun s : ℝ => a • u (c * (s - t₀), d • (x - x₀))) =
      a • (fun s : ℝ => u (c • (s - t₀), d • (x - x₀))) := rfl
  rw [he, fderiv_const_smul_field]
  simp only [Pi.smul_apply]
  rw [fderiv_comp_sub (f := fun s => u (c • s, d • (x - x₀))) t₀,
    fderiv_comp_smul (f := fun s => u (s, d • (x - x₀))) c]
  simp only [smul_smul, smul_apply, smul_eq_mul]

def parabolicVelocity (k t₀ : ℝ) (x₀ : Space) (u : VelocityField) : VelocityField :=
  dilateField k (k ^ 2) k t₀ x₀ u

def parabolicPressure (k t₀ : ℝ) (x₀ : Space) (p : PressureField) : PressureField :=
  dilateField (k ^ 2) (k ^ 2) k t₀ x₀ p

def parabolicForce (k t₀ : ℝ) (x₀ : Space) (f : VelocityField) : VelocityField :=
  dilateField (k ^ 3) (k ^ 2) k t₀ x₀ f

/-- Every term acquires the same cubic factor. No viscosity conversion is
needed for spatial parabolic concentration. -/
theorem parabolic_residual (ν k t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (p : PressureField) (t : ℝ) (x : Space) :
    residual ν (parabolicVelocity k t₀ x₀ u) (parabolicPressure k t₀ x₀ p) t x =
      k ^ 3 • residual ν u p (k ^ 2 * (t - t₀)) (k • (x - x₀)) := by
  simp only [residual, parabolicVelocity, parabolicPressure,
    dilate_temporalDerivative, dilate_advection, dilate_laplacian, dilate_gradient]
  rw [show k * k ^ 2 = k ^ 3 by ring, show k ^ 2 * k = k ^ 3 by ring]
  simp only [smul_add, smul_sub, smul_smul, mul_comm ν (k ^ 3)]

theorem parabolic_equation (ν k t₀ : ℝ) (x₀ : Space)
    (u : VelocityField) (p : PressureField) (f : VelocityField) (t : ℝ) (x : Space)
    (h : residual ν u p (k ^ 2 * (t - t₀)) (k • (x - x₀)) =
      f (k ^ 2 * (t - t₀), k • (x - x₀))) :
    residual ν (parabolicVelocity k t₀ x₀ u) (parabolicPressure k t₀ x₀ p) t x =
      parabolicForce k t₀ x₀ f (t, x) := by
  rw [parabolic_residual, h]
  rfl

/-- The actual spatial L2 energy of a dilated field. -/
theorem spatial_energy_dilate (u : Space → Space) (a k : ℝ) (hk : 0 < k) :
    (∫ x : Space, ‖a • u (k • x)‖ ^ 2) =
      a ^ 2 * (k ^ 3)⁻¹ * (∫ x : Space, ‖u x‖ ^ 2) := by
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun x : Space => ‖u x‖ ^ 2)
      k (hR := hk.le)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  ring

theorem spatial_energy_parabolic (u : Space → Space) (k : ℝ) (hk : 0 < k) :
    (∫ x : Space, ‖k • u (k • x)‖ ^ 2) =
      k⁻¹ * (∫ x : Space, ‖u x‖ ^ 2) := by
  rw [spatial_energy_dilate u k k hk]
  field_simp

end NSFormalization.Source
