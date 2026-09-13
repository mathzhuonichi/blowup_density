import Formal.PeriodicClayShear
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual finite and uniformly bounded kinetic energy in one spatial period.
The kinetic density omits the conventional factor 1/2; this changes no finiteness claim. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
open Set MeasureTheory

namespace ClayNS

/-- The closed unit fundamental cube; its boundary is Lebesgue-null. -/
def unitCube : Set Point := Icc (fun _ => 0) (fun _ => 1)

theorem unitCube_volume : volume unitCube = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

/-- Physical energy density integrated against 3D Lebesgue measure. -/
def shearEnergy (ν a t : ℝ) : ℝ :=
  ∫ x in unitCube, kineticDensity (shear ν a t x)

theorem shear_density_continuous (ν a t : ℝ) :
    Continuous (fun x : Point => kineticDensity (shear ν a t x)) := by
  have heq : (fun x : Point => kineticDensity (shear ν a t x)) =
      fun x => (ExplicitShear.profile ν a (2 * Real.pi) t (x 1)) ^ 2 := by
    funext x
    exact shear_kinetic_density ν a t x
  rw [heq]
  exact ((ExplicitShear.profile_contDiff ν a (2 * Real.pi)).continuous.comp
    (continuous_const.prodMk (continuous_apply 1))).pow 2

/-- This integrability proof prevents interpreting a divergent Bochner integral as zero. -/
theorem shear_density_integrable (ν a t : ℝ) :
    IntegrableOn (fun x : Point => kineticDensity (shear ν a t x)) unitCube := by
  exact (shear_density_continuous ν a t).integrableOn_Icc

theorem shear_energy_nonneg (ν a t : ℝ) : 0 ≤ shearEnergy ν a t := by
  apply integral_nonneg
  intro x
  change 0 ≤ kineticDensity (shear ν a t x)
  rw [shear_kinetic_density]
  exact sq_nonneg _

theorem shear_energy_le (ν a t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    shearEnergy ν a t ≤ a ^ 2 := by
  have hnorm : ‖∫ x in unitCube, kineticDensity (shear ν a t x)‖ ≤
      a ^ 2 * volume.real unitCube := by
    apply norm_setIntegral_le_of_norm_le_const
    · rw [unitCube_volume]
      exact ENNReal.one_lt_top
    · intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact shear_uniform_energy_density ν a t x hν ht
      · rw [shear_kinetic_density]
        exact sq_nonneg _
  have hvol : volume.real unitCube = 1 := by
    simp [Measure.real, unitCube_volume]
  rw [hvol, mul_one] at hnorm
  exact (le_abs_self _).trans hnorm

theorem shear_finite_uniform_energy (ν a : ℝ) (hν : 0 ≤ ν) :
    ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun x : Point => kineticDensity (shear ν a t x)) unitCube ∧
      0 ≤ shearEnergy ν a t ∧ shearEnergy ν a t ≤ a ^ 2 := by
  intro t ht
  exact ⟨shear_density_integrable ν a t, shear_energy_nonneg ν a t,
    shear_energy_le ν a t hν ht⟩

#print axioms shear_finite_uniform_energy
end ClayNS
