import Formal.PeriodicClayEnergy
import Formal.PeriodicClayQuantifiers

/-! Integrated final certificates. These prove a nonzero shear specialization of CMI B.
The universal datum quantifier in `ClayB` remains unproved. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace ClayNS

/-- Full global PDE certificate, nonzero datum, and actual uniform cell energy. -/
theorem certified_nonzero_periodic_NS (ν a : ℝ) (hν : 0 < ν) (ha : a ≠ 0) :
    AdmissiblePeriodicDatum (shearDatum a) ∧
    shearDatum a ≠ (fun _ _ => 0) ∧
    GlobalPeriodicSolution ν (shearDatum a) (shear ν a) (fun _ _ => 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun x : Point => kineticDensity (shear ν a t x)) unitCube ∧
      0 ≤ shearEnergy ν a t ∧ shearEnergy ν a t ≤ a ^ 2 := by
  exact ⟨shear_datum_admissible a, shear_datum_nonzero a ha,
    shear_global_periodic ν a, shear_finite_uniform_energy ν a hν.le⟩

/-- Quantifier-visible consequence: at least one nonzero admissible datum
has a global smooth periodic solution for each positive viscosity. -/
theorem clayB_has_nonzero_smooth_specialization :
    ∀ ν : ℝ, 0 < ν → ∃ u₀ : Point → Point, ∃ u : Velocity, ∃ p : Pressure,
      AdmissiblePeriodicDatum u₀ ∧ u₀ ≠ (fun _ _ => 0) ∧
      GlobalPeriodicSolution ν u₀ u p := by
  intro ν hν
  have h := certified_nonzero_periodic_NS ν 1 hν one_ne_zero
  exact ⟨shearDatum 1, shear ν 1, (fun _ _ => 0), h.1, h.2.1, h.2.2.1⟩

#print axioms certified_nonzero_periodic_NS
#print axioms clayB_has_nonzero_smooth_specialization

end ClayNS
