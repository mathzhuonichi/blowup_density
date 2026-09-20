import NSFormalization.Section4.A01.MildUniqueness

noncomputable section
namespace NSFormalization.Section4.A01
open Set EulerCylinderSobolevSpace EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms volterra_window_bound
#print axioms volterra_eq_zero
#print axioms quadratic_mild_unique
#print axioms mildUniqueness
#print axioms compatible_carriers_of_boundsInv'
#print axioms compatible_carriers_of_bounds'
#print axioms compatible_carriers_hall'

-- Positive horizon, genuine zero datum and zero force; existence AND uniqueness.
example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ∃! u : C(Icc (0 : ℝ) S, SobolevSpace 1 7),
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 (q := 6) le_rfl 0) 0 u t := by
  have hz : ∀ t, (0 : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) t =
      quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 (q := 6) le_rfl 0) 0 0 t := by
    intro t
    simp [quadraticDuhamel, source_eq]
  exact ⟨0, hz, fun u hu => mildUniqueness ν S hν hS 0 0 u 0 hu hz⟩

end NSFormalization.Section4.A01
