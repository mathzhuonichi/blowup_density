import NSFormalization.Section4.A01.HorizonUniform
import NSFormalization.Section4.A04.ZeroSolution
import Contracts.V1.Data

open NSFormalization.Section4
open NSFormalization.Section4.A01
open Set EulerCylinderSobolevSpace EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ENNReal

#print axioms HorizonLowerBoundH1
#print axioms HorizonLowerBoundH7L1
#print axioms picard_ballBound_mono
#print axioms picard_ballLipschitz_mono
#print axioms picard_budget_mono
#print axioms exists_uniform_H7_coefficient_horizon
#print axioms exists_uniform_H7_sup_force_horizon
#print axioms uniform_H7_zero

-- Definitional conformance with the contract vocabulary, without importing a
-- contract into the production module or asserting the obligation.
example (horizon : ℝ → BlowupDensity.Contracts.V1.Data.SpatialField → BlowupDensity.Contracts.V1.Data.SpaceTimeField → ℝ) :
    HorizonLowerBoundH1 horizon =
      (∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : BlowupDensity.Contracts.V1.Data.SpatialField) (f : BlowupDensity.Contracts.V1.Data.SpaceTimeField),
            a ∈ BlowupDensity.Contracts.V1.Data.initialClassR → BlowupDensity.Contracts.V1.Data.MemForceR f →
              BlowupDensity.Contracts.V1.Data.sobolevENorm 1 a ≤ K →
              BlowupDensity.Contracts.V1.Data.forceSobolevENormL1 1 f ≤ K → δ ≤ horizon ν a f) := rfl

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Invoke the proved uniform result, with the actual nonlinear coefficient
-- bundle; this does not assume a lifespan inequality for a chosen horizon.
example : ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
    ∃ u : C(Icc (0 : ℝ) δ, SobolevSpace 1 7),
      ‖u‖ ≤ 1 ∧ u ⟨0, le_rfl, hδ.le⟩ = 0 ∧
        ∀ t, u t = quadraticDuhamel 1 1 (by norm_num) hδ.le hδ1
          (coefficients 1 (le_refl 6) (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)))
          0 u t := uniform_H7_zero (by norm_num)

example : (0 : A02.SpatialField) ∈ A02.initialClassR := A04.zero_mem_initialClassR
example : D01.MemForceR (0 : A02.SpaceTimeField) := A04.memForceR_zero
