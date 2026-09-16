import Bindings.CompletedClosure

noncomputable section
open Set Filter MeasureTheory
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings NSFormalization.Section4
open scoped ENNReal Topology

-- Concrete zero reference, viscosity and singular time both one.
example (hreal : I03.CompactHomogeneousRealization) :
    ∃ (P : PacketAPI 1) (A : InsertionFamilyAPI 1 P),
      A.a = 0 ∧ A.scaling.correction.T = 1 ∧
      A.scaling.correction.g = 0 ∧
      A.scaling.correction.v = 0 ∧ A.scaling.correction.π = 0 ∧
      (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
        MemForceR (A.force ε) ∧ maximalLifespanR 1 0 (A.force ε) = ENNReal.ofReal 2 ∧
        ∃ U : ClassicalSolutionR 1 0 (A.force ε) 1,
          U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
      Tendsto (fun ε : ℝ => energyENorm 1 (fun z => A.velocity ε z - 0))
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ =>
        forceSobolevENorm 1 0 (fun z => A.force ε z - 0) +
        forceSobolevENorm 2 (-1) (fun z => A.force ε z - 0) +
        forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - 0))
        (𝓝[>] 0) (𝓝 0) := by
  exact strongTrajectoryClosure_of_realization hreal 0 A04.zero_mem_initialClassR
    1 (by norm_num) 1 (by norm_num) 0 A04.memForceR_zero 1 (by norm_num)
    (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
