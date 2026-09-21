import Bindings.CompletedDensity

noncomputable section

open Set
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings NSFormalization.Section4
open scoped ENNReal

/- A concrete admissible zero reference produces an actual positive scale whose
force has the asserted membership, exact lifespan, and full-horizon solution. -/
example :
    ∃ (P : PacketAPI 1) (A : InsertionFamilyAPI 1 P) (ε : ℝ),
      ε ∈ Ioc (0 : ℝ) A.ε₀ ∧
      MemForceR (A.force ε) ∧
      maximalLifespanR 1 0 (A.force ε) = ENNReal.ofReal 1 ∧
      ∃ U : ClassicalSolutionR 1 0 (A.force ε) 1,
        U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε := by
  obtain ⟨P, A, _ha, _hT, _hg, _hv, _hp, hfamily, _henergy, _hforce⟩ :=
    completedDensity.strongTrajectoryClosure
      0 A04.zero_mem_initialClassR
      1 (by norm_num) 1 (by norm_num)
      0 A04.memForceR_zero 1 (by norm_num)
      (maximalPartial_ofA02 (A04.zeroSol 1 (1 + 1) (by norm_num) (by norm_num)))
  refine ⟨P, A, A.ε₀, ⟨A.eps_pos, le_rfl⟩, ?_⟩
  exact hfamily A.ε₀ ⟨A.eps_pos, le_rfl⟩

