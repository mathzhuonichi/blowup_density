import NSFormalization.Section4.R41.ClassFacts

noncomputable section

namespace NSFormalization.Section4.R41

open Set NavierStokes.ProblemStatement
open scoped ENNReal

private theorem rev234_memForceRapid_zero :
    MemForceRapid (0 : A02.SpaceTimeField) := by
  refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
  simp

private theorem rev234_compact_zero_difference :
    D01.MemForceCompact
      (fun z => (0 : A02.SpaceTimeField) z - (0 : A02.SpaceTimeField) z) := by
  have hz : D01.MemForceCompact (0 : A02.SpaceTimeField) := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
    simp [NavierStokesR3.ProblemStatement.positiveTimeDomain]
  have hfun :
      (fun z => (0 : A02.SpaceTimeField) z - (0 : A02.SpaceTimeField) z) =
        (0 : A02.SpaceTimeField) := by
    funext z
    simp
  rw [hfun]
  exact hz

-- G3's rapid and compact-difference hypotheses are jointly satisfiable.
example : MemForceRapid (0 : A02.SpaceTimeField) :=
  memForceRapid_of_compact_difference 0 0 rev234_memForceRapid_zero
    rev234_compact_zero_difference

example : D01.forceSobolevENorm 1 0 (0 : A02.SpaceTimeField) ≠ 1 := by
  rw [forceSobolevENorm_zero]
  norm_num

-- Substantive mutation: change G5's proved norm value from zero to one.
example : D01.forceSobolevENorm 1 0 (0 : A02.SpaceTimeField) = 1 := by
  exact forceSobolevENorm_zero_of_one_or_two 1 (Or.inl rfl) 0

end NSFormalization.Section4.R41
