import NSFormalization.Section3.T21.Disjointness
import NSFormalization.Section3.T21.Zero

/-!
# T21 N10: failure of relative density
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- N10: at and above order `1 / 2`, finite-time breakdown forces from rest
are not relatively dense in the periodic force class. -/
theorem nonDensity
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ s : ℝ, 1 / 2 ≤ s → ∀ T : ℝ, 0 < T →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) := by
  intro ν hν s hs T hT hdense
  have hradius : 0 < ENNReal.ofReal (K.c * ν) :=
    ENNReal.ofReal_pos.mpr (mul_pos K.hc hν)
  obtain ⟨f, hbreak, hdist⟩ := hdense (0 : SpaceTimeField)
    zero_mem_forceClassT (ENNReal.ofReal (K.c * ν)) hradius
  have hball : f ∈ criticalBallT K.c ν s := by
    refine ⟨hbreak.1, ?_⟩
    simpa only [sub_zero] using hdist
  exact Set.disjoint_left.mp (ballDisjoint K ν hν T hT s hs) hball hbreak

end NSFormalization.Section3.T21
