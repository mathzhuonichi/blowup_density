import NSFormalization.Section3.T21.CriticalBridge
import NSFormalization.Section3.T21.ForceMonotonicity

/-!
# T21 N8--N9: exclusion of breakdown forces from critical balls
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

/-- N8: the critical-order small-data ball is disjoint from every finite-time
zero-datum breakdown set. -/
theorem criticalBallDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Disjoint (criticalBallT K.c ν (1 / 2)) (breakdownSetTZero ν T) := by
  intro ν hν T _hT
  rw [Set.disjoint_left]
  intro g hball hbreak
  have htop : maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
    criticalGlobalRegularity K ν hν g hball.1 hball.2
  have hle : maximalLifespanT ν (fun _ : Space ↦ 0) g ≤
      ENNReal.ofReal T := hbreak.2
  rw [htop] at hle
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hle)

/-- N9: every higher-order ball with the same radius is also disjoint from
the breakdown set. -/
theorem ballDisjoint
    (K : NSFormalization.Section3.T20.CriticalRegularityTAPI) :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
      Disjoint (criticalBallT K.c ν s) (breakdownSetTZero ν T) := by
  intro ν hν T hT s hs
  rw [Set.disjoint_left]
  intro g hball hbreak
  have hcritical : g ∈ criticalBallT K.c ν (1 / 2) :=
    ⟨hball.1, lt_of_le_of_lt (forceSobolevMonotone s hs g) hball.2⟩
  exact Set.disjoint_left.mp (criticalBallDisjoint K ν hν T hT)
    hcritical hbreak

end NSFormalization.Section3.T21
