import NSFormalization.Section3.T18.Lifespan

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open scoped ContDiff

namespace NSFormalization.Section3.T18.Rev436Nonvacuity

-- For every threaded insertion bundle, the scale guard has a concrete member.
example (data : InsertionData) : ε₀ data / 2 ∈ Ioc (0 : ℝ) (ε₀ data) := by
  have hε := eps_pos data
  constructor <;> linarith

-- The compact-periodic boundedness lemma itself has concrete, nonempty data.
example : ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Space,
    ‖(fun _ : SpaceTime => (0 : Space)) (t, x)‖ ≤ C := by
  let u : NSFormalization.Section4.A02.SpaceTimeField := fun _ ↦ 0
  have hsmooth : ContDiffOn ℝ ∞ u
      (Ico (0 : ℝ) 2 ×ˢ (Set.univ : Set Space)) := by
    simpa only [u] using
      (contDiff_const.contDiffOn : ContDiffOn ℝ ∞ (fun _ : SpaceTime ↦ (0 : Space)) _)
  have hperiodic : IsPeriodicOn (Ico (0 : ℝ) 2) u := by
    intro t ht x i
    rfl
  simpa only [u] using exists_speed_bound hsmooth hperiodic (by norm_num)

end NSFormalization.Section3.T18.Rev436Nonvacuity
