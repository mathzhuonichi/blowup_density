import NSFormalization.Section3.T11.DuhamelHalfStep

/- Reviewer negative check: the target's half-step constant is load-bearing.
   This deliberately asks for order `r + 1` and tries to reuse the theorem.
   It must fail with a type mismatch, not merely because an argument was dropped. -/
noncomputable section
namespace Rev330Negative

open Set
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NavierStokes.ProblemStatement
open scoped ContDiff

example {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g)
    (hp : IsPeriodicOn Set.univ g) (hT : 0 < T)
    (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A)
    (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u)
    (r : ℝ) (hr : 3 ≤ r) (v : ℝ → PeriodicSobolev r)
    (hv : ContinuousOn v (Ico 0 T))
    (hvu : ∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) :
    ∃ w : ℝ → PeriodicSobolev (r + 1),
      ContinuousOn w (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1) (v t) (w t) := by
  exact torusHalfStepInput ν hν C a g T ha hg hp hT A F P u hA hF hP hu r hr v hv hvu

end Rev330Negative
