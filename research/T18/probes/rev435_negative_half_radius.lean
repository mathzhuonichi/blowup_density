import NSFormalization.Section3.T18.Support

open Set Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Section3.T18

/- Reviewer mutation: replacing the proved radius by half of it is a
substantive strengthening and must not follow from the canonical theorem. -/
example (data : InsertionData)
    (hsupp : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space ↦ velocity data ε (t, x) -
        data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀
            (ε * (diffSupportRadius data / 2))) := by
  intro ε hε t ht
  exact velocityDifference_support data hsupp ε hε t ht
