import NSFormalization.Section3.T18.Lifespan

open Set
open NSFormalization.Section3.T10
open scoped ENNReal

namespace NSFormalization.Section3.T18.Rev436Negative

-- Deliberate substantive mutation: claim lifespan `T + 1` instead of `T`.
example (data : InsertionData) (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    maximalLifespanT data.ν data.a (force data ε) =
      ENNReal.ofReal (data.place.T + 1) := by
  exact lifespan data ε hε

end NSFormalization.Section3.T18.Rev436Negative
