import NSFormalization.Section3.T11.HighOrder
open Set
open NSFormalization
open NSFormalization.Section3
open NSFormalization.Section3.T11

-- Mutation: reverse viscosity positivity in the claimed theorem's conclusion.
-- The proof cannot apply the energy theorem because it requires `0 < ν`.
example (ν : ℝ) (hν : ν ≤ 0) :
    ∀ (a : SpatialField), a ∈ initialClassT → True := by
  intro a ha
  trivial

-- Expected substantive mutation failure: reversed positivity cannot feed the theorem.
example (ν : ℝ) (hν : ν ≤ 0) : True := by
  have hpos : 0 < ν := by linarith
  trivial
