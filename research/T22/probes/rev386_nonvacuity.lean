import NSFormalization.Section3.T22.WeightRatio

open NavierStokes.ProblemStatement (Space coordinateVector)
open NSFormalization.Section3.T22

/-- A concrete, nonzero instance of the delivered inequality: `s = 2`,
`xi = 2 e_0`, and `eta = e_0`. -/
example :
    (1 + ‖(2 : Real) • coordinateVector 0‖ ^ 2) ^ ((2 : Real) / 2) ≤
      2 ^ (|(2 : Real)| / 2) *
        (1 + ‖coordinateVector 0‖ ^ 2) ^ ((2 : Real) / 2) *
        (1 + ‖(2 : Real) • coordinateVector 0 - coordinateVector 0‖ ^ 2) ^
          (|(2 : Real)| / 2) :=
  weight_ratio_le 2 ((2 : Real) • coordinateVector 0) (coordinateVector 0)

example : (2 : Real) • coordinateVector 0 ≠ 0 := by
  simp [coordinateVector]

