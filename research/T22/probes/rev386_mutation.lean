import NSFormalization.Section3.T22.WeightRatio

open NavierStokes.ProblemStatement (coordinateVector)
open NSFormalization.Section3.T22

/- REVIEW NEGATIVE PROBE (intentionally does not typecheck).

The main statement's constant base is changed from `2` to `1`.  At `s = 2`,
`xi = 2 e_0`, and `eta = e_0`, this mutation says `5 <= 4`.
-/
example :
    (1 + ‖(2 : Real) • coordinateVector 0‖ ^ 2) ^ ((2 : Real) / 2) ≤
      1 ^ (|(2 : Real)| / 2) *
        (1 + ‖coordinateVector 0‖ ^ 2) ^ ((2 : Real) / 2) *
        (1 + ‖(2 : Real) • coordinateVector 0 - coordinateVector 0‖ ^ 2) ^
          (|(2 : Real)| / 2) := by
  have hdiff :
      (2 : Real) • coordinateVector 0 - coordinateVector 0 = coordinateVector 0 := by
    module
  rw [hdiff]
  norm_num [coordinateVector, norm_smul]
