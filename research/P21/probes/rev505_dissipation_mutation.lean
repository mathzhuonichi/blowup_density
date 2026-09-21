import NSFormalization.Section3.T11.EnstrophyInequality

open NSFormalization.Section3.T11

-- The unmutated c = 1 conclusion follows with jointly satisfiable premises at
-- ν=1, C=U=G=F=N=P=Q=Y=0, L=Z=1, d=-2.
example : (-2 : ℝ) + 1 * 1 ≤
    ((2 * 0) ^ 4 / (1 / 2) ^ 3 + (1 + 1)) * (1 + 0) ^ 3 +
      (1 + 2 / 1) * 0 := by
  exact weighted_cubic_assemblyT (ν := 1) (C := 0) (U := 0) (G := 0)
    (L := 1) (F := 0) (N := 0) (P := 0) (Q := 0) (d := -2)
    (Y := 0) (Z := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- Reviewer mutation: strengthen the main scalar dissipation coefficient from
-- c = 1 to c = 5 without changing the data or premises.  The conclusion then
-- normalizes to the false statement 3 ≤ 2.
/-- error: unsolved goals
⊢ False -/
#guard_msgs (error) in
example : (-2 : ℝ) + 5 * 1 * 1 ≤
    ((2 * 0) ^ 4 / (1 / 2) ^ 3 + (1 + 1)) * (1 + 0) ^ 3 +
      (1 + 2 / 1) * 0 := by
  norm_num
