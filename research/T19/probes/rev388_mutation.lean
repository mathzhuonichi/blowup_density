import NSFormalization.Section3.T19.Bookkeeping
noncomputable section
open NSFormalization.Section3.T19
-- Mutate the proved threshold from 1/2 to 1/3; preserve the proof tactic.
example : criticalOrder 1 = (1 : ℝ) / 3 := by
  norm_num [criticalOrder]
