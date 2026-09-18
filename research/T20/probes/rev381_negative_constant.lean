import NSFormalization.Section3.T20.CriticalRegularity

open NSFormalization.Section3.T20

/- Deliberate substantive mutation of the main API statement: replace the
   paper's bootstrap denominator 4 by 5.  The original field cannot close this
   changed goal.  This file is expected to fail to elaborate. -/
example (A : CriticalRegularityTAPI) : A.c < 1 / (5 * A.C₀) := by
  exact A.c_lt_C₀
