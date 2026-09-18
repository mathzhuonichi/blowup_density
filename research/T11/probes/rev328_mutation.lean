import NSFormalization.Section3.T11.ConvolutionBoundReal

open NSFormalization.Section3.T10 NSFormalization.Section3.T11
noncomputable section

local instance rev328MutationNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance rev328MutationNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/- Substantive negative mutation: flip the coefficient identity's sign. -/
example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real r hr A B).1 i k =
      -torusProjectedConvectionSymbolReal r A B i k := by
  exact torusConvolutionCLM_real_coeff r hr A B i k
