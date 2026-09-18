import NSFormalization.Section3.T11.ConvolutionBoundReal

open NSFormalization.Section3.T10 NSFormalization.Section3.T11
noncomputable section

local instance rev328NormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance rev328NormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

#check torusConvolutionCLM_real
#check torusConvolutionCLM_real_coeff
#check torusConvolutionCLM_real_norm_le
#check torusConvolutionCLM_real_coeff_transport
#check torusConvolutionCLM_real_reweight
#print NSFormalization.Section3.T11.torusConvolutionCLM_real

example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    PeriodicSobolev (r - 1) :=
  torusConvolutionCLM_real r hr A B
