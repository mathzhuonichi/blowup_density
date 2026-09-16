import NSFormalization.Section4.A01.MildEnergyEnvelope
open NSFormalization.Section4.A01
example {ν : ℝ} (hν : 0 < ν) (A low b y : ℝ) :
    (1/2 : ℝ) * (2*y*((A^2/(4*ν))*(256*low^2)*y+b)) +
      ν*(A*(16*low)*y/(2*ν))^2 =
      A*(16*low)*y*(A*(16*low)*y/(2*ν)) + b*y := by
  convert energyComparison_balance hν (A*(16*low)) b y using 1 <;> first | rfl | ring
example : ¬ ((1/2 : ℝ)*(2*1*(1^2/(2*1)*1+0)) + 1*(1*1/(2*1))^2 =
    1*1*(1*1/(2*1)) + 0*1) := by norm_num
