import NSFormalization.Section4.A01.MildEnergyEnvelope
open NSFormalization.Section4.A01
-- Substantive mutation: ODE coefficient denominator 4ν becomes 2ν.
example {ν : ℝ} (hν : 0 < ν) (k b y : ℝ) :
    (1/2 : ℝ) * (2*y*(k^2/(2*ν)*y+b)) + ν*(k*y/(2*ν))^2 =
      k*y*(k*y/(2*ν)) + b*y := by
  field_simp
  ring
