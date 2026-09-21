import NSFormalization.Section3.T11.PhysicalRecovery

noncomputable section
namespace NSFormalization.Section3.T11.Rev318NegativeSign

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10

-- Substantive mutation: flip the affine trajectory from (1+t)c to (1-t)c
-- while retaining the positive constant force. The proved theorem must not fit.
example {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (c : Space) (hT : 0 ≤ T) :
    TorusForcedMildOn C (torusConstantDatum 3 c)
      (fun _ ↦ torusConstantDatum 3 c) T
      (fun t ↦ (1-t) • torusConstantDatum 3 c) :=
  torusForcedMildOn_affine_constant C c hT

end NSFormalization.Section3.T11.Rev318NegativeSign
