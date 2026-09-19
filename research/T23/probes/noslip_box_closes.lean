import NSFormalization.Section3.T23.NoSlipUniqueness
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
-- Box IBP is closed. This probe will be extended to uniqueness when proved.
example {Ω : Set Space} (hΩ : IsBoxDomain Ω) : IBP Ω := ibp_box hΩ
