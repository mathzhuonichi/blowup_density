import NSFormalization.Section4.R44.JWeight

open NavierStokes.ProblemStatement
open NSFormalization.Section4.R44

/- Substantive negative mutation: add 1 to the exact Bessel-weight identity. -/
example {u f : Space → Space} (h : JWeightDatum u f) :
    (NSFormalization.Section4.D01.sobolevENorm (3 / 2) u).toReal ^ 2 =
      Y u ^ 2 + Z u ^ 2 + 1 := by
  exact weight_identity h
