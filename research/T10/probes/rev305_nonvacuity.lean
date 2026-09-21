import NSFormalization.Section3.T10.FourierCalculus

open NSFormalization.Section3.T10 NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open scoped ContDiff

private def reviewerMode : PeriodicFrequency := fun _ => 1

example : reviewerMode 0 = 1 := rfl

example :
    periodicFourierCoeff
        (fun x => fderiv ℝ (NSFormalization.Paper1.periodicCharacter reviewerMode) x
          (coordinateVector 0)) reviewerMode =
      periodicDerivativeSymbol 0 reviewerMode *
        periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter reviewerMode) reviewerMode :=
  periodicFourierCoeff_fderiv
    (NSFormalization.Paper1.periodicCharacter_periodic reviewerMode)
    ((NSFormalization.Paper1.periodicCharacter_smooth reviewerMode).of_le (by norm_num))
    0 reviewerMode

