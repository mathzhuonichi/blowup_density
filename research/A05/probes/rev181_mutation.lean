import Tests.GradientL6V2

noncomputable section

open MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm (dotHomogeneousENorm)
open scoped ENNReal

/- Substantive mutation: replace the critical `L³` target by `L⁴`.
The registered proof must not inhabit this changed statement. -/
example :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 4 volume ≤
        ENNReal.ofReal
            (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) *
          dotHomogeneousENorm (1 / 2) v :=
  BlowupDensity.Tests.checkedGradientL6V2.velocityCriticalL3
