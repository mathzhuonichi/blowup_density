import NSFormalization.Section3.T10.DatumBasics
import Contracts.V1.Data

noncomputable section

namespace NSFormalization.Section3.T10

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

example :
    ∀ (s : ℝ) (z : SpatialField) (A B : PeriodicSobolev s),
      IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B :=
  datum_unique

example :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i (-k) = star (A.1 i k) :=
  datum_real

example :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s :=
  meanZero_datum

end NSFormalization.Section3.T10
