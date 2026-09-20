import NSFormalization.Section3.T10.DatumBasics

noncomputable section

namespace NSFormalization.Section3.T10

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)

/- Reviewer negative probe: the requested mean subtraction is substantively
mutated to addition.  The implementation theorem must not inhabit this type. -/
example :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (fun x ↦ z x + meanT z) B ∧
            B ∈ meanZeroPeriodicSobolev s :=
  meanZero_datum

end NSFormalization.Section3.T10
