import Contracts.V1.Data
import NSFormalization.Section4.C01.ForceSlices

/-!
Conformance check for C01 unit U2.

The `example` below has, token for token, the type of the spec field
`BlowupDensity.C01.Draft.EnergyAbsorptionAPI.forceTimeRegularity`
(`research/C01/Spec.lean:326-329`), stated in the spec's own vocabulary
(`Contracts.V1.Data.SpaceTimeField`, `Contracts.V1.Data.MemForceR`, and the
`slice` / `l2Sq` / `l2Norm` restated verbatim from `Spec.lean:167,172,177`).
It is discharged by the proved theorem
`NSFormalization.Section4.C01.forceTimeRegularity`, whose statement is therefore
definitionally the spec field.  `#print axioms` must show only the three
standard logical axioms.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

namespace BlowupDensity.C01.ConformanceU2

/-- `research/C01/Spec.lean:167`. -/
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)

/-- `research/C01/Spec.lean:172`. -/
def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2

/-- `research/C01/Spec.lean:177`. -/
def l2Norm (z : SpatialField) : ℝ := Real.sqrt (l2Sq z)

/-- The type of `EnergyAbsorptionAPI.forceTimeRegularity`, discharged. -/
example :
    ∀ f : SpaceTimeField, MemForceR f →
      (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
        ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ)) :=
  NSFormalization.Section4.C01.forceTimeRegularity

end BlowupDensity.C01.ConformanceU2

#print axioms NSFormalization.Section4.C01.forceTimeRegularity
