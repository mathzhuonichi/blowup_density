import NSFormalization.Section3.T20.BIntegral
import NSFormalization.Section3.T20.ConstantTransport

/-!
# T20 U3/U4 probe: the canonical fields are closed by the proved theorems

Each `example` below is the exact `CriticalRegularityTAPI` field type
(`Section3/T20/CriticalRegularity.lean`), closed by `exact` with the proved
theorem — a statement-fidelity check against the canonical structure.  The
final block records non-vacuity: the smooth-periodic input class of the skew
identity contains a nonzero mode, so the universally quantified hypotheses of
`constantTransportSkew` are satisfiable, and `forceClassT` is inhabited for
`bIntegral`.
-/

noncomputable section
namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators InnerProductSpace

/-- `bIntegral` field type (verbatim), closed by the proved theorem. -/
example :
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalBIntegral (meanFreeForce g) ≤ criticalRho g :=
  bIntegral

/-- `constantTransportSkew` field type (verbatim), closed by the proved theorem. -/
example :
    ∀ (m : Space) (v w : SpatialField),
      SmoothPeriodicT v → SmoothPeriodicT w →
        Integrable
          (fun y : PeriodicTorus ↦
            (inner ℝ (torusLift (constantTransportSpatialT m v) y)
              (torusLift w y) : ℝ)) periodicTorusMeasure →
        Integrable
          (fun y : PeriodicTorus ↦
            (inner ℝ (torusLift v y)
              (torusLift (constantTransportSpatialT m w) y) : ℝ))
          periodicTorusMeasure →
          periodicPairing (constantTransportSpatialT m v) w =
            -periodicPairing v (constantTransportSpatialT m w) :=
  constantTransportSkew

/-- A nonzero smooth periodic mode: the skew hypotheses are non-vacuous. -/
example : ∃ v : SpatialField, SmoothPeriodicT v ∧ v ≠ 0 := by
  refine ⟨fun _ => coordinateVector 0, ⟨contDiff_const, fun _ _ => rfl⟩, ?_⟩
  intro h
  have hx : (coordinateVector 0 : Space) = (0 : Space) := congrFun h 0
  have h1 : (coordinateVector (0 : Fin 3) : Space) 0 = (1 : ℝ) := by
    simp [coordinateVector]
  rw [hx] at h1
  simp at h1

/-- The skew identity instantiated at the nonzero constant mode is a genuine
`CriticalRegularityTAPI`-shaped equation, not vacuously quantified. -/
example (m : Space)
    (h1 : Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m (fun _ => coordinateVector 0)) y)
            (torusLift (fun _ => coordinateVector 0) y) : ℝ)) periodicTorusMeasure)
    (h2 : Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (fun _ => coordinateVector 0) y)
            (torusLift (constantTransportSpatialT m (fun _ => coordinateVector 0)) y) : ℝ))
        periodicTorusMeasure) :
    periodicPairing (constantTransportSpatialT m (fun _ => coordinateVector 0))
        (fun _ => coordinateVector 0) =
      -periodicPairing (fun _ => coordinateVector 0)
        (constantTransportSpatialT m (fun _ => coordinateVector 0)) :=
  constantTransportSkew m (fun _ => coordinateVector 0) (fun _ => coordinateVector 0)
    ⟨contDiff_const, fun _ _ => rfl⟩ ⟨contDiff_const, fun _ _ => rfl⟩ h1 h2

/-- `forceClassT` is inhabited (the zero force), so `bIntegral` is not vacuous. -/
example : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ⟨Icc 1 2, isCompact_Icc, ?_, ?_⟩⟩
  · intro _ _ _ _; rfl
  · intro s hs; exact lt_of_lt_of_le one_pos hs.1
  · exact subset_trans (by simp [tsupport]) (empty_subset _)

end NSFormalization.Section3.T20
