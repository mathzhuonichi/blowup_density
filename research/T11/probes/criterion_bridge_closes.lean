import NSFormalization.Section3.T11.CriterionBridge

/-! All-order datum existence and the squared H² continuation criterion. -/
noncomputable section
namespace NSFormalization.Section3.T11.CriterionBridgeProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ContDiff ENNReal BigOperators

open NSFormalization.Section3.T11

example {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) :
    periodicSobolevENorm s z = ‖A‖ₑ := by
  exact periodicSobolevENorm_eq_datum hA

example (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    ∃ A : PeriodicSobolev s, IsPeriodicDatum s z A := by
  exact exists_periodicDatum_smooth s hs hp

example (s : ℝ) {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicSobolevENorm s z ≠ ⊤ := by
  exact periodicSobolevENorm_ne_top_smooth s hs hp

example {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    ‖A‖ = periodicVectorSobolevNorm s u t := by
  exact norm_periodicDatum hA

example {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t) := by
  exact periodicSobolevENorm_eq_of_datum hA

example (s : ℝ) (u : SpaceTimeField) (t : ℝ)
    (hs : ContDiff ℝ ∞ (fun x ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x ↦ u (t, x))) :
    periodicSobolevENorm s (fun x ↦ u (t, x)) =
      ENNReal.ofReal (periodicVectorSobolevNorm s u t) := by
  exact periodicSobolevENorm_eq_smooth s u t hs hp

example {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ContinuousOn (fun t ↦ periodicSobolevENorm (m : ℝ) (fun x ↦ w.velocity (t, x)))
      (Ico (0 : ℝ) T) := by
  exact continuousOn_periodicSobolevENorm w m

example {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) :
    AEMeasurable (fun t ↦ periodicSobolevENorm 2 (fun x ↦ w.velocity (t, x)))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  exact aemeasurable_periodicSobolevENorm w

example {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f S) :
    ContinuousOn (h2SquaredProfile (toFlow w)) (Ico (0 : ℝ) S) := by
  exact continuousOn_h2SquaredProfile w

example
    {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f S) :
    squaredHTwoIntegralT S w.velocity ≠ ⊤ ↔ FiniteH2Energy (toFlow w) := by
  exact squaredHTwoIntegralT_ne_top_iff_finiteH2Energy w

example (s : ℝ) : periodicSobolevENorm s (fun _ ↦ coordinateVector 0) ≠ ⊤ :=
  periodicSobolevENorm_ne_top_smooth s contDiff_const (fun _ _ ↦ rfl)

end NSFormalization.Section3.T11.CriterionBridgeProbe
