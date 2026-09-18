import NSFormalization.Section3.T17.Correction
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
open NSFormalization.Section3.T17
open scoped ContDiff Topology
-- Attempt the requested U4 exact check for the canonical field, without mutation.
example (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : NSFormalization.Section3.T16.CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint x₀ T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z := by
  exact physicalForce_eq_rescaledForceProfile ν hv x₀ T D hθ hη
