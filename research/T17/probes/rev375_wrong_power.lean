import NSFormalization.Section3.T17.ForceProfile
noncomputable section
namespace NSFormalization.Section3.T17.Rev375
open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open scoped ContDiff Topology
variable {ν : ℝ} {v : SpaceTimeField} {x₀ : Space} {T : ℝ} {D : CutoffData}
-- Substantive mutation: replace the physical ε⁻² factor by ε⁻³.
theorem field_force_profile_identity_chartForce (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
          (correctionChartPoint x₀ T ε z) =
        (ε ^ 3)⁻¹ • rescaledForceProfile ν v x₀ T ε D z :=
  physicalForce_eq_rescaledForceProfile ν hv x₀ T D hθ hη

end NSFormalization.Section3.T17.Rev375
