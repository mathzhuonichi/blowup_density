import NSFormalization.Section3.T23.Boundary

/-!
# T23 bounded-domain norm vocabulary

Definition bridges for the five bounded-domain energy and force norms used by
the boundary insertion API.  The comparison theorem itself is developed in
`DomainComparison`.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section3.T22
open scoped ENNReal

/-- Whole-definition bridge for the domain `L∞_t L²_x` term copied into the
T23 boundary vocabulary. -/
theorem domainEnergyEssSup_eq (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyEssSup Ω T z =
      essSup (fun t ↦ eLpNorm (fun x ↦ z (t, x)) 2 (volume.restrict Ω))
        (volume.restrict (Ioo (0 : ℝ) T)) := rfl

/-- Whole-definition bridge for the domain `L²_t L²_x` gradient term. -/
theorem domainEnergyGradient_eq (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyGradient Ω T z =
      (∫⁻ t in Ioo (0 : ℝ) T,
          (eLpNorm (fun x ↦ spatialGradient z t x) 2 (volume.restrict Ω)) ^ (2 : ℝ))
        ^ ((2 : ℝ)⁻¹) := rfl

/-- Whole-definition bridge for the bounded-domain energy norm. -/
theorem domainEnergyENorm_eq (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) :
    domainEnergyENorm Ω T z =
      domainEnergyEssSup Ω T z + domainEnergyGradient Ω T z := rfl

/-- Whole-definition bridge for the per-slice domain Sobolev force norm. -/
theorem domainForceSobolevENorm_eq (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    domainForceSobolevENorm Ω s f =
      ∫⁻ t in Ioi (0 : ℝ),
        domainSobolevENorm Ω s (restrictField Ω (fun x ↦ f (t, x))) := rfl

/-- Whole-definition bridge for the force norm of the literal zero extension. -/
theorem zeroExtForceSobolevENorm_eq (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    zeroExtForceSobolevENorm Ω s f =
      ∫⁻ t in Ioi (0 : ℝ),
        NSFormalization.Section4.D01.sobolevENorm s
          (zeroExtension Ω (fun x ↦ f (t, x))) := rfl

end NSFormalization.Section3.T23
