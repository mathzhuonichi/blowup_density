import Contracts.V1.Correction3
import Bindings.Correction3
import TestSupport.Axioms

/-! T17: the completed G4 block, three independent Spec field checks, and
non-vacuity at a nonzero periodic reference centred inside the cube. -/
noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal Topology BigOperators

/-- All 45 fields under exactly the completed G4 hypotheses. -/
theorem checkedCorrection3 : Correction3.correctionStatementAmended :=
  Bindings.Correction3.correctionStatementAmended_holds

run_cmd TestSupport.checkAxioms ``checkedCorrection3

/-- Independent check of the complete raw-field hypothesis block. -/
example : ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : Correction3.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (Correction3.CorrectionAPI ν place v r δ D) := checkedCorrection3

section SpecConformance
open Correction3.Packet
variable {ν : ℝ} {P : PacketAPI ν} (place : Correction3.Packet.PlacementData P)
  (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
  (A : Correction3.Packet.CorrectionAPI ν place v r δ D)

/-- Spec.lean:837-840: the exact force profile identity, including ε⁻². -/
example : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
    correctionForce ν v D ε (correctionChartPoint place ε z) =
      (ε ^ 2)⁻¹ • rescaledForceProfile ν v place ε D z := A.force_profile_identity

/-- Spec.lean:935-939: both endpoint exponents and the slice Fact guard. -/
example : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      Correction3.mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal (A.mixedConst p q * ε ^ (Correction3.alphaT p q + 1)) :=
  A.force_mixed_bound

/-- Spec.lean:955-961: the full Sobolev range and the sum of the two rates. -/
example : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
      ENNReal.ofReal (A.sobolevConst s *
        (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := A.force_sobolev_bound
end SpecConformance

/-- The registered records retain a nonzero reference and an actual admissible
scale; this is a full API witness, not a conditional field check. -/
theorem checkedCorrection3_nonvacuous :
    NSFormalization.Section3.T17.Nonvacuity.reference ≠ 0 ∧
    ∃ D : CutoffData, 0 < D.ε₀ ∧ D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ ∧
      Nonempty (Correction3.CorrectionAPI 1
        (Bindings.Correction3.placementToContract NSFormalization.Section3.T17.Nonvacuity.place)
        NSFormalization.Section3.T17.Nonvacuity.reference (1 / 4) 1 D) :=
  Bindings.Correction3.nonvacuous_correction

run_cmd TestSupport.checkAxioms ``checkedCorrection3_nonvacuous
end BlowupDensity.Tests
