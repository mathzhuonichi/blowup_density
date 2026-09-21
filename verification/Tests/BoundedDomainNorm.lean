import Contracts.V1.BoundedDomainNorm
import Bindings.BoundedDomainNorm
import TestSupport.Axioms

/-!
# Tests for `T04.bounded_domain_norm`

The checked record is the registered three-field API.  The examples below
repeat the public field shape and instantiate the zero-extension comparison on
a concrete nonzero smooth bump supported in a compact ball strictly inside an
open ball.
-/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.BoundedDomainNorm
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal Topology SchwartzMap

/-- The implementation supplies the complete bounded-domain norm API. -/
theorem checkedBoundedDomainNorm : BoundedDomainNormAPI :=
  Bindings.BoundedDomainNorm.boundedDomainNorm

run_cmd TestSupport.checkAxioms ``checkedBoundedDomainNorm

theorem checkedBoundedDomainNormStatement : boundedDomainNormStatement :=
  Bindings.BoundedDomainNorm.boundedDomainNormStatement_holds

run_cmd TestSupport.checkAxioms ``checkedBoundedDomainNormStatement

/-! ## Independent conformance with `research/T22/Spec.lean` -/

example :
    ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
      ContDiffOn ℝ ∞ z Ω →
      domainSobolevENorm Ω 0 (restrictField Ω z) =
        eLpNorm z 2 (volume.restrict Ω) :=
  checkedBoundedDomainNorm.orderZero

/-! ## Non-vacuity on a ball and a nonzero `ContDiffBump` field -/

example (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      domainSobolevENorm NSFormalization.Section3.T22.nonvacuityΩ s
          (restrictField NSFormalization.Section3.T22.nonvacuityΩ
            NSFormalization.Section3.T22.nonvacuityField) ≤
        sobolevENorm s
          (zeroExtension NSFormalization.Section3.T22.nonvacuityΩ
            NSFormalization.Section3.T22.nonvacuityField) ∧
      sobolevENorm s
          (zeroExtension NSFormalization.Section3.T22.nonvacuityΩ
            NSFormalization.Section3.T22.nonvacuityField) ≤
        ENNReal.ofReal C *
          domainSobolevENorm NSFormalization.Section3.T22.nonvacuityΩ s
            (restrictField NSFormalization.Section3.T22.nonvacuityΩ
              NSFormalization.Section3.T22.nonvacuityField) ∧
      NSFormalization.Section3.T22.nonvacuityField 0 ≠ 0 := by
  obtain ⟨C, hC, hbound⟩ :=
    checkedBoundedDomainNorm.zeroExtensionComparison
      NSFormalization.Section3.T22.nonvacuityΩ
      NSFormalization.Section3.T22.nonvacuityK
      NSFormalization.Section3.T22.nonvacuityΩ_open
      NSFormalization.Section3.T22.nonvacuityK_compact
      NSFormalization.Section3.T22.nonvacuityK_subset_Ω s
  obtain ⟨hleft, hright⟩ := hbound
    NSFormalization.Section3.T22.nonvacuityField
    NSFormalization.Section3.T22.nonvacuityField_contDiff.contDiffOn
    NSFormalization.Section3.T22.nonvacuityField_support
  exact ⟨C, hC, hleft, hright,
    NSFormalization.Section3.T22.nonvacuityField_ne_zero⟩

end BlowupDensity.Tests
