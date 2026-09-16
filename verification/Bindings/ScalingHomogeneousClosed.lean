import Bindings.ScalingHomogeneous
import NSFormalization.Section4.I03.PathMeasurability

/-!
# Unconditional homogeneous scaling

`PathMeasurability` proves the only named input left by lane 250.  This binding
discharges it in the registered `Contracts.V1.Data` vocabulary and exposes the
two homogeneous fields with the exact quantifier order of
`research/I03/Spec.lean` / `Contracts/V1/Scaling.lean`.

This file must live in `verification/Bindings`: `CompactHomogeneousRealization`
and `HomogeneousScalingAPI` mention the downstream Contracts library, which the
upstream `NSFormalization` package cannot import.
-/

noncomputable section

namespace NSFormalization.Section4.I03

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings
open scoped ENNReal

/-- Lane 250's sole named input: every explicit D01 compact homogeneous path
is a.e. strongly measurable on positive time. -/
theorem compactHomogeneousRealization : CompactHomogeneousRealization := by
  intro s hs hs0 F hF hc
  exact compactHomogeneousPath_aestronglyMeasurable hs hs0 hF hc

/-- The existing homogeneous scaling package with its path-realization input
discharged. -/
def homogeneousScalingClosed {ν : ℝ} {P : PacketAPI ν}
    (C : CorrectionAPI ν P) (th : ThresholdAPI) : HomogeneousScalingAPI ν P :=
  homogeneousScaling compactHomogeneousRealization C th

/-- `research/I03/Spec.lean`'s `packetNegativeHomogeneous` field, with exactly
its binder order and with the closed package's finite packet constants. -/
theorem packetNegativeHomogeneous' {ν : ℝ} {P : PacketAPI ν}
    (C : CorrectionAPI ν P) (th : ThresholdAPI) :
    ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) (homogeneousScalingClosed C th).scaling.ε₀,
      Data.forceHomogeneousENorm q s
          (scaledForce P.force (homogeneousScalingClosed C th).scaling.correction.x₀
            (homogeneousScalingClosed C th).scaling.correction.T ε) ≤
        ENNReal.ofReal ((homogeneousScalingClosed C th).packetHomogeneousConst q s *
          ε ^ (homogeneousScalingClosed C th).scaling.thresholds.exponent q.toReal s) :=
  (homogeneousScalingClosed C th).packetNegativeHomogeneous

/-- `research/I03/Spec.lean`'s `correctionNegativeHomogeneous` field, with
exactly its binder order and with the closed package's uniform correction
constants. -/
theorem correctionNegativeHomogeneous' {ν : ℝ} {P : PacketAPI ν}
    (C : CorrectionAPI ν P) (th : ThresholdAPI) :
    ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) (homogeneousScalingClosed C th).scaling.ε₀,
      Data.forceHomogeneousENorm q s
          ((homogeneousScalingClosed C th).scaling.correction.forceCorrection ε) ≤
        ENNReal.ofReal ((homogeneousScalingClosed C th).correctionHomogeneousConst q s *
          ε ^ ((homogeneousScalingClosed C th).scaling.thresholds.exponent q.toReal s + 1)) :=
  (homogeneousScalingClosed C th).correctionNegativeHomogeneous

end NSFormalization.Section4.I03
