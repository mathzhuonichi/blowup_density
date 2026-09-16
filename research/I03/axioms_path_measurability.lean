import Bindings.ScalingHomogeneousClosed

open Set MeasureTheory
open NSFormalization.Paper3
open BlowupDensity.Contracts.V1
open BlowupDensity.Bindings
open scoped ENNReal ContDiff

namespace NSFormalization.Section4.I03

#print axioms compactHomogeneousPath_sub_enorm_sq_le
#print axioms compactHomogeneousPath_sub_norm_sq_le
#print axioms compactHomogeneousPath_continuous
#print axioms compactHomogeneousPath_aestronglyMeasurable
#print axioms compactHomogeneousRealization
#print axioms homogeneousScalingClosed
#print axioms packetNegativeHomogeneous'
#print axioms correctionNegativeHomogeneous'

/-! Non-vacuity probes: the continuity theorem applies to an actual packet
profile, and both closed fields specialize at the manuscript endpoint
`q = 2`, `s = -1`. -/

example {ν : ℝ} (P : PacketAPI ν) :
    Continuous (D01.Homogeneous.compactHomogeneousPath
      (by norm_num : -3 / 2 < (-1 : ℝ)) P.force_smooth P.force_support.1) :=
  compactHomogeneousPath_continuous (by norm_num) (by norm_num)
    P.force_smooth P.force_support.1

example {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) (th : ThresholdAPI)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (homogeneousScalingClosed C th).scaling.ε₀) :
    Data.forceHomogeneousENorm 2 (-1)
        (scaledForce P.force (homogeneousScalingClosed C th).scaling.correction.x₀
          (homogeneousScalingClosed C th).scaling.correction.T ε) ≤
      ENNReal.ofReal ((homogeneousScalingClosed C th).packetHomogeneousConst 2 (-1) *
        ε ^ (homogeneousScalingClosed C th).scaling.thresholds.exponent 2 (-1)) :=
  packetNegativeHomogeneous' C th 2 (by norm_num) (-1) (by norm_num) (by norm_num) ε hε

example {ν : ℝ} {P : PacketAPI ν} (C : CorrectionAPI ν P) (th : ThresholdAPI)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (homogeneousScalingClosed C th).scaling.ε₀) :
    Data.forceHomogeneousENorm 2 (-1)
        ((homogeneousScalingClosed C th).scaling.correction.forceCorrection ε) ≤
      ENNReal.ofReal ((homogeneousScalingClosed C th).correctionHomogeneousConst 2 (-1) *
        ε ^ ((homogeneousScalingClosed C th).scaling.thresholds.exponent 2 (-1) + 1)) :=
  correctionNegativeHomogeneous' C th 2 (by norm_num) (-1)
    (by norm_num) (by norm_num) ε hε

end NSFormalization.Section4.I03
