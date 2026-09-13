import NSFormalization.Source.TimeNormScaling
import NSFormalization.Source.VectorForceNorms

/-!
# Whole-space endpoint rates for the concentrated packet

These are direct wrappers around the proved OpenAI scaling estimates.  At
`q = 1`, the order-zero endpoint has rate `ε^(1/2)` and the order-one
endpoint has rate `ε^(-1/2)`.  The statements retain the finite endpoint
profile constants and make no periodic or critical embedding claim.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicPacketEndpointRates

open Set Filter MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Paper3
open scoped ContDiff ENNReal FourierTransform

/-- Scalar component order-zero whole-space endpoint bound for the actual
parabolic packet at positive scale `ε ≤ 1`. -/
theorem packet_scalar_H0_L1_endpoint_bound
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin 3) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (center : ℝ) :
    eLpNorm (fun t => fourierSobolevNorm 0
      (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
        eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce F i (t, x))) 1 volume := by
  have heq : (fun t => fourierSobolevNorm 0
      (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) =
      (fun t => fourierSobolevNorm 0 (parabolicComplexForce ε⁻¹ center
        (fun t x => coordinateForce F i (t, x)) t)) := by
    funext t
    exact coordinate_norm_parabolicForce 0 ε⁻¹ center 0 F i t
  rw [heq]
  have hh := force_eLpNorm_positive_epsilon (s := 0) (by norm_num) hε hε1 center 1
    (fun t x => coordinateForce F i (t, x))
    (fun t => Paper3.compact_spacetime_fourier_slice_continuous
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) t)
    (fun t => Paper3.compact_spacetime_bessel_slices 0
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) t)
    (Paper3.stronglyMeasurable_fourierSobolev_time 0
      (coordinateForce_smooth hF i).continuous)
  convert hh using 1 <;> norm_num

/-- Scalar component order-one whole-space endpoint bound for the actual
parabolic packet.  The rate is the expected `ε^(-1/2)` at `q = 1`. -/
theorem packet_scalar_H1_L1_endpoint_bound
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin 3) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (center : ℝ) :
    eLpNorm (fun t => fourierSobolevNorm 1
      (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) 1 volume ≤
      ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
        eLpNorm (fun t => fourierSobolevNorm 1
          (fun x => coordinateForce F i (t, x))) 1 volume := by
  have heq : (fun t => fourierSobolevNorm 1
      (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) =
      (fun t => fourierSobolevNorm 1 (parabolicComplexForce ε⁻¹ center
        (fun t x => coordinateForce F i (t, x)) t)) := by
    funext t
    exact coordinate_norm_parabolicForce 1 ε⁻¹ center 0 F i t
  rw [heq]
  have hh := force_eLpNorm_positive_epsilon (s := 1) (by norm_num) hε hε1 center 1
    (fun t x => coordinateForce F i (t, x))
    (fun t => Paper3.compact_spacetime_fourier_slice_continuous
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) t)
    (fun t => Paper3.compact_spacetime_bessel_slices 1
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) t)
    (Paper3.stronglyMeasurable_fourierSobolev_time 1
      (coordinateForce_smooth hF i).continuous)
  convert hh using 1 <;> norm_num

/-- Vector order-zero endpoint rate, obtained by the finite three-component
reassembly inequality. -/
theorem packet_vector_H0_L1_endpoint_bound
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (center : ℝ) :
    eLpNorm (vectorFourierSobolevNorm 0 (parabolicForce ε⁻¹ center 0 F)) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
        ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce F i (t, x))) 1 volume := by
  have hm := eLpNorm_vector_le_sum 0 (parabolicForce ε⁻¹ center 0 F) 1
    (by norm_num) (fun i =>
      (Paper3.stronglyMeasurable_fourierSobolev_time 0
        (coordinateForce_smooth (parabolicForce_smooth _ _ _ hF) i).continuous).aestronglyMeasurable)
  calc
    eLpNorm (vectorFourierSobolevNorm 0 (parabolicForce ε⁻¹ center 0 F)) 1 volume ≤
        ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 0
          (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) 1 volume := hm
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
          eLpNorm (fun t => fourierSobolevNorm 0
            (fun x => coordinateForce F i (t, x))) 1 volume := by
      apply Finset.sum_le_sum
      intro i hi
      exact packet_scalar_H0_L1_endpoint_bound hF hc i hε hε1 center
    _ = ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) *
          ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 0
            (fun x => coordinateForce F i (t, x))) 1 volume := by
      rw [Finset.mul_sum]

/-- Vector order-one endpoint rate, with the expected `ε^(-1/2)` factor. -/
theorem packet_vector_H1_L1_endpoint_bound
    {F : VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (center : ℝ) :
    eLpNorm (vectorFourierSobolevNorm 1 (parabolicForce ε⁻¹ center 0 F)) 1 volume ≤
      ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
        ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 1
          (fun x => coordinateForce F i (t, x))) 1 volume := by
  have hm := eLpNorm_vector_le_sum 1 (parabolicForce ε⁻¹ center 0 F) 1
    (by norm_num) (fun i =>
      (Paper3.stronglyMeasurable_fourierSobolev_time 1
        (coordinateForce_smooth (parabolicForce_smooth _ _ _ hF) i).continuous).aestronglyMeasurable)
  calc
    eLpNorm (vectorFourierSobolevNorm 1 (parabolicForce ε⁻¹ center 0 F)) 1 volume ≤
        ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 1
          (fun x => coordinateForce (parabolicForce ε⁻¹ center 0 F) i (t, x))) 1 volume := hm
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
          eLpNorm (fun t => fourierSobolevNorm 1
            (fun x => coordinateForce F i (t, x))) 1 volume := by
      apply Finset.sum_le_sum
      intro i hi
      exact packet_scalar_H1_L1_endpoint_bound hF hc i hε hε1 center
    _ = ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) *
          ∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm 1
            (fun x => coordinateForce F i (t, x))) 1 volume := by
      rw [Finset.mul_sum]

end NSFormalization.Paper1.PeriodicPacketEndpointRates
