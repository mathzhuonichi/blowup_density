import Formal.R3SchwartzConvectionH2L2Majorant
import Formal.R3SchwartzDerivativeH3LpBounds

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/--
For one fixed physical coordinate, the H² weighted Fourier norm of the convection summand is
controlled by the two H³ input norms.  The only coordinate-dependent factor left is the explicit
Fourier derivative constant `r3CoordinateDerivativeFrequencyConstant i`.

This combines the representative/Young bridge with the previously established H³ Fourier `L¹` and
weighted `L²` estimates; no Navier--Stokes local-wellposedness statement is used here.
-/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_H3
    (i : Fin 3) (u v : R3SchwartzVelocity) :
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzConvectionTerm i u v))).toLp
          2 (volume : Measure R3)‖ ≤
      4 * ‖r3H2InverseBesselWeightL2‖ *
        r3CoordinateDerivativeFrequencyConstant i *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
  have hyoung :=
    norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_YoungFactors
      i u v
  have hleftL2 :=
    norm_r3H2WeightedScalarSchwartz_fourier_coordinate_toLp_le_H3 i u
  have hrightL1 :=
    integral_norm_fourier_r3SchwartzCoordinateDerivative_le_H3 i v
  have hleftL1 :=
    integral_norm_fourier_r3SchwartzCoordinate_le_H3 i u
  have hrightL2 :=
    norm_r3H2WeightedVelocitySchwartz_fourier_coordinateDerivative_toLp_le_H3 i v
  have hderL1_nonneg :
      0 ≤ ∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖ := by
    exact integral_nonneg (fun ξ => norm_nonneg _)
  have hderL2_nonneg :
      0 ≤ ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
          2 (volume : Measure R3)‖ :=
    norm_nonneg _
  have hH3u_nonneg : 0 ≤ ‖r3SchwartzToHsCLM 3 u‖ := norm_nonneg _
  have hweightedH3u_nonneg :
      0 ≤ ‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 u‖ :=
    mul_nonneg (norm_nonneg _) hH3u_nonneg
  have hfirst :
      ‖(r3H2WeightedScalarSchwartz
          (𝓕 (r3SchwartzCoordinate i u))).toLp
          2 (volume : Measure R3)‖ *
        (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) ≤
      ‖r3SchwartzToHsCLM 3 u‖ *
        (‖r3H2InverseBesselWeightL2‖ *
          (r3CoordinateDerivativeFrequencyConstant i *
            ‖r3SchwartzToHsCLM 3 v‖)) := by
    calc
      ‖(r3H2WeightedScalarSchwartz
          (𝓕 (r3SchwartzCoordinate i u))).toLp
          2 (volume : Measure R3)‖ *
          (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) ≤
        ‖r3SchwartzToHsCLM 3 u‖ *
          (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) :=
        mul_le_mul_of_nonneg_right hleftL2 hderL1_nonneg
      _ ≤ ‖r3SchwartzToHsCLM 3 u‖ *
          (‖r3H2InverseBesselWeightL2‖ *
            (r3CoordinateDerivativeFrequencyConstant i *
              ‖r3SchwartzToHsCLM 3 v‖)) :=
        mul_le_mul_of_nonneg_left hrightL1 hH3u_nonneg
  have hsecond :
      (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinate i u)) ξ‖) *
        ‖(r3H2WeightedVelocitySchwartz
          (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
          2 (volume : Measure R3)‖ ≤
      (‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 u‖) *
        (r3CoordinateDerivativeFrequencyConstant i *
          ‖r3SchwartzToHsCLM 3 v‖) := by
    calc
      (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinate i u)) ξ‖) *
          ‖(r3H2WeightedVelocitySchwartz
            (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
            2 (volume : Measure R3)‖ ≤
        (‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 u‖) *
          ‖(r3H2WeightedVelocitySchwartz
            (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
            2 (volume : Measure R3)‖ :=
        mul_le_mul_of_nonneg_right hleftL1 hderL2_nonneg
      _ ≤ (‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 u‖) *
          (r3CoordinateDerivativeFrequencyConstant i *
            ‖r3SchwartzToHsCLM 3 v‖) :=
        mul_le_mul_of_nonneg_left hrightL2 hweightedH3u_nonneg
  have hsum := add_le_add hfirst hsecond
  calc
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzConvectionTerm i u v))).toLp
          2 (volume : Measure R3)‖ ≤
      2 *
        (‖(r3H2WeightedScalarSchwartz
              (𝓕 (r3SchwartzCoordinate i u))).toLp
              2 (volume : Measure R3)‖ *
            (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) +
          (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinate i u)) ξ‖) *
            ‖(r3H2WeightedVelocitySchwartz
                (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
                2 (volume : Measure R3)‖) :=
      hyoung
    _ ≤ 2 *
        (‖r3SchwartzToHsCLM 3 u‖ *
            (‖r3H2InverseBesselWeightL2‖ *
              (r3CoordinateDerivativeFrequencyConstant i *
                ‖r3SchwartzToHsCLM 3 v‖)) +
          (‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 u‖) *
            (r3CoordinateDerivativeFrequencyConstant i *
              ‖r3SchwartzToHsCLM 3 v‖)) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * ‖r3H2InverseBesselWeightL2‖ *
        r3CoordinateDerivativeFrequencyConstant i *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
      ring

/-- The preceding frequency-side estimate rewritten as the canonical physical H² Sobolev norm. -/
theorem norm_r3SchwartzToHsCLM_two_convectionTerm_le_H3
    (i : Fin 3) (u v : R3SchwartzVelocity) :
    ‖r3SchwartzToHsCLM 2 (r3SchwartzConvectionTerm i u v)‖ ≤
      4 * ‖r3H2InverseBesselWeightL2‖ *
        r3CoordinateDerivativeFrequencyConstant i *
        ‖r3SchwartzToHsCLM 3 u‖ * ‖r3SchwartzToHsCLM 3 v‖ := by
  rw [norm_r3SchwartzToHsCLM_eq_frequencyCoordinate]
  rw [← r3H2WeightedVelocitySchwartz_fourier_eq_frequencyCoordinate]
  exact norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_H3 i u v

end

end MNS2
