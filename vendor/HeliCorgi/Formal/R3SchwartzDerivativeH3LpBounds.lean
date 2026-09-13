import Formal.R3SchwartzDerivativeFrequencyBound

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/-- The order-two weighted Fourier `L²` norm of one coordinate derivative is controlled by the
canonical H³ norm of the undifferentiated field. -/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_coordinateDerivative_toLp_le_H3
    (i : Fin 3) (v : R3SchwartzVelocity) :
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
          2 (volume : Measure R3)‖ ≤
      r3CoordinateDerivativeFrequencyConstant i * ‖r3SchwartzToHsCLM 3 v‖ := by
  calc
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
          2 (volume : Measure R3)‖ ≤
        r3CoordinateDerivativeFrequencyConstant i *
          ‖(r3SchwartzSobolevFrequencyCoordinate 3 v).toLp
            2 (volume : Measure R3)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [
        (r3H2WeightedVelocitySchwartz
          (𝓕 (r3SchwartzCoordinateDerivative i v))).coeFn_toLp
            2 (volume : Measure R3),
        (r3SchwartzSobolevFrequencyCoordinate 3 v).coeFn_toLp
          2 (volume : Measure R3)]
        with ξ hder hthree
      rw [hder, hthree]
      exact
        norm_r3H2WeightedVelocitySchwartz_fourier_coordinateDerivative_le i v ξ
    _ = r3CoordinateDerivativeFrequencyConstant i * ‖r3SchwartzToHsCLM 3 v‖ := by
      rw [← norm_r3SchwartzToHsCLM_eq_frequencyCoordinate 3 v]

/-- The unweighted Fourier `L¹` norm of one coordinate derivative is controlled by the canonical
H³ norm of the undifferentiated velocity. -/
theorem integral_norm_fourier_r3SchwartzCoordinateDerivative_le_H3
    (i : Fin 3) (v : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ *
        (r3CoordinateDerivativeFrequencyConstant i * ‖r3SchwartzToHsCLM 3 v‖) := by
  calc
    (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖) ≤
        ‖r3H2InverseBesselWeightL2‖ *
          ‖(r3H2WeightedVelocitySchwartz
              (𝓕 (r3SchwartzCoordinateDerivative i v))).toLp
                2 (volume : Measure R3)‖ :=
      integral_norm_r3SchwartzVelocity_le_H2WeightedL2
        (𝓕 (r3SchwartzCoordinateDerivative i v))
    _ ≤ ‖r3H2InverseBesselWeightL2‖ *
        (r3CoordinateDerivativeFrequencyConstant i * ‖r3SchwartzToHsCLM 3 v‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_r3H2WeightedVelocitySchwartz_fourier_coordinateDerivative_toLp_le_H3 i v)
        (norm_nonneg r3H2InverseBesselWeightL2)

end

end MNS2
