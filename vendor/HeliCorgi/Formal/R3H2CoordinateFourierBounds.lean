import Formal.R3H2VelocityFourierL1Bound

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/-- A single coordinate of an `R³` Schwartz velocity is pointwise dominated by the full velocity
norm. -/
theorem norm_r3SchwartzCoordinate_le
    (i : Fin 3) (f : R3SchwartzVelocity) (ξ : R3) :
    ‖r3SchwartzCoordinate i f ξ‖ ≤ ‖f ξ‖ := by
  rw [r3SchwartzCoordinate_apply]
  exact PiLp.norm_apply_le (f ξ) i

/-- Fourier transform commutes with extraction of a fixed velocity coordinate. -/
theorem fourier_r3SchwartzCoordinate_eq
    (i : Fin 3) (f : R3SchwartzVelocity) :
    𝓕 (r3SchwartzCoordinate i f) = r3SchwartzCoordinate i (𝓕 f) := by
  ext ξ
  change
    (𝓕 (fun x : R3 => f x i)) ξ =
      (𝓕 (fun x : R3 => f x)) ξ i
  rw [Real.fourier_eq, Real.fourier_eq]
  have hcoord : ∀ v : R3C, r3CoordinateFiberAux i v = v i := by
    intro v
    rfl
  simpa only [Circle.smul_def, map_smul, PiLp.smul_apply, hcoord] using
    (r3CoordinateFiberAux i).integral_comp_comm
      ((Real.fourierIntegral_convergent_iff ξ).2 f.integrable)

/-- The `L¹` norm of one Schwartz velocity coordinate is dominated by the vector-valued `L¹` norm. -/
theorem integral_norm_r3SchwartzCoordinate_le
    (i : Fin 3) (f : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖r3SchwartzCoordinate i f ξ‖) ≤
      ∫ ξ : R3, ‖f ξ‖ := by
  exact integral_mono
    (Integrable.norm (r3SchwartzCoordinate i f).integrable)
    (Integrable.norm f.integrable)
    (fun ξ => norm_r3SchwartzCoordinate_le i f ξ)

/-- Each coordinate of the Fourier-transformed velocity has quantitative `L¹` control by the
canonical H³ norm. -/
theorem integral_norm_r3SchwartzCoordinate_fourier_le_H3
    (i : Fin 3) (f : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖r3SchwartzCoordinate i (𝓕 f) ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 f‖ := by
  exact (integral_norm_r3SchwartzCoordinate_le i (𝓕 f)).trans
    (integral_norm_fourier_r3SchwartzVelocity_le_H3 f)

/-- The literal Fourier transform of one physical coordinate has the same H³-controlled `L¹`
bound, using Fourier/coordinate commutation. -/
theorem integral_norm_fourier_r3SchwartzCoordinate_le_H3
    (i : Fin 3) (f : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖(𝓕 (r3SchwartzCoordinate i f)) ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 f‖ := by
  rw [fourier_r3SchwartzCoordinate_eq]
  exact integral_norm_r3SchwartzCoordinate_fourier_le_H3 i f

/-- Order-two weighting preserves the coordinate-versus-vector pointwise norm domination. -/
theorem norm_r3H2WeightedScalarSchwartz_coordinate_le_velocity
    (i : Fin 3) (f : R3SchwartzVelocity) (ξ : R3) :
    ‖r3H2WeightedScalarSchwartz (r3SchwartzCoordinate i f) ξ‖ ≤
      ‖r3H2WeightedVelocitySchwartz f ξ‖ := by
  rw [norm_r3H2WeightedScalarSchwartz, norm_r3H2WeightedVelocitySchwartz]
  exact mul_le_mul_of_nonneg_left
    (norm_r3SchwartzCoordinate_le i f ξ)
    (le_of_lt (r3H2BesselWeight_pos ξ))

/-- The weighted scalar coordinate `L²` norm is dominated by the weighted vector `L²` norm. -/
theorem norm_r3H2WeightedScalarSchwartz_coordinate_toLp_le
    (i : Fin 3) (f : R3SchwartzVelocity) :
    ‖(r3H2WeightedScalarSchwartz (r3SchwartzCoordinate i f)).toLp
        2 (volume : Measure R3)‖ ≤
      ‖(r3H2WeightedVelocitySchwartz f).toLp
        2 (volume : Measure R3)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [
    (r3H2WeightedScalarSchwartz (r3SchwartzCoordinate i f)).coeFn_toLp
      2 (volume : Measure R3),
    (r3H2WeightedVelocitySchwartz f).coeFn_toLp
      2 (volume : Measure R3)]
    with ξ hs hv
  rw [hs, hv]
  exact norm_r3H2WeightedScalarSchwartz_coordinate_le_velocity i f ξ

/-- The order-two weighted Fourier coordinate `L²` norm is controlled by the canonical H³ norm. -/
theorem norm_r3H2WeightedScalarSchwartz_coordinate_fourier_toLp_le_H3
    (i : Fin 3) (f : R3SchwartzVelocity) :
    ‖(r3H2WeightedScalarSchwartz (r3SchwartzCoordinate i (𝓕 f))).toLp
        2 (volume : Measure R3)‖ ≤
      ‖r3SchwartzToHsCLM 3 f‖ := by
  exact (norm_r3H2WeightedScalarSchwartz_coordinate_toLp_le i (𝓕 f)).trans
    (norm_r3H2WeightedVelocitySchwartz_fourier_toLp_le_H3 f)

/-- The literal Fourier transform of one physical coordinate has the same H³-controlled weighted
`L²` bound, using Fourier/coordinate commutation. -/
theorem norm_r3H2WeightedScalarSchwartz_fourier_coordinate_toLp_le_H3
    (i : Fin 3) (f : R3SchwartzVelocity) :
    ‖(r3H2WeightedScalarSchwartz (𝓕 (r3SchwartzCoordinate i f))).toLp
        2 (volume : Measure R3)‖ ≤
      ‖r3SchwartzToHsCLM 3 f‖ := by
  rw [fourier_r3SchwartzCoordinate_eq]
  exact norm_r3H2WeightedScalarSchwartz_coordinate_fourier_toLp_le_H3 i f

end

end MNS2
