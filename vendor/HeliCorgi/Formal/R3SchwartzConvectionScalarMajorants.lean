import Formal.R3SchwartzConvectionH2FrequencyMajorant

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/-- The left scalar majorant produced by the additive order-two Bessel split. -/
def r3H2LeftScalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) : ℝ :=
  ∫ η : R3,
    ‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖

/-- The right scalar majorant produced by the additive order-two Bessel split. -/
def r3H2RightScalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) : ℝ :=
  ∫ η : R3,
    ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖

/-- The left scalar-majorant integrand is integrable for every output frequency. -/
theorem integrable_r3H2LeftScalarMajorant_integrand
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    Integrable (fun η : R3 =>
      ‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖) := by
  have hA2shift :
      Integrable (fun η : R3 => ‖r3H2WeightedScalarSchwartz a (ξ - η)‖) := by
    simpa using
      ((r3H2WeightedScalarSchwartz a).integrable.norm.comp_sub_left ξ)
  have hbMeas : AEStronglyMeasurable (fun η : R3 => ‖b η‖) :=
    b.continuous.norm.aestronglyMeasurable
  have hbBound :
      ∀ᵐ η : R3, ‖(‖b η‖ : ℝ)‖ ≤ SchwartzMap.seminorm ℝ 0 0 b := by
    filter_upwards with η
    simpa [Real.norm_of_nonneg (norm_nonneg (b η))] using
      (SchwartzMap.norm_le_seminorm ℝ b η)
  exact hA2shift.mul_bdd hbMeas hbBound

/-- The right scalar-majorant integrand is integrable for every output frequency. -/
theorem integrable_r3H2RightScalarMajorant_integrand
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    Integrable (fun η : R3 =>
      ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
  have haShift : Integrable (fun η : R3 => ‖a (ξ - η)‖) := by
    simpa using (a.integrable.norm.comp_sub_left ξ)
  have hB2Meas :
      AEStronglyMeasurable (fun η : R3 => ‖r3H2WeightedVelocitySchwartz b η‖) :=
    (r3H2WeightedVelocitySchwartz b).continuous.norm.aestronglyMeasurable
  have hB2Bound :
      ∀ᵐ η : R3,
        ‖(‖r3H2WeightedVelocitySchwartz b η‖ : ℝ)‖ ≤
          SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedVelocitySchwartz b) := by
    filter_upwards with η
    simpa [Real.norm_of_nonneg (norm_nonneg (r3H2WeightedVelocitySchwartz b η))] using
      (SchwartzMap.norm_le_seminorm ℝ (r3H2WeightedVelocitySchwartz b) η)
  exact haShift.mul_bdd hB2Meas hB2Bound

/-- The left majorant is exactly the ordinary real scalar convolution of the two norm fields. -/
theorem r3H2LeftScalarMajorant_eq_convolution
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    r3H2LeftScalarMajorant a b ξ =
      MeasureTheory.convolution
        (fun ζ : R3 => ‖r3H2WeightedScalarSchwartz a ζ‖)
        (fun η : R3 => ‖b η‖)
        (ContinuousLinearMap.mul ℝ ℝ) (volume : Measure R3) ξ := by
  simpa [r3H2LeftScalarMajorant] using
    (MeasureTheory.convolution_eq_swap
      (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := fun ζ : R3 => ‖r3H2WeightedScalarSchwartz a ζ‖)
      (g := fun η : R3 => ‖b η‖)
      (μ := (volume : Measure R3))
      (x := ξ)).symm

/-- The right majorant is exactly the ordinary real scalar convolution of the two norm fields. -/
theorem r3H2RightScalarMajorant_eq_convolution
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    r3H2RightScalarMajorant a b ξ =
      MeasureTheory.convolution
        (fun ζ : R3 => ‖a ζ‖)
        (fun η : R3 => ‖r3H2WeightedVelocitySchwartz b η‖)
        (ContinuousLinearMap.mul ℝ ℝ) (volume : Measure R3) ξ := by
  simpa [r3H2RightScalarMajorant] using
    (MeasureTheory.convolution_eq_swap
      (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := fun ζ : R3 => ‖a ζ‖)
      (g := fun η : R3 => ‖r3H2WeightedVelocitySchwartz b η‖)
      (μ := (volume : Measure R3))
      (x := ξ)).symm

/-- Both scalar majorants are nonnegative. -/
theorem r3H2LeftScalarMajorant_nonneg
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    0 ≤ r3H2LeftScalarMajorant a b ξ := by
  exact integral_nonneg fun η =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Both scalar majorants are nonnegative. -/
theorem r3H2RightScalarMajorant_nonneg
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    0 ≤ r3H2RightScalarMajorant a b ξ := by
  exact integral_nonneg fun η =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)

/--
The pointwise H²-frequency estimate for one physical convection summand, now separated into two
named scalar convolutions.  The remaining analytic gate is to bundle these scalar convolutions in
`L²` and apply the two Young estimates.
-/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_le_scalarMajorants
    (i : Fin 3) (u v : R3SchwartzVelocity) (ξ : R3) :
    ‖r3H2WeightedVelocitySchwartz (𝓕 (r3SchwartzConvectionTerm i u v)) ξ‖ ≤
      2 *
        (r3H2LeftScalarMajorant
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ +
          r3H2RightScalarMajorant
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ) := by
  calc
    ‖r3H2WeightedVelocitySchwartz (𝓕 (r3SchwartzConvectionTerm i u v)) ξ‖ ≤
        2 * ∫ η : R3,
          (‖r3H2WeightedScalarSchwartz (𝓕 (r3SchwartzCoordinate i u)) (ξ - η)‖ *
              ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) η‖ +
            ‖(𝓕 (r3SchwartzCoordinate i u)) (ξ - η)‖ *
              ‖r3H2WeightedVelocitySchwartz
                (𝓕 (r3SchwartzCoordinateDerivative i v)) η‖) :=
      norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_le_additiveIntegral i u v ξ
    _ = 2 *
        (r3H2LeftScalarMajorant
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ +
          r3H2RightScalarMajorant
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ) := by
      rw [integral_add
        (integrable_r3H2LeftScalarMajorant_integrand
          (𝓕 (r3SchwartzCoordinate i u))
          (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ)
        (integrable_r3H2RightScalarMajorant_integrand
          (𝓕 (r3SchwartzCoordinate i u))
          (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ)]
      rfl

end

end MNS2
