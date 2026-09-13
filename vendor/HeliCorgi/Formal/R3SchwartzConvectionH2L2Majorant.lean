import Formal.R3SchwartzScalarMajorantL2

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/--
The pointwise H² frequency majorant lifts to an `L²` norm estimate for one physical convection
summand.  At this stage the two ordinary scalar majorants remain as bundled `L²` norms.
-/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_scalarMajorants
    (i : Fin 3) (u v : R3SchwartzVelocity) :
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzConvectionTerm i u v))).toLp
          2 (volume : Measure R3)‖ ≤
      2 *
        (‖r3H2LeftScalarMajorantL2
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v))‖ +
          ‖r3H2RightScalarMajorantL2
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v))‖) := by
  let a : R3SchwartzScalar := 𝓕 (r3SchwartzCoordinate i u)
  let b : R3SchwartzVelocity := 𝓕 (r3SchwartzCoordinateDerivative i v)
  calc
    ‖(r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzConvectionTerm i u v))).toLp
          2 (volume : Measure R3)‖ ≤
        2 * ‖r3H2LeftScalarMajorantL2 a b + r3H2RightScalarMajorantL2 a b‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards
        [(r3H2WeightedVelocitySchwartz
            (𝓕 (r3SchwartzConvectionTerm i u v))).coeFn_toLp
              2 (volume : Measure R3),
          Lp.coeFn_add (r3H2LeftScalarMajorantL2 a b)
            (r3H2RightScalarMajorantL2 a b),
          MemLp.coeFn_toLp (memLp_r3H2LeftScalarMajorant a b),
          MemLp.coeFn_toLp (memLp_r3H2RightScalarMajorant a b)]
        with ξ hweighted hadd hleft hright
      have hadd' :
          (r3H2LeftScalarMajorantL2 a b + r3H2RightScalarMajorantL2 a b) ξ =
            (r3H2LeftScalarMajorantL2 a b : R3 → ℝ) ξ +
              (r3H2RightScalarMajorantL2 a b : R3 → ℝ) ξ := by
        simpa only [Pi.add_apply] using hadd
      have hleft' :
          (r3H2LeftScalarMajorantL2 a b : R3 → ℝ) ξ =
            r3H2LeftScalarMajorant a b ξ := by
        simpa [r3H2LeftScalarMajorantL2] using hleft
      have hright' :
          (r3H2RightScalarMajorantL2 a b : R3 → ℝ) ξ =
            r3H2RightScalarMajorant a b ξ := by
        simpa [r3H2RightScalarMajorantL2] using hright
      rw [hweighted, hadd', hleft', hright']
      rw [Real.norm_of_nonneg
        (add_nonneg (r3H2LeftScalarMajorant_nonneg a b ξ)
          (r3H2RightScalarMajorant_nonneg a b ξ))]
      simpa [a, b] using
        (norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_le_scalarMajorants
          i u v ξ)
    _ ≤ 2 *
        (‖r3H2LeftScalarMajorantL2 a b‖ +
          ‖r3H2RightScalarMajorantL2 a b‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_add_le (r3H2LeftScalarMajorantL2 a b)
          (r3H2RightScalarMajorantL2 a b)) (by norm_num)
    _ = 2 *
        (‖r3H2LeftScalarMajorantL2
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v))‖ +
          ‖r3H2RightScalarMajorantL2
            (𝓕 (r3SchwartzCoordinate i u))
            (𝓕 (r3SchwartzCoordinateDerivative i v))‖) := by
      rfl

/--
The preceding `L²` estimate with the two scalar-majorant norms discharged by the Young bounds.
This is the direct analytic input for the existing H³ Fourier estimates.
-/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_YoungFactors
    (i : Fin 3) (u v : R3SchwartzVelocity) :
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
                2 (volume : Measure R3)‖) := by
  have hmajorant :=
    norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_toLp_le_scalarMajorants
      i u v
  have hleft :=
    norm_r3H2LeftScalarMajorantL2_le
      (𝓕 (r3SchwartzCoordinate i u))
      (𝓕 (r3SchwartzCoordinateDerivative i v))
  have hright :=
    norm_r3H2RightScalarMajorantL2_le
      (𝓕 (r3SchwartzCoordinate i u))
      (𝓕 (r3SchwartzCoordinateDerivative i v))
  have hsum := add_le_add hleft hright
  exact hmajorant.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

end

end MNS2
