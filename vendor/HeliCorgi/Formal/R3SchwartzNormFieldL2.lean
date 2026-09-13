import Formal.R3YoungRealL1L2Bochner
import Formal.R3H2YoungWeightedBridge

namespace MNS2

open MeasureTheory

noncomputable section

/-- The pointwise norm of a complex scalar Schwartz field, bundled canonically in real `L²(R³)`. -/
def r3SchwartzScalarNormL2 (a : R3SchwartzScalar) : R3L2RealScalar :=
  ((a.memLp 2 (volume : Measure R3)).norm).toLp (fun ξ : R3 => ‖a ξ‖)

/-- The pointwise norm of a complex velocity Schwartz field, bundled canonically in real `L²(R³)`. -/
def r3SchwartzVelocityNormL2 (b : R3SchwartzVelocity) : R3L2RealScalar :=
  ((b.memLp 2 (volume : Measure R3)).norm).toLp (fun ξ : R3 => ‖b ξ‖)

/-- The scalar norm-field bundle represents the literal pointwise norm almost everywhere. -/
theorem coeFn_r3SchwartzScalarNormL2
    (a : R3SchwartzScalar) :
    (r3SchwartzScalarNormL2 a : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (fun ξ : R3 => ‖a ξ‖) := by
  exact ((a.memLp 2 (volume : Measure R3)).norm).coeFn_toLp

/-- The velocity norm-field bundle represents the literal pointwise norm almost everywhere. -/
theorem coeFn_r3SchwartzVelocityNormL2
    (b : R3SchwartzVelocity) :
    (r3SchwartzVelocityNormL2 b : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (fun ξ : R3 => ‖b ξ‖) := by
  exact ((b.memLp 2 (volume : Measure R3)).norm).coeFn_toLp

/-- Taking the pointwise norm does not change the `L²` norm of a scalar Schwartz field. -/
theorem norm_r3SchwartzScalarNormL2
    (a : R3SchwartzScalar) :
    ‖r3SchwartzScalarNormL2 a‖ =
      ‖a.toLp 2 (volume : Measure R3)‖ := by
  rw [r3SchwartzScalarNormL2, Lp.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_norm]

/-- Taking the pointwise norm does not change the `L²` norm of a velocity Schwartz field. -/
theorem norm_r3SchwartzVelocityNormL2
    (b : R3SchwartzVelocity) :
    ‖r3SchwartzVelocityNormL2 b‖ =
      ‖b.toLp 2 (volume : Measure R3)‖ := by
  rw [r3SchwartzVelocityNormL2, Lp.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_norm]

/-- The left additive-H² majorant has a canonical real `L² * L¹` Young candidate. -/
def r3H2LeftMajorantYoungL2
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) : R3L2RealScalar :=
  r3RealYoungL2L1Convolution
    (r3SchwartzScalarNormL2 (r3H2WeightedScalarSchwartz a))
    (fun ξ : R3 => ‖b ξ‖)

/-- The right additive-H² majorant has a canonical real `L¹ * L²` Young candidate. -/
def r3H2RightMajorantYoungL2
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) : R3L2RealScalar :=
  r3RealYoungL1L2Convolution
    (fun ξ : R3 => ‖a ξ‖)
    (r3SchwartzVelocityNormL2 (r3H2WeightedVelocitySchwartz b))

/-- Young bound for the bundled left majorant candidate. -/
theorem norm_r3H2LeftMajorantYoungL2_le
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    ‖r3H2LeftMajorantYoungL2 a b‖ ≤
      ‖(r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)‖ *
        (∫ ξ : R3, ‖b ξ‖) := by
  simpa [r3H2LeftMajorantYoungL2, norm_r3SchwartzScalarNormL2] using
    (norm_r3RealYoungL2L1Convolution_le
      (r3SchwartzScalarNormL2 (r3H2WeightedScalarSchwartz a))
      b.continuous.norm b.integrable.norm)

/-- Young bound for the bundled right majorant candidate. -/
theorem norm_r3H2RightMajorantYoungL2_le
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    ‖r3H2RightMajorantYoungL2 a b‖ ≤
      (∫ ξ : R3, ‖a ξ‖) *
        ‖(r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)‖ := by
  simpa [r3H2RightMajorantYoungL2, norm_r3SchwartzVelocityNormL2] using
    (norm_r3RealYoungL1L2Convolution_le
      a.continuous.norm a.integrable.norm
      (r3SchwartzVelocityNormL2 (r3H2WeightedVelocitySchwartz b)))

end

end MNS2
