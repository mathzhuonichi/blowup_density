import Formal.R3SchwartzConvectionScalarMajorants
import Formal.R3SchwartzNormFieldL2
import Formal.R3YoungRealConvolutionCommutativity

namespace MNS2

open MeasureTheory

noncomputable section

/--
The bundled right Young candidate has the ordinary right scalar majorant as an almost-everywhere
representative.
-/
theorem coeFn_r3H2RightMajorantYoungL2_eq_scalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    (r3H2RightMajorantYoungL2 a b : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      r3H2RightScalarMajorant a b := by
  have hbound :
      ∀ ξ : R3,
        ‖(‖r3H2WeightedVelocitySchwartz b ξ‖ : ℝ)‖ ≤
          SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedVelocitySchwartz b) := by
    intro ξ
    simpa [Real.norm_of_nonneg (norm_nonneg (r3H2WeightedVelocitySchwartz b ξ))] using
      (SchwartzMap.norm_le_seminorm ℝ (r3H2WeightedVelocitySchwartz b) ξ)
  have h :=
    coeFn_r3RealYoungL1L2Convolution_eq_convolution_of_ae_of_bound
      (f := fun ξ : R3 => ‖a ξ‖)
      a.continuous.norm a.integrable.norm
      (g := r3SchwartzVelocityNormL2 (r3H2WeightedVelocitySchwartz b))
      (g₀ := fun ξ : R3 => ‖r3H2WeightedVelocitySchwartz b ξ‖)
      (coeFn_r3SchwartzVelocityNormL2 (r3H2WeightedVelocitySchwartz b))
      (r3H2WeightedVelocitySchwartz b).continuous.norm
      (SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedVelocitySchwartz b)) hbound
  change
    (r3RealYoungL1L2Convolution
        (fun ξ : R3 => ‖a ξ‖)
        (r3SchwartzVelocityNormL2 (r3H2WeightedVelocitySchwartz b)) : R3 → ℝ) =ᵐ[
      (volume : Measure R3)] r3H2RightScalarMajorant a b
  exact h.trans <| Filter.Eventually.of_forall fun ξ =>
    (r3H2RightScalarMajorant_eq_convolution a b ξ).symm

/--
The bundled left Young candidate has the ordinary left scalar majorant as an almost-everywhere
representative.  Its Bochner implementation integrates the `L¹` factor first, so the final step
uses commutativity of real scalar convolution.
-/
theorem coeFn_r3H2LeftMajorantYoungL2_eq_scalarMajorant
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) :
    (r3H2LeftMajorantYoungL2 a b : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      r3H2LeftScalarMajorant a b := by
  have hbound :
      ∀ ξ : R3,
        ‖(‖r3H2WeightedScalarSchwartz a ξ‖ : ℝ)‖ ≤
          SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedScalarSchwartz a) := by
    intro ξ
    simpa [Real.norm_of_nonneg (norm_nonneg (r3H2WeightedScalarSchwartz a ξ))] using
      (SchwartzMap.norm_le_seminorm ℝ (r3H2WeightedScalarSchwartz a) ξ)
  have h :=
    coeFn_r3RealYoungL1L2Convolution_eq_convolution_of_ae_of_bound
      (f := fun ξ : R3 => ‖b ξ‖)
      b.continuous.norm b.integrable.norm
      (g := r3SchwartzScalarNormL2 (r3H2WeightedScalarSchwartz a))
      (g₀ := fun ξ : R3 => ‖r3H2WeightedScalarSchwartz a ξ‖)
      (coeFn_r3SchwartzScalarNormL2 (r3H2WeightedScalarSchwartz a))
      (r3H2WeightedScalarSchwartz a).continuous.norm
      (SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedScalarSchwartz a)) hbound
  change
    (r3RealYoungL1L2Convolution
        (fun ξ : R3 => ‖b ξ‖)
        (r3SchwartzScalarNormL2 (r3H2WeightedScalarSchwartz a)) : R3 → ℝ) =ᵐ[
      (volume : Measure R3)] r3H2LeftScalarMajorant a b
  refine h.trans <| Filter.Eventually.of_forall fun ξ => ?_
  exact
    (r3RealScalarConvolution_comm
        (fun η : R3 => ‖b η‖)
        (fun η : R3 => ‖r3H2WeightedScalarSchwartz a η‖) ξ).trans
      (r3H2LeftScalarMajorant_eq_convolution a b ξ).symm

end

end MNS2
