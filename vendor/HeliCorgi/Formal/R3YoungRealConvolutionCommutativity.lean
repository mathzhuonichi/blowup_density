import Formal.R3YoungRealSetIntegralBridge

namespace MNS2

open MeasureTheory

noncomputable section

/--
Ordinary real scalar convolution on `R³` is commutative for the multiplication bilinear map.
No integrability hypothesis is needed because this is only a change-of-variables identity for the
Bochner integral convention already used by `MeasureTheory.convolution`.
-/
theorem r3RealScalarConvolution_comm
    (f g : R3 → ℝ) (x : R3) :
    MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ)
        (volume : Measure R3) x =
      MeasureTheory.convolution g f (ContinuousLinearMap.mul ℝ ℝ)
        (volume : Measure R3) x := by
  calc
    MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ)
        (volume : Measure R3) x =
        ∫ y : R3, f (x - y) * g y := by
      simpa [ContinuousLinearMap.mul_apply'] using
        (MeasureTheory.convolution_eq_swap
          (L := ContinuousLinearMap.mul ℝ ℝ)
          (f := f) (g := g) (μ := (volume : Measure R3)) (x := x))
    _ = ∫ y : R3, g y * f (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [mul_comm]
    _ = MeasureTheory.convolution g f (ContinuousLinearMap.mul ℝ ℝ)
        (volume : Measure R3) x := by
      rfl

end

end MNS2
