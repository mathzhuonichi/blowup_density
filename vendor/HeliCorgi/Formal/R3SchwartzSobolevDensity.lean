import Formal.R3SchwartzSobolevCore

namespace MNS2

open MeasureTheory
open scoped SchwartzMap

noncomputable section

/-- The Bessel multiplier of order `s` and the multiplier of order `-s` cancel pointwise. -/
theorem r3SobolevWeightComplex_mul_neg
    (s : ℝ) (ξ : R3) :
    r3SobolevWeightComplex s ξ * r3SobolevWeightComplex (-s) ξ = 1 := by
  unfold r3SobolevWeightComplex
  rw [← Complex.ofReal_mul]
  rw [← Real.rpow_add (by positivity)]
  have hexponent : s / 2 + -s / 2 = 0 := by ring
  rw [hexponent, Real.rpow_zero]
  simp

/-- The inverse-order Bessel multiplier is a right inverse on the Schwartz core. -/
theorem r3SchwartzBesselMultiplier_inverse_apply
    (s : ℝ) (f : R3SchwartzVelocity) :
    SchwartzMap.fourierMultiplierCLM R3C (r3SobolevWeightComplex s)
        (SchwartzMap.fourierMultiplierCLM R3C (r3SobolevWeightComplex (-s)) f) = f := by
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (r3SobolevWeightComplex_hasTemperateGrowth s)
    (r3SobolevWeightComplex_hasTemperateGrowth (-s))]
  have hweight :
      r3SobolevWeightComplex s * r3SobolevWeightComplex (-s) =
        (fun _ : R3 => (1 : ℂ)) := by
    funext ξ
    exact r3SobolevWeightComplex_mul_neg s ξ
  rw [hweight, SchwartzMap.fourierMultiplierCLM_const]
  simp

/-- Multiplication by the order-`s` Bessel weight is onto on Schwartz fields. -/
theorem r3SchwartzBesselMultiplier_surjective (s : ℝ) :
    Function.Surjective
      (SchwartzMap.fourierMultiplierCLM R3C (r3SobolevWeightComplex s)) := by
  intro f
  exact ⟨SchwartzMap.fourierMultiplierCLM R3C (r3SobolevWeightComplex (-s)) f,
    r3SchwartzBesselMultiplier_inverse_apply s f⟩

/-- Canonical Schwartz coordinates are dense in every Bessel-coordinate Sobolev carrier. -/
theorem r3SchwartzToHsCLM_denseRange (s : ℝ) :
    DenseRange (r3SchwartzToHsCLM s) := by
  unfold r3SchwartzToHsCLM
  have hToLp : DenseRange
      (SchwartzMap.toLpCLM ℂ R3C 2 (volume : Measure R3)) := by
    exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  exact hToLp.comp
    (r3SchwartzBesselMultiplier_surjective s).denseRange
    (SchwartzMap.toLpCLM ℂ R3C 2 (volume : Measure R3)).continuous

end

end MNS2
