import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Formal.R3H2AdditiveConvolutionWeight
import Formal.R3H2YoungWeightedBridge

namespace MNS2

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The inverse order-two Bessel weight, viewed as a complex scalar multiplier. -/
def r3H2InverseBesselWeightComplex (ξ : R3) : ℂ :=
  Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ))

/-- In dimension three, the inverse order-two Bessel weight belongs to `L²`. -/
theorem r3H2InverseBesselWeightComplex_memLp :
    MemLp r3H2InverseBesselWeightComplex 2 (volume : Measure R3) := by
  have hreal :
      MemLp (fun ξ : R3 => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) 2 (volume : Measure R3) := by
    have hg :
        (fun ξ : R3 => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
      fun_prop
    have hmeas :
        AEStronglyMeasurable
          (fun ξ : R3 => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ))
          (volume : Measure R3) :=
      hg.1.continuous.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    have hdim : (Module.finrank ℝ R3 : ℝ) < 4 := by
      norm_num [R3]
    refine (integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure R3)) hdim).congr ?_
    filter_upwards with ξ
    have hbase : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
    have hnegTwo :
        ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-2 : ℝ) =
          (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) ^ 2 := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_natCast (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) 2
    have hnegOne :
        ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-1 : ℝ) =
          ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num,
        Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
    rw [show (-(4 : ℝ) / 2) = (-2 : ℝ) by norm_num, hnegTwo, hnegOne]
  exact hreal.ofReal

/-- The inverse order-two Bessel weight bundled as an `L²` scalar field. -/
def r3H2InverseBesselWeightL2 : Lp ℂ 2 (volume : Measure R3) :=
  r3H2InverseBesselWeightComplex_memLp.toLp r3H2InverseBesselWeightComplex

/-- The bundled inverse Bessel weight agrees a.e. with its pointwise formula. -/
theorem r3H2InverseBesselWeightL2_ae :
    r3H2InverseBesselWeightL2 =ᵐ[volume]
      r3H2InverseBesselWeightComplex := by
  exact MemLp.coeFn_toLp r3H2InverseBesselWeightComplex_memLp

/-- The inverse order-two weight cancels the order-two Sobolev multiplier pointwise. -/
theorem r3H2InverseBesselWeightComplex_mul_weight_two (ξ : R3) :
    r3H2InverseBesselWeightComplex ξ * r3SobolevWeightComplex 2 ξ = 1 := by
  unfold r3H2InverseBesselWeightComplex r3SobolevWeightComplex
  have hbase : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  change Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) *
      Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 2)) = Complex.ofReal 1
  rw [← Complex.ofReal_mul]
  congr 1
  have htwo : (2 : ℝ) / 2 = 1 := by norm_num
  rw [htwo, Real.rpow_one]
  have hneg : (-1 : ℝ) = -(1 : ℝ) := by norm_num
  rw [hneg, Real.rpow_neg_eq_inv_rpow, Real.rpow_one, inv_mul_cancel₀ hbase.ne']

/-- Multiplying an order-two weighted scalar Schwartz field by the inverse weight recovers it. -/
theorem r3H2InverseBesselWeightComplex_smul_weightedScalar
    (a : R3SchwartzScalar) (ξ : R3) :
    r3H2InverseBesselWeightComplex ξ • r3H2WeightedScalarSchwartz a ξ = a ξ := by
  rw [r3H2WeightedScalarSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (r3SobolevWeightComplex_hasTemperateGrowth 2)]
  rw [smul_smul, r3H2InverseBesselWeightComplex_mul_weight_two]
  simp

/--
The `L¹` reconstruction obtained by multiplying the weighted scalar `L²` field by the inverse
Bessel weight in `L²`.  Hölder's `2 · 2 → 1` multiplication is provided directly by mathlib's
heterogeneous `Lp` scalar multiplication.
-/
def r3H2ScalarL1Reconstruction (a : R3SchwartzScalar) :
    Lp ℂ 1 (volume : Measure R3) :=
  r3H2InverseBesselWeightL2 •
    (r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)

/-- The `L¹` reconstruction agrees almost everywhere with the original scalar Schwartz field. -/
theorem r3H2ScalarL1Reconstruction_ae (a : R3SchwartzScalar) :
    r3H2ScalarL1Reconstruction a =ᵐ[volume] a := by
  unfold r3H2ScalarL1Reconstruction
  filter_upwards [
    r3H2InverseBesselWeightL2_ae,
    (r3H2WeightedScalarSchwartz a).coeFn_toLp 2 (volume : Measure R3),
    Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) r3H2InverseBesselWeightL2
      ((r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3))]
    with ξ hinv hweight hsmul
  rw [hsmul, Pi.smul_apply', hinv, hweight]
  exact r3H2InverseBesselWeightComplex_smul_weightedScalar a ξ

/-- Cauchy--Schwarz in `Lp` form for the inverse-weight reconstruction. -/
theorem norm_r3H2ScalarL1Reconstruction_le (a : R3SchwartzScalar) :
    ‖r3H2ScalarL1Reconstruction a‖ ≤
      ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)‖ := by
  unfold r3H2ScalarL1Reconstruction
  exact Lp.norm_smul_le _ _

/--
Quantitative three-dimensional Fourier `L¹` bound at Sobolev order two.

The constant is the fixed `L²` norm of the inverse order-two Bessel weight; no compactness or
nonconstructive Sobolev-embedding constant is introduced.
-/
theorem integral_norm_r3SchwartzScalar_le_H2WeightedL2
    (a : R3SchwartzScalar) :
    (∫ ξ : R3, ‖a ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)‖ := by
  have ha : Integrable (fun ξ : R3 => a ξ) := a.integrable
  have hL1 : ha.toL1 (fun ξ : R3 => a ξ) = r3H2ScalarL1Reconstruction a := by
    apply Lp.ext
    filter_upwards [ha.coeFn_toL1, r3H2ScalarL1Reconstruction_ae a] with ξ hleft hright
    rw [hleft, hright]
  calc
    (∫ ξ : R3, ‖a ξ‖) = ‖ha.toL1 (fun ξ : R3 => a ξ)‖ :=
      (L1.norm_of_fun_eq_integral_norm ha).symm
    _ = ‖r3H2ScalarL1Reconstruction a‖ := by rw [hL1]
    _ ≤ ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedScalarSchwartz a).toLp 2 (volume : Measure R3)‖ :=
      norm_r3H2ScalarL1Reconstruction_le a

end

end MNS2
