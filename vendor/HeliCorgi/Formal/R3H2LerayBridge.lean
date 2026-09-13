import Formal.R3H2FourierL1Bound
import Formal.R3LerayPointwiseProjectionIdentification

namespace MNS2

open MeasureTheory Filter FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

/-- The inverse order-two Bessel weight is continuous. -/
theorem continuous_r3H2InverseBesselWeightComplex :
    Continuous r3H2InverseBesselWeightComplex := by
  have hreal :
      (fun ξ : R3 => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
    fun_prop
  exact Complex.continuous_ofReal.comp hreal.1.continuous

/-- The inverse order-two Bessel weight is bounded by one. -/
theorem norm_r3H2InverseBesselWeightComplex_le_one (ξ : R3) :
    ‖r3H2InverseBesselWeightComplex ξ‖ ≤ 1 := by
  rw [r3H2InverseBesselWeightComplex, Complex.norm_real, Real.norm_eq_abs]
  have hbase : 1 ≤ (1 : ℝ) + ‖ξ‖ ^ 2 := by
    nlinarith [sq_nonneg ‖ξ‖]
  have hpow :
      ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-1 : ℝ) =
        ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num,
      Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
  rw [hpow, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact (inv_le_one₀ (by positivity)).2 hbase

/-- The inverse order-two Bessel weight has temperate growth. -/
theorem r3H2InverseBesselWeightComplex_hasTemperateGrowth :
    r3H2InverseBesselWeightComplex.HasTemperateGrowth := by
  unfold r3H2InverseBesselWeightComplex
  fun_prop

/-- The inverse order-two Bessel weight bundled as a bounded frequency multiplier. -/
theorem r3H2InverseBesselWeightComplex_memLp_top :
    MemLp r3H2InverseBesselWeightComplex ⊤ (volume : Measure R3) :=
  memLp_top_of_bound
    continuous_r3H2InverseBesselWeightComplex.aestronglyMeasurable
    1
    (ae_of_all _ norm_r3H2InverseBesselWeightComplex_le_one)

def r3H2InverseBesselWeightLpTop :
    Lp ℂ ⊤ (volume : Measure R3) :=
  r3H2InverseBesselWeightComplex_memLp_top.toLp
    r3H2InverseBesselWeightComplex

theorem r3H2InverseBesselWeightLpTop_ae :
    r3H2InverseBesselWeightLpTop =ᵐ[volume]
      r3H2InverseBesselWeightComplex := by
  exact MemLp.coeFn_toLp r3H2InverseBesselWeightComplex_memLp_top

/-- Multiplication by `J⁻²` on the Fourier-side `L²` coordinate. -/
def r3H2InverseBesselL2FrequencyOperator :
    R3L2Velocity →L[ℂ] R3L2Velocity :=
  r3L2ScalarMultiplier r3H2InverseBesselWeightLpTop

theorem r3H2InverseBesselL2FrequencyOperator_ae (g : R3L2Velocity) :
    r3H2InverseBesselL2FrequencyOperator g =ᵐ[volume]
      fun ξ => r3H2InverseBesselWeightComplex ξ • g ξ := by
  unfold r3H2InverseBesselL2FrequencyOperator
  rw [r3L2ScalarMultiplier_apply]
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) r3H2InverseBesselWeightLpTop g,
      r3H2InverseBesselWeightLpTop_ae]
    with ξ hmul hweight
  rw [hmul]
  exact congrArg (fun c : ℂ => c • g ξ) hweight

/--
Decode an order-two Bessel coordinate into the physical `L²` carrier by the actual bounded
Fourier multiplier `J⁻²`.  This is not a cast through the phantom Sobolev-order alias.
-/
def r3H2ToL2Operator : R3HsVelocity 2 →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3H2InverseBesselL2FrequencyOperator ∘L
      fourierCLM ℂ R3L2Velocity

theorem fourier_r3H2ToL2Operator (g : R3HsVelocity 2) :
    𝓕 (r3H2ToL2Operator g) =
      r3H2InverseBesselL2FrequencyOperator (𝓕 g) := by
  simp [r3H2ToL2Operator]

/-- The bounded `H²`-coordinate decoder agrees with the existing tempered-distribution decoder. -/
theorem r3L2ToTempered_r3H2ToL2Operator (g : R3HsVelocity 2) :
    r3L2ToTemperedCLM (r3H2ToL2Operator g) =
      r3HsToTemperedCLM 2 g := by
  symm
  have hinjective :
      Function.Injective (fun T : TemperedDistribution R3 R3C => 𝓕 T) :=
    Function.LeftInverse.injective (fun T : TemperedDistribution R3 R3C =>
      FourierTransform.fourierInv_fourier_eq T)
  apply hinjective
  change
    𝓕 (r3HsToTemperedCLM 2 g) =
      𝓕 (r3L2ToTemperedCLM (r3H2ToL2Operator g))
  rw [r3HsToTemperedCLM_apply,
    TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  change
    TemperedDistribution.smulLeftCLM R3C (r3SobolevWeightComplex (-2))
        (𝓕 (g : TemperedDistribution R3 R3C)) =
      𝓕 ((r3H2ToL2Operator g : R3L2Velocity) :
        TemperedDistribution R3 R3C)
  rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  change
    TemperedDistribution.smulLeftCLM R3C (r3SobolevWeightComplex (-2))
        ((𝓕 g : R3L2Velocity) : TemperedDistribution R3 R3C) =
      ((𝓕 (r3H2ToL2Operator g) : R3L2Velocity) :
        TemperedDistribution R3 R3C)
  rw [fourier_r3H2ToL2Operator]
  have hweight :
      r3SobolevWeightComplex (-2) = r3H2InverseBesselWeightComplex := by
    funext ξ
    unfold r3SobolevWeightComplex r3H2InverseBesselWeightComplex
    congr 1
    norm_num
  rw [hweight]
  symm
  exact MeasureTheory.Lp.toTemperedDistribution_smul_eq
    r3H2InverseBesselWeightComplex_hasTemperateGrowth
    r3H2InverseBesselWeightComplex_memLp_top (𝓕 g)

/-- Canonical order-two Schwartz coordinates decode to their literal physical `L²` field. -/
@[simp]
theorem r3H2ToL2Operator_r3SchwartzToHsCLM
    (f : R3SchwartzVelocity) :
    r3H2ToL2Operator (r3SchwartzToHsCLM 2 f) = f.toLp 2 := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change 𝓕 (r3H2ToL2Operator (r3SchwartzToHsCLM 2 f)) = 𝓕 (f.toLp 2)
  rw [fourier_r3H2ToL2Operator, r3SchwartzToHsCLM_apply,
    SchwartzMap.toLp_fourier_eq, fourier_r3SchwartzBesselCoordinate,
    SchwartzMap.toLp_fourier_eq]
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change r3H2InverseBesselWeightLpTop •
      (r3SchwartzSobolevFrequencyCoordinate 2 f).toLp 2 =
    (𝓕 f).toLp 2
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) r3H2InverseBesselWeightLpTop
      ((r3SchwartzSobolevFrequencyCoordinate 2 f).toLp 2),
      r3H2InverseBesselWeightLpTop_ae,
      (r3SchwartzSobolevFrequencyCoordinate 2 f).coeFn_toLp 2
        (volume : Measure R3),
      (𝓕 f).coeFn_toLp 2 (volume : Measure R3)]
    with ξ hmul hinv hweighted hfourier
  rw [hmul, Pi.smul_apply', hinv, hweighted, hfourier]
  unfold r3SchwartzSobolevFrequencyCoordinate
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_smul]
  change
    (r3H2InverseBesselWeightComplex ξ * r3SobolevWeightComplex 2 ξ) •
      (𝓕 f) ξ = (𝓕 f) ξ
  rw [r3H2InverseBesselWeightComplex_mul_weight_two, one_smul]

/-- The Leray projector acting specifically on the stored order-two Bessel coordinate. -/
def r3LerayH2Operator :
    R3HsVelocity 2 →L[ℂ] R3HsVelocity 2 :=
  r3LerayL2Operator

@[simp]
theorem r3LerayH2Operator_apply (g : R3HsVelocity 2) :
    r3LerayH2Operator g = r3LerayL2Operator g := by
  rfl

theorem r3LerayH2Operator_mem_solenoidal (g : R3HsVelocity 2) :
    r3LerayH2Operator g ∈ r3L2SolenoidalSubmodule := by
  exact r3LerayL2Operator_mem_solenoidal g

theorem r3LerayH2Operator_idempotent (g : R3HsVelocity 2) :
    r3LerayH2Operator (r3LerayH2Operator g) = r3LerayH2Operator g := by
  exact r3LerayL2Operator_idempotent g

theorem norm_r3LerayH2Operator_apply_le (g : R3HsVelocity 2) :
    ‖r3LerayH2Operator g‖ ≤ ‖g‖ := by
  exact norm_r3LerayL2Operator_apply_le g

theorem norm_r3LerayH2Operator_le_one :
    ‖r3LerayH2Operator‖ ≤ 1 :=
  norm_r3LerayL2Operator_le_one

/-- The inverse Bessel multiplier commutes with the pointwise frequency-side Leray projector. -/
theorem r3H2InverseBesselL2FrequencyOperator_commutes_leray
    (g : R3L2Velocity) :
    r3H2InverseBesselL2FrequencyOperator
        (r3LerayL2FrequencyOperator g) =
      r3LerayL2FrequencyOperator
        (r3H2InverseBesselL2FrequencyOperator g) := by
  apply Lp.ext
  filter_upwards
    [r3H2InverseBesselL2FrequencyOperator_ae
      (r3LerayL2FrequencyOperator g),
      r3LerayL2FrequencyOperator_ae g,
      r3LerayL2FrequencyOperator_ae
        (r3H2InverseBesselL2FrequencyOperator g),
      r3H2InverseBesselL2FrequencyOperator_ae g]
    with ξ hleft hleray hright hinverse
  rw [hleft, hleray, hright, hinverse]
  exact (r3LeraySymbolComplex ξ).map_smul
    (r3H2InverseBesselWeightComplex ξ) (g ξ) |>.symm

/-- Decoding an order-two coordinate commutes with the physical `L²` Leray projector. -/
theorem r3H2ToL2Operator_commutes_leray (g : R3HsVelocity 2) :
    r3H2ToL2Operator (r3LerayH2Operator g) =
      r3LerayL2Operator (r3H2ToL2Operator g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3H2ToL2Operator (r3LerayH2Operator g)) =
      𝓕 (r3LerayL2Operator (r3H2ToL2Operator g))
  rw [fourier_r3H2ToL2Operator, r3LerayH2Operator_apply,
    fourier_r3LerayL2Operator,
    fourier_r3LerayL2Operator, fourier_r3H2ToL2Operator]
  exact r3H2InverseBesselL2FrequencyOperator_commutes_leray (𝓕 g)

/-- The order-two decoder intertwines coordinate Leray with the literal physical `L²` projector. -/
theorem r3HsToTempered_r3LerayH2Operator (g : R3HsVelocity 2) :
    r3HsToTemperedCLM 2 (r3LerayH2Operator g) =
      r3L2ToTemperedCLM
        (r3LerayL2Operator (r3H2ToL2Operator g)) := by
  rw [← r3L2ToTempered_r3H2ToL2Operator,
    r3H2ToL2Operator_commutes_leray]

/-- On a canonical Schwartz coordinate, the decoded projection is the existing physical `L²` projection. -/
theorem r3HsToTempered_r3LerayH2Operator_schwartz
    (f : R3SchwartzVelocity) :
    r3HsToTemperedCLM 2
        (r3LerayH2Operator (r3SchwartzToHsCLM 2 f)) =
      r3L2ToTemperedCLM (r3LerayL2Operator (f.toLp 2)) := by
  rw [r3HsToTempered_r3LerayH2Operator,
    r3H2ToL2Operator_r3SchwartzToHsCLM]

end

end MNS2
