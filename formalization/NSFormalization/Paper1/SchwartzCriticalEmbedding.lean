import NSFormalization.Source.FractionalRepresentative
import NSFormalization.Source.FractionalRealization
import NSFormalization.Paper3.CompactSobolevRealization

/-!
# Whole-space critical estimate on Schwartz fields

This module records the genuine Riesz-potential route at order `a = 1/2`.
The input datum is the weighted Fourier `L²` datum, the singular multiplier
identity is used to identify the physical field, and the existing `L² → L³`
potential bound supplies the norm estimate.  No periodic or finite-mode claim
is made here.
-/

noncomputable section
namespace NSFormalization.Paper1.SchwartzCriticalEmbedding

open Set MeasureTheory FourierTransform
open NSFormalization
open NSFormalization.Paper3
open NSFormalization.Source
open NSFormalization.Source.BesselFractionalData
open NSFormalization.Source.FractionalRepresentative
open NSFormalization.Source.FractionalRealization
open NSFormalization.RieszPotentialLp NSFormalization.RieszPotentialOperator
open NSFormalization.RieszComplexPotential NSFormalization.RieszL2Fourier
open scoped ENNReal SchwartzMap ContDiff

local notation "X" => EuclideanSpace ℝ (Fin 3)

abbrev criticalOrder : ℝ := (1 / 2 : ℝ)

private theorem criticalOrder_pos : 0 < criticalOrder := by norm_num
private theorem criticalOrder_lt : criticalOrder < 3 / 2 := by norm_num

/-- The homogeneous derivative datum obtained from the inhomogeneous weighted
Fourier datum. -/
def criticalDatum (φ : SchwartzMap X ℂ) : Lp ℂ 2 (volume : Measure X) :=
  datum criticalOrder (by norm_num) (weightedFourierLp criticalOrder φ)

/-- The `L²` physical input whose Fourier transform is the critical
fractional derivative datum. -/
def criticalInput (φ : SchwartzMap X ℂ) : Lp ℂ 2 (volume : Measure X) :=
  𝓕⁻ (criticalDatum φ)

/-- Fourier transform of the critical physical input. -/
theorem fourier_criticalInput (φ : SchwartzMap X ℂ) :
    𝓕 (criticalInput φ) = criticalDatum φ := by
  exact FourierInvPair.fourier_fourierInv_eq _

/-- The actual unnormalized Riesz potential of the critical physical input. -/
def criticalPotential (φ : SchwartzMap X ℂ) : X → ℂ :=
  complexPotential criticalOrder (criticalInput φ)

/-- The potential has the expected `L³` bound in terms of its actual
fractional derivative datum. -/
theorem criticalPotential_eLpNorm_le (φ : SchwartzMap X ℂ) :
    eLpNorm (criticalPotential φ) 3 volume ≤
      ENNReal.ofReal (potentialConstant criticalOrder *
        (512 : ℝ) ^ (1 / targetExponent criticalOrder) *
        ‖criticalDatum φ‖) := by
  have hinput : MemLp (criticalInput φ) 2 volume := Lp.memLp _
  have hbound := eLpNorm_complexPotential_le criticalOrder_pos criticalOrder_lt hinput
  have hnorm : ‖criticalInput φ‖ = ‖criticalDatum φ‖ := by
    rw [← Lp.norm_fourier_eq (criticalInput φ), fourier_criticalInput]
  have hnorm' : (eLpNorm (criticalInput φ : X → ℂ) 2 volume).toReal =
      ‖criticalInput φ‖ := by
    rfl
  convert hbound using 1 <;> norm_num [criticalPotential, criticalOrder, targetExponent, hnorm, hnorm']

/-- The datum contraction gives the same estimate in the original weighted
Fourier Sobolev norm. -/
theorem criticalPotential_eLpNorm_le_weighted (φ : SchwartzMap X ℂ) :
    eLpNorm (criticalPotential φ) 3 volume ≤
      ENNReal.ofReal (potentialConstant criticalOrder *
        (512 : ℝ) ^ (1 / targetExponent criticalOrder) *
        ‖weightedFourierLp criticalOrder φ‖) := by
  have h := criticalPotential_eLpNorm_le φ
  have hdatum : ‖criticalDatum φ‖ ≤ ‖weightedFourierLp criticalOrder φ‖ := by
    exact datum_norm_le criticalOrder (by norm_num) _
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ potentialConstant criticalOrder *
      (512 : ℝ) ^ (1 / targetExponent criticalOrder) := by
    exact mul_nonneg (by unfold potentialConstant; positivity)
      (Real.rpow_nonneg (by norm_num) _)
  exact mul_le_mul_of_nonneg_left hdatum hc

/- The pointwise potential estimate controls an actual `Lp` representative.
This is the representative needed when passing to tempered distributions. -/
def criticalPotentialLp (φ : SchwartzMap X ℂ) :
    Lp ℂ (ENNReal.ofReal (targetExponent criticalOrder)) (volume : Measure X) :=
  (complexPotential_memLp criticalOrder_pos criticalOrder_lt
    (Lp.memLp (criticalInput φ))).toLp (criticalPotential φ)

theorem criticalPotentialLp_eq_potentialOperator (φ : SchwartzMap X ℂ) :
    criticalPotentialLp φ =
      potentialOperator criticalOrder_pos criticalOrder_lt (criticalInput φ) := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (potentialOperator_coe_ae criticalOrder_pos criticalOrder_lt (criticalInput φ)).symm

/-- The critical potential is the original Schwartz field after the proved
Fourier-kernel normalization.  This is the physical-field bridge needed to
use the `L³` estimate for the field itself. -/
theorem normalizedCriticalPotential_toDistribution (φ : SchwartzMap X ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
      ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
    (RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹ •
        (criticalPotentialLp φ : 𝓢'(X, ℂ)) = (φ : 𝓢'(X, ℂ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
    ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
  change (RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹ •
      (potentialOperator criticalOrder_pos criticalOrder_lt
        (physicalInput criticalOrder criticalOrder_pos.le
          (weightedFourierLp criticalOrder φ)) : 𝓢'(X, ℂ)) = _
  have hp :
      (potentialOperator criticalOrder_pos criticalOrder_lt (criticalInput φ) : 𝓢'(X, ℂ)) =
        (RieszFourierProfilePower.constant criticalOrder : ℂ) •
          sobolevRealization criticalOrder (weightedFourierLp criticalOrder φ) := by
    simpa [criticalInput, criticalDatum, physicalInput] using
      (potential_toDistribution criticalOrder_pos criticalOrder_lt
        (weightedFourierLp criticalOrder φ))
  rw [show physicalInput criticalOrder criticalOrder_pos.le
      (weightedFourierLp criticalOrder φ) = criticalInput φ by rfl, hp]
  have hc : (RieszFourierProfilePower.constant criticalOrder : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (kernelConstant_pos criticalOrder_pos criticalOrder_lt).ne'
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul,
    sobolevRealization_weightedFourierLp]

theorem criticalPotential_toDistribution (φ : SchwartzMap X ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
      ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
    (criticalPotentialLp φ : 𝓢'(X, ℂ)) =
      (RieszFourierProfilePower.constant criticalOrder : ℂ) • (φ : 𝓢'(X, ℂ)) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
    ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
  calc
    (criticalPotentialLp φ : 𝓢'(X, ℂ)) =
        (potentialOperator criticalOrder_pos criticalOrder_lt (criticalInput φ) : 𝓢'(X, ℂ)) := by
      rw [criticalPotentialLp_eq_potentialOperator]
    _ = (RieszFourierProfilePower.constant criticalOrder : ℂ) •
        sobolevRealization criticalOrder (weightedFourierLp criticalOrder φ) := by
      exact potential_toDistribution criticalOrder_pos criticalOrder_lt _
    _ = (RieszFourierProfilePower.constant criticalOrder : ℂ) • (φ : 𝓢'(X, ℂ)) := by
      rw [sobolevRealization_weightedFourierLp]

/- The distributional identification also determines the `L³` representative.
This is the final bridge from the potential estimate to the original physical
Schwartz field. -/
theorem normalizedCriticalPotential_toLp (φ : SchwartzMap X ℂ) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
      ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
    (RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹ •
        criticalPotentialLp φ = φ.toLp (ENNReal.ofReal (targetExponent criticalOrder)) volume := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
    ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
  have hi : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure X)
        (ENNReal.ofReal (targetExponent criticalOrder))) :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  apply hi
  rw [map_smul]
  change (RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹ •
      (criticalPotentialLp φ : 𝓢'(X, ℂ)) =
      (φ.toLp (ENNReal.ofReal (targetExponent criticalOrder)) volume : 𝓢'(X, ℂ))
  rw [normalizedCriticalPotential_toDistribution]
  exact (Lp.toTemperedDistribution_toLp_eq
    (p := ENNReal.ofReal (targetExponent criticalOrder)) (μ := volume) φ).symm

theorem criticalFieldLp_norm_le_datum (φ : SchwartzMap X ℂ) :
    ‖φ.toLp (ENNReal.ofReal (targetExponent criticalOrder)) volume‖ ≤
      ‖(RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹‖ *
        ((potentialConstant criticalOrder * (512 : ℝ) ^
          (1 / targetExponent criticalOrder)) * ‖criticalDatum φ‖) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent criticalOrder)) :=
    ⟨targetExponent_one_le criticalOrder_pos criticalOrder_lt⟩
  rw [← normalizedCriticalPotential_toLp φ, norm_smul,
    criticalPotentialLp_eq_potentialOperator]
  calc
    ‖(RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹‖ *
        ‖potentialOperator criticalOrder_pos criticalOrder_lt (criticalInput φ)‖ ≤
      ‖(RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹‖ *
        ((potentialConstant criticalOrder * (512 : ℝ) ^
          (1 / targetExponent criticalOrder)) * ‖criticalInput φ‖) := by
      exact mul_le_mul_of_nonneg_left
        (potentialOperator_norm_le criticalOrder_pos criticalOrder_lt _)
        (norm_nonneg _)
    _ = ‖(RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹‖ *
        ((potentialConstant criticalOrder * (512 : ℝ) ^
          (1 / targetExponent criticalOrder)) * ‖criticalDatum φ‖) := by
      rw [show ‖criticalInput φ‖ = ‖criticalDatum φ‖ by
        rw [← Lp.norm_fourier_eq (criticalInput φ), fourier_criticalInput]]

theorem criticalFieldLp_norm_le_weighted (φ : SchwartzMap X ℂ) :
    ‖φ.toLp (ENNReal.ofReal (targetExponent criticalOrder)) volume‖ ≤
      ‖(RieszFourierProfilePower.constant criticalOrder : ℂ)⁻¹‖ *
        ((potentialConstant criticalOrder * (512 : ℝ) ^
          (1 / targetExponent criticalOrder)) *
          ‖weightedFourierLp criticalOrder φ‖) := by
  have h := criticalFieldLp_norm_le_datum φ
  have hd := datum_norm_le criticalOrder (by norm_num)
    (weightedFourierLp criticalOrder φ)
  apply h.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd
      (by unfold potentialConstant; positivity)) (norm_nonneg _)

end NSFormalization.Paper1.SchwartzCriticalEmbedding
