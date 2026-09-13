import Formal.R3H2LerayBridge
import Formal.R3StokesSolenoidalPreservation
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq

namespace MNS2

open MeasureTheory Filter FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

/-- The positive frequency scale in the one-derivative Stokes smoothing estimate. -/
def r3StokesH2H3SmoothingScale (nu tau : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 * nu * tau

/--
An explicit upper bound for the `H^2`-to-`H^3` Stokes smoothing norm.

For positive viscosity and positive elapsed time it is of order
`1 + (nu * tau)^(-1/2)`.  This definition is only a numerical majorant; the smoothing
operator itself below still requires proofs that both parameters are strictly positive.
-/
def r3StokesH2H3TimeKernel (nu tau : ℝ) : ℝ :=
  1 + (Real.sqrt (r3StokesH2H3SmoothingScale nu tau))⁻¹

/--
The stored-coordinate frequency multiplier for one derivative of Stokes smoothing.

An order-two coordinate is `J^2 u`; multiplying by `J exp(tau * nu * Delta)` produces
the order-three coordinate `J^3 exp(tau * nu * Delta) u`.
-/
def r3StokesH2ToH3ScalarComplex (nu tau : ℝ) (xi : R3) : ℂ :=
  r3SobolevWeightComplex 1 xi * r3StokesScalarComplex nu tau xi

theorem r3StokesH2H3SmoothingScale_pos
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    0 < r3StokesH2H3SmoothingScale nu tau := by
  unfold r3StokesH2H3SmoothingScale
  positivity

theorem norm_r3SobolevWeightComplex_one (xi : R3) :
    ‖r3SobolevWeightComplex 1 xi‖ = Real.sqrt (1 + ‖xi‖ ^ 2) := by
  unfold r3SobolevWeightComplex
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _), Real.sqrt_eq_rpow]

theorem r3StokesScalar_eq_smoothingScale
    (nu tau : ℝ) (xi : R3) :
    r3StokesScalar nu tau xi =
      Real.exp (-(r3StokesH2H3SmoothingScale nu tau * ‖xi‖ * ‖xi‖)) := by
  unfold r3StokesScalar r3StokesDecayRate r3StokesH2H3SmoothingScale
  congr 2
  ring

theorem norm_mul_r3StokesScalar_le_inv_sqrt
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (xi : R3) :
    ‖xi‖ * r3StokesScalar nu tau xi ≤
      (Real.sqrt (r3StokesH2H3SmoothingScale nu tau))⁻¹ := by
  rw [r3StokesScalar_eq_smoothingScale]
  have h := Real.abs_mulExpNegMulSq_le
    (r3StokesH2H3SmoothingScale_pos hnu htau) (x := ‖xi‖)
  rw [Real.mulExpNegMulSq, abs_of_nonneg] at h
  · exact h
  · positivity

/-- The one-derivative Stokes multiplier has the explicit positive-time bound. -/
theorem norm_r3StokesH2ToH3ScalarComplex_le
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (xi : R3) :
    ‖r3StokesH2ToH3ScalarComplex nu tau xi‖ ≤
      r3StokesH2H3TimeKernel nu tau := by
  rw [r3StokesH2ToH3ScalarComplex, norm_mul,
    norm_r3SobolevWeightComplex_one,
    r3StokesScalarComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (r3StokesScalar_pos nu tau xi)]
  calc
    Real.sqrt (1 + ‖xi‖ ^ 2) * r3StokesScalar nu tau xi ≤
        (1 + ‖xi‖) * r3StokesScalar nu tau xi := by
      exact mul_le_mul_of_nonneg_right (sqrt_one_add_norm_sq_le xi)
        (r3StokesScalar_pos nu tau xi).le
    _ = r3StokesScalar nu tau xi + ‖xi‖ * r3StokesScalar nu tau xi := by ring
    _ ≤ 1 + (Real.sqrt (r3StokesH2H3SmoothingScale nu tau))⁻¹ := by
      gcongr
      · exact r3StokesScalar_le_one hnu.le htau.le xi
      · exact norm_mul_r3StokesScalar_le_inv_sqrt hnu htau xi

theorem continuous_r3StokesH2ToH3ScalarComplex (nu tau : ℝ) :
    Continuous (r3StokesH2ToH3ScalarComplex nu tau) := by
  exact (r3SobolevWeightComplex_hasTemperateGrowth 1).1.continuous.mul
    (continuous_r3StokesScalarComplex nu tau)

theorem r3StokesH2H3TimeKernel_nonneg
    {nu tau : ℝ} (_hnu : 0 < nu) (_htau : 0 < tau) :
    0 ≤ r3StokesH2H3TimeKernel nu tau := by
  unfold r3StokesH2H3TimeKernel
  positivity

theorem r3StokesH2ToH3ScalarComplex_memLp_top
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    MemLp (r3StokesH2ToH3ScalarComplex nu tau) ⊤
      (volume : Measure R3) :=
  memLp_top_of_bound
    (continuous_r3StokesH2ToH3ScalarComplex nu tau).aestronglyMeasurable
    (r3StokesH2H3TimeKernel nu tau)
    (ae_of_all _ (norm_r3StokesH2ToH3ScalarComplex_le hnu htau))

/-- The positive-time smoothing coefficient bundled as an `L-infinity` multiplier. -/
def r3StokesH2ToH3ScalarLpTop
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    Lp ℂ ⊤ (volume : Measure R3) :=
  (r3StokesH2ToH3ScalarComplex_memLp_top hnu htau).toLp
    (r3StokesH2ToH3ScalarComplex nu tau)

theorem r3StokesH2ToH3ScalarLpTop_ae
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    r3StokesH2ToH3ScalarLpTop hnu htau =ᵐ[volume]
      r3StokesH2ToH3ScalarComplex nu tau := by
  exact MemLp.coeFn_toLp
    (r3StokesH2ToH3ScalarComplex_memLp_top hnu htau)

theorem norm_r3StokesH2ToH3ScalarLpTop_le
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    ‖r3StokesH2ToH3ScalarLpTop hnu htau‖ ≤
      r3StokesH2H3TimeKernel nu tau := by
  unfold r3StokesH2ToH3ScalarLpTop
  rw [Lp.norm_toLp, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal
    (r3StokesH2H3TimeKernel_nonneg hnu htau)
    (eLpNormEssSup_le_of_ae_bound
      (ae_of_all _ (norm_r3StokesH2ToH3ScalarComplex_le hnu htau)))

/-- Multiplication by the smoothing coefficient on the stored Fourier coordinate. -/
def r3StokesH2ToH3FrequencyOperator
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    R3HsVelocity 2 →L[ℂ] R3HsVelocity 3 :=
  r3L2ScalarMultiplier (r3StokesH2ToH3ScalarLpTop hnu htau)

theorem r3StokesH2ToH3FrequencyOperator_ae
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    r3StokesH2ToH3FrequencyOperator hnu htau g =ᵐ[volume]
      fun xi => r3StokesH2ToH3ScalarComplex nu tau xi • g xi := by
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change
    ((r3StokesH2ToH3ScalarLpTop hnu htau • g : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun xi => r3StokesH2ToH3ScalarComplex nu tau xi • g xi
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ENNReal))
      (r3StokesH2ToH3ScalarLpTop hnu htau) g,
      r3StokesH2ToH3ScalarLpTop_ae hnu htau]
    with xi hmul hscalar
  rw [hmul, Pi.smul_apply', hscalar]

/--
The genuine positive-time Stokes smoothing map from order-two to order-three coordinates.

Although both carrier aliases have underlying type `L^2`, this map is not an identity/retyping:
its Fourier multiplier is explicitly `J exp(tau * nu * Delta)`.
-/
def r3StokesH2ToH3Operator
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    R3HsVelocity 2 →L[ℂ] R3HsVelocity 3 :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3StokesH2ToH3FrequencyOperator hnu htau ∘L
      fourierCLM ℂ R3L2Velocity

theorem fourier_r3StokesH2ToH3Operator
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    𝓕 (r3StokesH2ToH3Operator hnu htau g) =
      r3StokesH2ToH3FrequencyOperator hnu htau (𝓕 g) := by
  simp [r3StokesH2ToH3Operator]

/-- The smoothing map satisfies the explicit one-derivative pointwise norm bound. -/
theorem norm_r3StokesH2ToH3Operator_apply_le
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    ‖r3StokesH2ToH3Operator hnu htau g‖ ≤
      r3StokesH2H3TimeKernel nu tau * ‖g‖ := by
  calc
    ‖r3StokesH2ToH3Operator hnu htau g‖ =
        ‖𝓕 (r3StokesH2ToH3Operator hnu htau g)‖ := by
      symm
      exact Lp.norm_fourier_eq _
    _ = ‖r3StokesH2ToH3FrequencyOperator hnu htau (𝓕 g)‖ := by
      rw [fourier_r3StokesH2ToH3Operator]
    _ ≤ ‖r3StokesH2ToH3ScalarLpTop hnu htau‖ * ‖𝓕 g‖ := by
      exact Lp.norm_smul_le _ _
    _ ≤ r3StokesH2H3TimeKernel nu tau * ‖𝓕 g‖ := by
      gcongr
      exact norm_r3StokesH2ToH3ScalarLpTop_le hnu htau
    _ = r3StokesH2H3TimeKernel nu tau * ‖g‖ := by
      rw [Lp.norm_fourier_eq]

/-- The bundled smoothing operator has the same explicit operator-norm bound. -/
theorem norm_r3StokesH2ToH3Operator_le
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) :
    ‖r3StokesH2ToH3Operator hnu htau‖ ≤
      r3StokesH2H3TimeKernel nu tau := by
  exact (r3StokesH2ToH3Operator hnu htau).opNorm_le_bound
    (r3StokesH2H3TimeKernel_nonneg hnu htau)
    (norm_r3StokesH2ToH3Operator_apply_le hnu htau)

/-- The explicit `1 + O(tau^(-1/2))` smoothing majorant is locally time-integrable. -/
theorem intervalIntegrable_r3StokesH2H3TimeKernel
    {nu T : ℝ} (hnu : 0 < nu) (hT : 0 ≤ T) :
    IntervalIntegrable (r3StokesH2H3TimeKernel nu) volume 0 T := by
  let c : ℝ := (2 * Real.pi) ^ 2 * nu
  have hc : 0 < c := mul_pos (sq_pos_of_pos (by positivity)) hnu
  have hsqrt :
      IntervalIntegrable (fun t : ℝ => (Real.sqrt t)⁻¹) volume 0 T := by
    have hrpow :
        IntervalIntegrable (fun t : ℝ => t ^ (-1 / 2 : ℝ)) volume 0 T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine hrpow.congr ?_
    intro t htmem
    have ht0 : 0 ≤ t := by
      rw [Set.uIoc_of_le hT] at htmem
      exact htmem.1.le
    change t ^ (-1 / 2 : ℝ) = (Real.sqrt t)⁻¹
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg ht0, Real.sqrt_eq_rpow]
  have hbase :
      IntervalIntegrable
        (fun t : ℝ => 1 + (Real.sqrt c)⁻¹ * (Real.sqrt t)⁻¹)
        volume 0 T :=
    intervalIntegrable_const.add (hsqrt.const_mul (Real.sqrt c)⁻¹)
  refine hbase.congr ?_
  intro t htmem
  have ht0 : 0 ≤ t := by
    rw [Set.uIoc_of_le hT] at htmem
    exact htmem.1.le
  change
    1 + (Real.sqrt c)⁻¹ * (Real.sqrt t)⁻¹ =
      r3StokesH2H3TimeKernel nu t
  unfold r3StokesH2H3TimeKernel r3StokesH2H3SmoothingScale
  change 1 + (Real.sqrt c)⁻¹ * (Real.sqrt t)⁻¹ =
    1 + (Real.sqrt (c * t))⁻¹
  rw [Real.sqrt_mul hc.le t, mul_inv]

/-- The inverse order-three Bessel weight used to reconstruct a physical `L^2` field. -/
def r3H3InverseBesselWeightComplex (xi : R3) : ℂ :=
  r3SobolevWeightComplex (-3) xi

theorem continuous_r3H3InverseBesselWeightComplex :
    Continuous r3H3InverseBesselWeightComplex := by
  exact (r3SobolevWeightComplex_hasTemperateGrowth (-3)).1.continuous

theorem norm_r3H3InverseBesselWeightComplex_le_one (xi : R3) :
    ‖r3H3InverseBesselWeightComplex xi‖ ≤ 1 := by
  unfold r3H3InverseBesselWeightComplex r3SobolevWeightComplex
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [sq_nonneg ‖xi‖]
  · norm_num

theorem r3H3InverseBesselWeightComplex_memLp_top :
    MemLp r3H3InverseBesselWeightComplex ⊤ (volume : Measure R3) :=
  memLp_top_of_bound
    continuous_r3H3InverseBesselWeightComplex.aestronglyMeasurable
    1 (ae_of_all _ norm_r3H3InverseBesselWeightComplex_le_one)

def r3H3InverseBesselWeightLpTop :
    Lp ℂ ⊤ (volume : Measure R3) :=
  r3H3InverseBesselWeightComplex_memLp_top.toLp
    r3H3InverseBesselWeightComplex

theorem r3H3InverseBesselWeightLpTop_ae :
    r3H3InverseBesselWeightLpTop =ᵐ[volume]
      r3H3InverseBesselWeightComplex := by
  exact MemLp.coeFn_toLp r3H3InverseBesselWeightComplex_memLp_top

/-- Multiplication by `J^-3` on the Fourier-side order-three coordinate. -/
def r3H3InverseBesselL2FrequencyOperator :
    R3L2Velocity →L[ℂ] R3L2Velocity :=
  r3L2ScalarMultiplier r3H3InverseBesselWeightLpTop

theorem r3H3InverseBesselL2FrequencyOperator_ae (g : R3L2Velocity) :
    r3H3InverseBesselL2FrequencyOperator g =ᵐ[volume]
      fun xi => r3H3InverseBesselWeightComplex xi • g xi := by
  unfold r3H3InverseBesselL2FrequencyOperator
  rw [r3L2ScalarMultiplier_apply]
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) r3H3InverseBesselWeightLpTop g,
      r3H3InverseBesselWeightLpTop_ae]
    with xi hmul hweight
  rw [hmul]
  exact congrArg (fun z : ℂ => z • g xi) hweight

/--
Decode an order-three coordinate into physical `L^2` by the genuine bounded multiplier `J^-3`.
This supplies order-aware semantics rather than relying on the phantom carrier alias.
-/
def r3H3ToL2Operator : R3HsVelocity 3 →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3H3InverseBesselL2FrequencyOperator ∘L
      fourierCLM ℂ R3L2Velocity

theorem fourier_r3H3ToL2Operator (g : R3HsVelocity 3) :
    𝓕 (r3H3ToL2Operator g) =
      r3H3InverseBesselL2FrequencyOperator (𝓕 g) := by
  simp [r3H3ToL2Operator]

/-- The bounded order-three reconstruction is exactly the existing tempered decoder. -/
theorem r3L2ToTempered_r3H3ToL2Operator (g : R3HsVelocity 3) :
    r3L2ToTemperedCLM (r3H3ToL2Operator g) =
      r3HsToTemperedCLM 3 g := by
  symm
  have hinjective :
      Function.Injective (fun S : TemperedDistribution R3 R3C => 𝓕 S) :=
    Function.LeftInverse.injective (fun S : TemperedDistribution R3 R3C =>
      FourierTransform.fourierInv_fourier_eq S)
  apply hinjective
  change
    𝓕 (r3HsToTemperedCLM 3 g) =
      𝓕 (r3L2ToTemperedCLM (r3H3ToL2Operator g))
  rw [r3HsToTemperedCLM_apply,
    TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply]
  change
    TemperedDistribution.smulLeftCLM R3C (r3SobolevWeightComplex (-3))
        (𝓕 (g : TemperedDistribution R3 R3C)) =
      𝓕 ((r3H3ToL2Operator g : R3L2Velocity) :
        TemperedDistribution R3 R3C)
  rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
    MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
  change
    TemperedDistribution.smulLeftCLM R3C (r3SobolevWeightComplex (-3))
        ((𝓕 g : R3L2Velocity) : TemperedDistribution R3 R3C) =
      ((𝓕 (r3H3ToL2Operator g) : R3L2Velocity) :
        TemperedDistribution R3 R3C)
  rw [fourier_r3H3ToL2Operator]
  symm
  exact MeasureTheory.Lp.toTemperedDistribution_smul_eq
    (r3SobolevWeightComplex_hasTemperateGrowth (-3))
    r3H3InverseBesselWeightComplex_memLp_top (𝓕 g)

theorem r3H3InverseBesselWeight_mul_smoothingScalar
    (nu tau : ℝ) (xi : R3) :
    r3H3InverseBesselWeightComplex xi *
        r3StokesH2ToH3ScalarComplex nu tau xi =
      r3StokesScalarComplex nu tau xi * r3H2InverseBesselWeightComplex xi := by
  have hweights :
      r3H3InverseBesselWeightComplex xi * r3SobolevWeightComplex 1 xi =
        r3H2InverseBesselWeightComplex xi := by
    unfold r3H3InverseBesselWeightComplex r3SobolevWeightComplex
      r3H2InverseBesselWeightComplex
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    congr 1
    norm_num
  unfold r3StokesH2ToH3ScalarComplex
  rw [← mul_assoc, hweights, mul_comm]

theorem r3H3InverseBesselFrequency_smoothing_eq_stokes_H2Inverse
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3L2Velocity) :
    r3H3InverseBesselL2FrequencyOperator
        (r3StokesH2ToH3FrequencyOperator hnu htau g) =
      r3StokesL2FrequencyMultiplier hnu.le htau.le
        (r3H2InverseBesselL2FrequencyOperator g) := by
  apply Lp.ext
  filter_upwards
    [r3H3InverseBesselL2FrequencyOperator_ae
      (r3StokesH2ToH3FrequencyOperator hnu htau g),
      r3StokesH2ToH3FrequencyOperator_ae hnu htau g,
      r3StokesL2FrequencyMultiplier_ae hnu.le htau.le
        (r3H2InverseBesselL2FrequencyOperator g),
      r3H2InverseBesselL2FrequencyOperator_ae g]
    with xi hleft hsmooth hright hinverse
  rw [hleft, hsmooth, hright, hinverse, smul_smul, smul_smul,
    r3H3InverseBesselWeight_mul_smoothingScalar]

/--
Reconstructing the smoothed order-three coordinate gives the literal physical `L^2` Stokes flow
of the reconstructed order-two input.
-/
theorem r3H3ToL2Operator_r3StokesH2ToH3Operator
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    r3H3ToL2Operator (r3StokesH2ToH3Operator hnu htau g) =
      r3StokesL2Operator hnu.le htau.le (r3H2ToL2Operator g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3H3ToL2Operator (r3StokesH2ToH3Operator hnu htau g)) =
      𝓕 (r3StokesL2Operator hnu.le htau.le (r3H2ToL2Operator g))
  rw [fourier_r3H3ToL2Operator,
    fourier_r3StokesH2ToH3Operator,
    fourier_r3StokesL2Operator, fourier_r3H2ToL2Operator]
  exact r3H3InverseBesselFrequency_smoothing_eq_stokes_H2Inverse
    hnu htau (𝓕 g)

/-- Exact decoder compatibility of the positive-time `H^2`-to-`H^3` smoothing map. -/
theorem r3HsToTempered_r3StokesH2ToH3Operator
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    r3HsToTemperedCLM 3 (r3StokesH2ToH3Operator hnu htau g) =
      r3L2ToTemperedCLM
        (r3StokesL2Operator hnu.le htau.le (r3H2ToL2Operator g)) := by
  rw [← r3L2ToTempered_r3H3ToL2Operator,
    r3H3ToL2Operator_r3StokesH2ToH3Operator]

/-- The Leray projector acting specifically on stored order-three Bessel coordinates. -/
def r3LerayH3Operator :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 :=
  r3LerayL2Operator

@[simp]
theorem r3LerayH3Operator_apply (g : R3HsVelocity 3) :
    r3LerayH3Operator g = r3LerayL2Operator g := by
  rfl

theorem r3H3InverseBesselL2FrequencyOperator_commutes_leray
    (g : R3L2Velocity) :
    r3H3InverseBesselL2FrequencyOperator
        (r3LerayL2FrequencyOperator g) =
      r3LerayL2FrequencyOperator
        (r3H3InverseBesselL2FrequencyOperator g) := by
  apply Lp.ext
  filter_upwards
    [r3H3InverseBesselL2FrequencyOperator_ae
      (r3LerayL2FrequencyOperator g),
      r3LerayL2FrequencyOperator_ae g,
      r3LerayL2FrequencyOperator_ae
        (r3H3InverseBesselL2FrequencyOperator g),
      r3H3InverseBesselL2FrequencyOperator_ae g]
    with xi hleft hleray hright hinverse
  rw [hleft, hleray, hright, hinverse]
  exact (r3LeraySymbolComplex xi).map_smul
    (r3H3InverseBesselWeightComplex xi) (g xi) |>.symm

theorem r3H3ToL2Operator_commutes_leray (g : R3HsVelocity 3) :
    r3H3ToL2Operator (r3LerayH3Operator g) =
      r3LerayL2Operator (r3H3ToL2Operator g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3H3ToL2Operator (r3LerayH3Operator g)) =
      𝓕 (r3LerayL2Operator (r3H3ToL2Operator g))
  rw [fourier_r3H3ToL2Operator, r3LerayH3Operator_apply,
    fourier_r3LerayL2Operator, fourier_r3LerayL2Operator,
    fourier_r3H3ToL2Operator]
  exact r3H3InverseBesselL2FrequencyOperator_commutes_leray (𝓕 g)

/-- The order-three decoder gives the physical `L^2` meaning of coordinate Leray projection. -/
theorem r3HsToTempered_r3LerayH3Operator (g : R3HsVelocity 3) :
    r3HsToTemperedCLM 3 (r3LerayH3Operator g) =
      r3L2ToTemperedCLM
        (r3LerayL2Operator (r3H3ToL2Operator g)) := by
  rw [← r3L2ToTempered_r3H3ToL2Operator,
    r3H3ToL2Operator_commutes_leray]

theorem r3StokesH2ToH3FrequencyOperator_commutes_leray
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3L2Velocity) :
    r3StokesH2ToH3FrequencyOperator hnu htau
        (r3LerayL2FrequencyOperator g) =
      r3LerayL2FrequencyOperator
        (r3StokesH2ToH3FrequencyOperator hnu htau g) := by
  apply Lp.ext
  filter_upwards
    [r3StokesH2ToH3FrequencyOperator_ae hnu htau
      (r3LerayL2FrequencyOperator g),
      r3LerayL2FrequencyOperator_ae g,
      r3LerayL2FrequencyOperator_ae
        (r3StokesH2ToH3FrequencyOperator hnu htau g),
      r3StokesH2ToH3FrequencyOperator_ae hnu htau g]
    with xi hleft hleray hright hsmooth
  rw [hleft, hleray, hright, hsmooth]
  exact (r3LeraySymbolComplex xi).map_smul
    (r3StokesH2ToH3ScalarComplex nu tau xi) (g xi) |>.symm

/-- The order-aware Stokes smoothing map intertwines order-two and order-three Leray projection. -/
theorem r3StokesH2ToH3Operator_commutes_leray
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau) (g : R3HsVelocity 2) :
    r3StokesH2ToH3Operator hnu htau (r3LerayH2Operator g) =
      r3LerayH3Operator (r3StokesH2ToH3Operator hnu htau g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change
    𝓕 (r3StokesH2ToH3Operator hnu htau (r3LerayH2Operator g)) =
      𝓕 (r3LerayH3Operator (r3StokesH2ToH3Operator hnu htau g))
  rw [fourier_r3StokesH2ToH3Operator, r3LerayH2Operator_apply,
    fourier_r3LerayL2Operator, r3LerayH3Operator_apply,
    fourier_r3LerayL2Operator, fourier_r3StokesH2ToH3Operator]
  exact r3StokesH2ToH3FrequencyOperator_commutes_leray hnu htau (𝓕 g)

/-- Positive-time smoothing preserves the stored-coordinate `L^2` solenoidal submodule. -/
theorem r3StokesH2ToH3Operator_mem_solenoidal
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau)
    (g : R3HsVelocity 2) (hg : g ∈ r3L2SolenoidalSubmodule) :
    r3StokesH2ToH3Operator hnu htau g ∈ r3L2SolenoidalSubmodule := by
  have hcomm := r3StokesH2ToH3Operator_commutes_leray hnu htau g
  rw [r3LerayH2Operator_apply,
    r3LerayL2Operator_fixed_of_mem g hg] at hcomm
  rw [hcomm]
  exact r3LerayL2Operator_mem_solenoidal _

theorem r3H2ToL2Operator_mem_solenoidal_of_mem
    (g : R3HsVelocity 2) (hg : g ∈ r3L2SolenoidalSubmodule) :
    r3H2ToL2Operator g ∈ r3L2SolenoidalSubmodule := by
  have hcomm := r3H2ToL2Operator_commutes_leray g
  rw [r3LerayH2Operator_apply,
    r3LerayL2Operator_fixed_of_mem g hg] at hcomm
  rw [hcomm]
  exact r3LerayL2Operator_mem_solenoidal _

/-- The reconstructed physical `L^2` Stokes output remains solenoidal. -/
theorem r3StokesL2Operator_r3H2ToL2Operator_mem_solenoidal
    {nu tau : ℝ} (hnu : 0 < nu) (htau : 0 < tau)
    (g : R3HsVelocity 2) (hg : g ∈ r3L2SolenoidalSubmodule) :
    r3StokesL2Operator hnu.le htau.le (r3H2ToL2Operator g) ∈
      r3L2SolenoidalSubmodule := by
  exact r3StokesL2Operator_mem_solenoidal hnu.le htau.le _
    (r3H2ToL2Operator_mem_solenoidal_of_mem g hg)

end

end MNS2
