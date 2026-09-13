import Formal.R3ConvectionSourceIdentification
import Formal.R3EndpointSafeProjectedDuhamel

/-!
# Duhamel differentiation infrastructure for the projected momentum equation
(Clay semantic-promotion edge 2b-ii.a, **infrastructure pass**)

This file builds — and proves — analytic machinery **towards** the passage from the
endpoint-safe projected **mild** equation (`IsR3EndpointSafeProjectedMildSolutionOn`) to
the projected **momentum** equation `∂ₜU − νΔU + P((U·∇)U) = 0` for the decoded physical
velocity `U t = r3H3ToL2Operator (u t)`.  These lemmas are **not** verified to be
sufficient for that passage; what is proved here is exactly:

* **The decoded Laplacian.**  `r3H3LaplacianL2Operator` is the explicit bounded
  multiplier `Δ̂·J⁻³` conjugated by the Fourier transform (its order-two companion
  `r3H2LaplacianL2Operator` carries `Δ̂·J⁻²`; only the order-three one is identified
  distributionally below), with
  `Δ̂(ξ) = −(2π)²‖ξ‖²` in the repository's convention.  It **earns the name `Δ`** by
  theorem: `r3L2ToTempered_r3H3LaplacianL2Operator` proves that its `L²` embedding is the
  distributional Laplacian `∑ᵢ ∂ᵢ∂ᵢ` of the tempered distribution decoded by the
  carrier's own order-three decoder.
* **Commutations.** `r3H3LaplacianL2Operator_stokes` (the Laplacian commutes with the
  Stokes flow) and `r3H3LaplacianL2Operator_smoothing` (it intertwines the `H²→H³`
  smoothing operator with the physical heat flow through the order-two Laplacian) — the
  two identities that move `νΔ` through the Duhamel formula.
* **The generator identity.** `hasDerivAt_inner_r3StokesL2Path`: at every positive time
  the pairing derivative of the heat flow of `X` is the pairing of the heat flow of `Y`,
  for any pair with `𝓕Y = νΔ̂ • 𝓕X` a.e.  Proved by differentiating the explicit heat
  kernel under the frequency integral (dominated a.e. derivative; the smoothing factor
  `z e^{-zc} ≤ c⁻¹` of `mul_exp_neg_mul_le` absorbs the frequency growth at positive
  times), with `fourier_r3H3Laplacian_ae` / `fourier_r3H2Laplacian_ae` supplying the
  hypothesis for the decoded Laplacians.
* **The integrated form.** `integral_inner_r3StokesL2Path`: the fundamental theorem of
  calculus on each time slice (one-sided derivative on the open interval, so the `τ = 0`
  endpoint is never differentiated).
* **The triangle swap.** `integral_triangle_swap`: Fubini for the Duhamel triangle
  `{(s, σ) : s ≤ σ}` on a compact time square.
* **The decoded mild identity.** `r3MildDecodedVelocity_duhamel`: the decoded velocity of
  a mild solution is the heat-flowed initial datum minus the heat-flowed convection
  source, integrated in time — the decoded form on which the momentum assembly runs.
* **The nonlinearity is identified.** `r3MildConvectionSource_eq` records that the decoded
  Duhamel source is, by edge 2b-i, the Leray projection of the literal pointwise
  convection of the decoded representatives; `r3HelmholtzPressure_gradient_trajectoryConvection`
  instantiates the edge-2a pressure witness at that source.

**Scope of this file.**  The final assembly — the fundamental integral identity and the
strong `L²`-valued time derivative — is **not** in this file: at the time of this file's
pass it was attempted, hit repeated Lean elaboration timeouts, and was removed rather
than shipped unverified.  It has since been completed in
`Formal/R3ProjectedMomentumEquation.lean` (edge 2b-ii.a-assembly), which consumes the
commutations, the generator identity in its integrated form, the triangle swap and the
decoded mild identity.  Two items above remain unconsumed by any theorem:
`r3L2ToTempered_r3H3LaplacianL2Operator` is cited to earn the name `Δ` but not used in
the assembly, and `r3HelmholtzPressure_gradient_trajectoryConvection` is the edge-2a
pressure witness reserved for edge 2b-ii.b.  Not claimed in either file: classical
pointwise time derivatives beyond the `L²`-valued one, global smoothness, the unprojected
equation with pressure (edge 2b-ii.b), and edges 3/4/5.

No phantom Sobolev inclusion is used: every physical object passes through the explicit
decoders.  No rapid decay is claimed.
-/

namespace MNS2

open MeasureTheory FourierTransform Real LineDeriv intervalIntegral
open scoped FourierTransform SchwartzMap ContDiff NNReal

noncomputable section

/-! ## The decoded Laplacian as a bounded coordinate multiplier -/

/-- The frequency symbol of the physical Laplacian under the repository convention:
`Δ̂(ξ) = −(2π)²‖ξ‖²`. -/
def r3LaplacianSymbol (ξ : R3) : ℝ := -((2 * π) ^ 2 * ‖ξ‖ ^ 2)

theorem neg_r3StokesDecayRate (ν : ℝ) (ξ : R3) :
    ν * r3LaplacianSymbol ξ = -r3StokesDecayRate ν ξ := by
  unfold r3LaplacianSymbol r3StokesDecayRate
  ring

/-- The decoded order-three Laplacian weight `Δ̂·J⁻³`; two of the three inverse powers
absorb the symbol growth. -/
def r3H3LaplacianWeight : R3 → ℂ :=
  fun ξ => ((r3LaplacianSymbol ξ : ℝ) : ℂ) * r3H3InverseBesselWeightComplex ξ

/-- The decoded order-two Laplacian weight `Δ̂·J⁻²`. -/
def r3H2LaplacianWeight : R3 → ℂ :=
  fun ξ => ((r3LaplacianSymbol ξ : ℝ) : ℂ) * r3H2InverseBesselWeightComplex ξ

theorem continuous_r3H3LaplacianWeight : Continuous r3H3LaplacianWeight := by
  unfold r3H3LaplacianWeight r3LaplacianSymbol
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul
    continuous_r3H3InverseBesselWeightComplex

theorem continuous_r3H2LaplacianWeight : Continuous r3H2LaplacianWeight := by
  unfold r3H2LaplacianWeight r3LaplacianSymbol
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul
    continuous_r3H2InverseBesselWeightComplex

/-- Two inverse Bessel powers absorb the Laplacian symbol at order three. -/
theorem norm_r3H3LaplacianWeight_le (ξ : R3) :
    ‖r3H3LaplacianWeight ξ‖ ≤ (2 * π) ^ 2 := by
  have hb : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hsym : ‖((r3LaplacianSymbol ξ : ℝ) : ℂ)‖ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold r3LaplacianSymbol
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hweight : ‖r3H3InverseBesselWeightComplex ξ‖ = (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) := by
    unfold r3H3InverseBesselWeightComplex r3SobolevWeightComplex
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hb.le _)]
  unfold r3H3LaplacianWeight
  rw [norm_mul, hsym, hweight]
  have hsq : ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) ≤ 1 := by
    have h1 : ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by linarith [sq_nonneg ‖ξ‖]
    have h2 : ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) ≤
        (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hb.le _)
    have h3 : (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) := by
      rw [show (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) =
          (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) by
        rw [Real.rpow_one], ← Real.rpow_add hb]
      norm_num
    have h4 : ((1 : ℝ) + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)
    calc ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2)
        ≤ (1 + ‖ξ‖ ^ 2) ^ ((-1 : ℝ) / 2) := h2.trans_eq h3
      _ ≤ 1 := h4
  calc (2 * π) ^ 2 * ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2)
      = (2 * π) ^ 2 * (‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2)) := by ring
    _ ≤ (2 * π) ^ 2 * 1 := by
        have hpos : (0 : ℝ) ≤ (2 * π) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hsq hpos
    _ = (2 * π) ^ 2 := mul_one _

/-- One inverse Bessel power pair absorbs the Laplacian symbol at order two. -/
theorem norm_r3H2LaplacianWeight_le (ξ : R3) :
    ‖r3H2LaplacianWeight ξ‖ ≤ (2 * π) ^ 2 := by
  have hb : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hsym : ‖((r3LaplacianSymbol ξ : ℝ) : ℂ)‖ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold r3LaplacianSymbol
    rw [abs_neg, abs_of_nonneg (by positivity)]
  have hweight : ‖r3H2InverseBesselWeightComplex ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) := by
    unfold r3H2InverseBesselWeightComplex
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hb.le _)]
  unfold r3H2LaplacianWeight
  rw [norm_mul, hsym, hweight]
  have hsq : ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) ≤ 1 := by
    have hinv : (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) = (1 + ‖ξ‖ ^ 2)⁻¹ := by
      rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
    rw [hinv, ← div_eq_mul_inv, div_le_one hb]
    linarith [sq_nonneg ‖ξ‖]
  calc (2 * π) ^ 2 * ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)
      = (2 * π) ^ 2 * (‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ)) := by ring
    _ ≤ (2 * π) ^ 2 * 1 := by
        have hpos : (0 : ℝ) ≤ (2 * π) ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hsq hpos
    _ = (2 * π) ^ 2 := mul_one _

theorem r3H3LaplacianWeight_memLp_top :
    MemLp r3H3LaplacianWeight ⊤ (volume : Measure R3) :=
  memLp_top_of_bound continuous_r3H3LaplacianWeight.aestronglyMeasurable
    ((2 * π) ^ 2) (Filter.Eventually.of_forall norm_r3H3LaplacianWeight_le)

theorem r3H2LaplacianWeight_memLp_top :
    MemLp r3H2LaplacianWeight ⊤ (volume : Measure R3) :=
  memLp_top_of_bound continuous_r3H2LaplacianWeight.aestronglyMeasurable
    ((2 * π) ^ 2) (Filter.Eventually.of_forall norm_r3H2LaplacianWeight_le)

/-- The decoded order-three Laplacian weight as an `L∞` multiplier element. -/
def r3H3LaplacianWeightLpTop : Lp ℂ ⊤ (volume : Measure R3) :=
  r3H3LaplacianWeight_memLp_top.toLp r3H3LaplacianWeight

/-- The decoded order-two Laplacian weight as an `L∞` multiplier element. -/
def r3H2LaplacianWeightLpTop : Lp ℂ ⊤ (volume : Measure R3) :=
  r3H2LaplacianWeight_memLp_top.toLp r3H2LaplacianWeight

/-- **The decoded Laplacian from the order-three coordinate**: conjugation of the bounded
multiplier `Δ̂·J⁻³` by the Fourier transform. -/
def r3H3LaplacianL2Operator : R3HsVelocity 3 →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3L2ScalarMultiplier r3H3LaplacianWeightLpTop ∘L
      fourierCLM ℂ R3L2Velocity

/-- The decoded Laplacian from the order-two coordinate. -/
def r3H2LaplacianL2Operator : R3HsVelocity 2 →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3L2ScalarMultiplier r3H2LaplacianWeightLpTop ∘L
      fourierCLM ℂ R3L2Velocity

theorem r3H3LaplacianMultiplier_ae (g : R3L2Velocity) :
    r3L2ScalarMultiplier r3H3LaplacianWeightLpTop g =ᵐ[volume]
      fun ξ => r3H3LaplacianWeight ξ • g ξ := by
  rw [r3L2ScalarMultiplier_apply]
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ENNReal)) r3H3LaplacianWeightLpTop g,
      MemLp.coeFn_toLp r3H3LaplacianWeight_memLp_top] with ξ hmul hweight
  rw [hmul]
  exact congrArg (fun c : ℂ => c • g ξ) hweight

theorem r3H2LaplacianMultiplier_ae (g : R3L2Velocity) :
    r3L2ScalarMultiplier r3H2LaplacianWeightLpTop g =ᵐ[volume]
      fun ξ => r3H2LaplacianWeight ξ • g ξ := by
  rw [r3L2ScalarMultiplier_apply]
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ENNReal)) r3H2LaplacianWeightLpTop g,
      MemLp.coeFn_toLp r3H2LaplacianWeight_memLp_top] with ξ hmul hweight
  rw [hmul]
  exact congrArg (fun c : ℂ => c • g ξ) hweight

theorem fourier_r3H3LaplacianL2Operator (g : R3HsVelocity 3) :
    𝓕 (r3H3LaplacianL2Operator g) =
      r3L2ScalarMultiplier r3H3LaplacianWeightLpTop (𝓕 g) := by
  simp [r3H3LaplacianL2Operator]

theorem fourier_r3H2LaplacianL2Operator (g : R3HsVelocity 2) :
    𝓕 (r3H2LaplacianL2Operator g) =
      r3L2ScalarMultiplier r3H2LaplacianWeightLpTop (𝓕 g) := by
  simp [r3H2LaplacianL2Operator]

/-! ## Commutation of the decoded Laplacian with the heat operators -/

/-- The decoded Laplacian commutes with the Stokes flow on the coordinate carrier. -/
theorem r3H3LaplacianL2Operator_stokes {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : R3HsVelocity 3) :
    r3H3LaplacianL2Operator (r3StokesL2Operator hν ht f) =
      r3StokesL2Operator hν ht (r3H3LaplacianL2Operator f) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change 𝓕 (r3H3LaplacianL2Operator (r3StokesL2Operator hν ht f)) =
    𝓕 (r3StokesL2Operator hν ht (r3H3LaplacianL2Operator f))
  rw [fourier_r3H3LaplacianL2Operator, fourier_r3StokesL2Operator,
    fourier_r3StokesL2Operator, fourier_r3H3LaplacianL2Operator]
  apply Lp.ext
  filter_upwards [r3H3LaplacianMultiplier_ae (r3StokesL2FrequencyMultiplier hν ht (𝓕 f)),
    r3StokesL2FrequencyMultiplier_ae hν ht (𝓕 f),
    r3StokesL2FrequencyMultiplier_ae hν ht
      (r3L2ScalarMultiplier r3H3LaplacianWeightLpTop (𝓕 f)),
    r3H3LaplacianMultiplier_ae ((𝓕 f : R3L2Velocity))] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, smul_smul, smul_smul, mul_comm]

/-- The decoded Laplacian intertwines the `H²→H³` smoothing operator with the physical
heat flow through the order-two Laplacian: `Δ̂J⁻³ · (J¹e^{−ντΔ̂}) = e^{−ντΔ̂} · Δ̂J⁻²`. -/
theorem r3H3LaplacianL2Operator_smoothing {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ)
    (g : R3HsVelocity 2) :
    r3H3LaplacianL2Operator (r3StokesH2ToH3Operator hν hτ g) =
      r3StokesL2Operator hν.le hτ.le (r3H2LaplacianL2Operator g) := by
  apply (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).injective
  change 𝓕 (r3H3LaplacianL2Operator (r3StokesH2ToH3Operator hν hτ g)) =
    𝓕 (r3StokesL2Operator hν.le hτ.le (r3H2LaplacianL2Operator g))
  rw [fourier_r3H3LaplacianL2Operator, fourier_r3StokesH2ToH3Operator,
    fourier_r3StokesL2Operator, fourier_r3H2LaplacianL2Operator]
  apply Lp.ext
  filter_upwards [r3H3LaplacianMultiplier_ae (r3StokesH2ToH3FrequencyOperator hν hτ (𝓕 g)),
    r3StokesH2ToH3FrequencyOperator_ae hν hτ (𝓕 g),
    r3StokesL2FrequencyMultiplier_ae hν.le hτ.le
      (r3L2ScalarMultiplier r3H2LaplacianWeightLpTop (𝓕 g)),
    r3H2LaplacianMultiplier_ae ((𝓕 g : R3L2Velocity))] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, smul_smul, smul_smul]
  congr 1
  unfold r3H3LaplacianWeight r3H2LaplacianWeight
  have hcollapse := r3H3InverseBesselWeight_mul_smoothingScalar ν τ ξ
  calc ((r3LaplacianSymbol ξ : ℝ) : ℂ) * r3H3InverseBesselWeightComplex ξ *
        r3StokesH2ToH3ScalarComplex ν τ ξ
      = ((r3LaplacianSymbol ξ : ℝ) : ℂ) *
          (r3H3InverseBesselWeightComplex ξ * r3StokesH2ToH3ScalarComplex ν τ ξ) := by
        ring
    _ = ((r3LaplacianSymbol ξ : ℝ) : ℂ) *
          (r3StokesScalarComplex ν τ ξ * r3H2InverseBesselWeightComplex ξ) := by
        rw [hcollapse]
    _ = r3StokesScalarComplex ν τ ξ *
          (((r3LaplacianSymbol ξ : ℝ) : ℂ) * r3H2InverseBesselWeightComplex ξ) := by
        ring

/-! ## The decoded Laplacian is the distributional Laplacian -/

/-- The distributional Laplacian on `R3C`-valued tempered distributions:
`Δ = ∑ᵢ ∂ᵢ∂ᵢ`. -/
def r3TemperedLaplacian (T : 𝓢'(R3, R3C)) : 𝓢'(R3, R3C) :=
  ∑ i : Fin 3, ∂_{r3StdBasis i} (∂_{r3StdBasis i} T)

theorem r3TemperedLaplacian_apply (T : 𝓢'(R3, R3C)) (φ : 𝓢(R3, ℂ)) :
    r3TemperedLaplacian T φ = ∑ i : Fin 3, T (∂_{r3StdBasis i} (∂_{r3StdBasis i} φ)) := by
  unfold r3TemperedLaplacian
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc (∂_{r3StdBasis i} (∂_{r3StdBasis i} T)) φ
      = T (-∂_{r3StdBasis i} (-∂_{r3StdBasis i} φ)) := rfl
    _ = T (∂_{r3StdBasis i} (∂_{r3StdBasis i} φ)) := by
        congr 1
        rw [show ∂_{r3StdBasis i} (-∂_{r3StdBasis i} φ) =
            -∂_{r3StdBasis i} (∂_{r3StdBasis i} φ) from
          map_neg (LineDeriv.lineDerivOpCLM ℂ 𝓢(R3, ℂ) (r3StdBasis i)) _, neg_neg]

/-- The second-order multiplier obtained by pulling two coordinate derivatives through the
Fourier transform: `ξ ↦ (-(2πi)ξᵢ)² ψ ξ`. -/
def r3SecondDerivMultiplier (ψ : 𝓢(R3, ℂ)) (i : Fin 3) : 𝓢(R3, ℂ) :=
  r3DerivMultiplier (r3DerivMultiplier ψ i) i

theorem lineDerivOp_two_eq_fourier (ψ : 𝓢(R3, ℂ)) (i : Fin 3) :
    ∂_{r3StdBasis i} (∂_{r3StdBasis i} (𝓕 ψ)) = 𝓕 (r3SecondDerivMultiplier ψ i) := by
  unfold r3SecondDerivMultiplier
  rw [lineDerivOp_eq_fourier_r3DerivMultiplier ψ i,
    lineDerivOp_eq_fourier_r3DerivMultiplier (r3DerivMultiplier ψ i) i]

theorem r3SecondDerivMultiplier_apply (ψ : 𝓢(R3, ℂ)) (i : Fin 3) (ξ : R3) :
    r3SecondDerivMultiplier ψ i ξ =
      -((2 * π) ^ 2 : ℝ) * (((ξ i : ℝ) : ℂ)) ^ 2 * ψ ξ := by
  unfold r3SecondDerivMultiplier
  rw [r3DerivMultiplier_apply, r3DerivMultiplier_apply]
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  push_cast
  ring_nf
  rw [hI]
  ring

/-- Summing the second-order multipliers over the three coordinates produces exactly the
Laplacian symbol. -/
theorem sum_r3SecondDerivMultiplier_apply (ψ : 𝓢(R3, ℂ)) (ξ : R3) :
    ∑ i : Fin 3, r3SecondDerivMultiplier ψ i ξ =
      ((r3LaplacianSymbol ξ : ℝ) : ℂ) * ψ ξ := by
  have hnorm : ((‖ξ‖ ^ 2 : ℝ) : ℂ) =
      ((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2 := by
    have hr : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hr]
    push_cast
    ring
  rw [Fin.sum_univ_three, r3SecondDerivMultiplier_apply, r3SecondDerivMultiplier_apply,
    r3SecondDerivMultiplier_apply]
  unfold r3LaplacianSymbol
  push_cast
  rw [show ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring, hnorm]
  ring

/-- **The decoded Laplacian is the distributional Laplacian**: the bounded multiplier
operator `Δ̂·J⁻³` represents, through the plain `L²` embedding, exactly the distributional
Laplacian of the tempered distribution decoded by the carrier's order-three decoder.  This
is what earns the operator the name `Δ`. -/
theorem r3L2ToTempered_r3H3LaplacianL2Operator (f : R3HsVelocity 3) :
    r3L2ToTemperedCLM (r3H3LaplacianL2Operator f) =
      r3TemperedLaplacian (r3HsToTemperedCLM 3 f) := by
  have hdecode : r3HsToTemperedCLM 3 f = r3L2ToTemperedCLM (r3H3ToL2Operator f) :=
    (r3L2ToTempered_r3H3ToL2Operator f).symm
  rw [hdecode]
  refine DFunLike.ext _ _ fun φ => ?_
  set ψ : 𝓢(R3, ℂ) := 𝓕⁻ φ with hψdef
  have hφ : 𝓕 ψ = φ := fourier_fourierInv_eq φ
  set W : R3L2Velocity := r3H3ToL2Operator f with hWdef
  -- Pairing of an `L²` field against a Fourier-side multiplier.
  have hpair : ∀ (V : R3L2Velocity) (χ : 𝓢(R3, ℂ)),
      (r3L2ToTemperedCLM V) (𝓕 χ) =
        ∫ ξ : R3, χ ξ • ((𝓕 V : R3L2Velocity) : R3 → R3C) ξ := by
    intro V χ
    calc (r3L2ToTemperedCLM V) (𝓕 χ)
        = (V : 𝓢'(R3, R3C)) (𝓕 χ) := rfl
      _ = (𝓕 (V : 𝓢'(R3, R3C))) χ :=
          (TemperedDistribution.fourier_apply (V : 𝓢'(R3, R3C)) χ).symm
      _ = ((𝓕 V : R3L2Velocity) : 𝓢'(R3, R3C)) χ := by
          rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      _ = ∫ ξ : R3, χ ξ • ((𝓕 V : R3L2Velocity) : R3 → R3C) ξ :=
          MeasureTheory.Lp.toTemperedDistribution_apply (𝓕 V) χ
  have hint : ∀ (V : R3L2Velocity) (χ : 𝓢(R3, ℂ)),
      Integrable (fun ξ : R3 => χ ξ • ((𝓕 V : R3L2Velocity) : R3 → R3C) ξ) volume := by
    intro V χ
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (𝓕 V)).smul (χ.memLp 2 (volume : Measure R3)))
  -- Left side: the decoded Laplacian, paired.
  have hL : (r3L2ToTemperedCLM (r3H3LaplacianL2Operator f)) φ =
      ∫ ξ : R3, ψ ξ • (r3H3LaplacianWeight ξ • ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) := by
    rw [← hφ, hpair (r3H3LaplacianL2Operator f) ψ]
    refine integral_congr_ae ?_
    rw [fourier_r3H3LaplacianL2Operator]
    filter_upwards [r3H3LaplacianMultiplier_ae ((𝓕 f : R3L2Velocity))] with ξ hξ
    rw [hξ]
  -- Right side: the distributional Laplacian of the decode, paired.
  have hR : (r3TemperedLaplacian (r3L2ToTemperedCLM W)) φ =
      ∑ i : Fin 3, ∫ ξ : R3,
        r3SecondDerivMultiplier ψ i ξ • ((𝓕 W : R3L2Velocity) : R3 → R3C) ξ := by
    rw [r3TemperedLaplacian_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ∂_{r3StdBasis i} (∂_{r3StdBasis i} φ) = 𝓕 (r3SecondDerivMultiplier ψ i) from by
      rw [← hφ]; exact lineDerivOp_two_eq_fourier ψ i]
    exact hpair W (r3SecondDerivMultiplier ψ i)
  rw [hL, hR, ← MeasureTheory.integral_finsetSum _ (fun i _ => hint W _)]
  refine integral_congr_ae ?_
  have hWfourier : ((𝓕 W : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => r3H3InverseBesselWeightComplex ξ • ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ := by
    rw [hWdef, fourier_r3H3ToL2Operator]
    exact r3H3InverseBesselL2FrequencyOperator_ae (𝓕 f)
  filter_upwards [hWfourier] with ξ hξ
  rw [hξ]
  have hsum : ∑ i : Fin 3,
      r3SecondDerivMultiplier ψ i ξ •
        (r3H3InverseBesselWeightComplex ξ • ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) =
      (∑ i : Fin 3, r3SecondDerivMultiplier ψ i ξ) •
        (r3H3InverseBesselWeightComplex ξ • ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) := by
    rw [Finset.sum_smul]
  rw [hsum, sum_r3SecondDerivMultiplier_apply]
  unfold r3H3LaplacianWeight
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-! ## The totalized heat flow path and its pairing derivative -/

/-- The physical heat flow path, totalized by clamping the elapsed time at zero (the
continuous extension: `S(0) = id`). -/
def r3StokesL2Path {ν : ℝ} (hν : 0 ≤ ν) (X : R3L2Velocity) (τ : ℝ) : R3L2Velocity :=
  r3StokesL2Operator hν (le_max_left 0 τ) X

theorem r3StokesL2Path_of_nonneg {ν : ℝ} (hν : 0 ≤ ν) (X : R3L2Velocity) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    r3StokesL2Path hν X τ = r3StokesL2Operator hν hτ X := by
  unfold r3StokesL2Path
  simp only [max_eq_right hτ]

theorem r3StokesL2Path_of_nonpos {ν : ℝ} (hν : 0 ≤ ν) (X : R3L2Velocity) {τ : ℝ}
    (hτ : τ ≤ 0) :
    r3StokesL2Path hν X τ = X := by
  unfold r3StokesL2Path
  simp only [max_eq_left hτ]
  exact DFunLike.congr_fun (r3StokesL2Operator_zero_time hν) X

theorem continuous_r3StokesL2Path {ν : ℝ} (hν : 0 ≤ ν) (X : R3L2Velocity) :
    Continuous (r3StokesL2Path hν X) := by
  have h : r3StokesL2Path hν X =
      (fun t : Set.Ici (0 : ℝ) => r3StokesL2Operator hν t.property X) ∘
        (fun τ : ℝ => (⟨max 0 τ, le_max_left 0 τ⟩ : Set.Ici (0 : ℝ))) := by
    funext τ
    rfl
  rw [h]
  exact (continuous_r3StokesL2Operator_orbit hν X).comp
    (Continuous.subtype_mk (continuous_const.max continuous_id) _)

/-- The frequency pairing of two `L²` fields is integrable. -/
theorem integrable_fourier_pairing (ψ X : R3L2Velocity) :
    Integrable (fun ξ : R3 =>
      inner ℂ (((𝓕 ψ : R3L2Velocity) : R3 → R3C) ξ)
        (((𝓕 X : R3L2Velocity) : R3 → R3C) ξ)) volume :=
  MeasureTheory.L2.integrable_inner (𝓕 ψ : R3L2Velocity) (𝓕 X : R3L2Velocity)

/-- Frequency representation of the heat pairing at nonnegative times. -/
theorem inner_r3StokesL2Path {ν : ℝ} (hν : 0 ≤ ν) (X ψ : R3L2Velocity) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    inner ℂ ψ (r3StokesL2Path hν X τ) =
      ∫ ξ : R3, Real.exp (-(r3StokesDecayRate ν ξ * τ)) •
        inner ℂ (((𝓕 ψ : R3L2Velocity) : R3 → R3C) ξ)
          (((𝓕 X : R3L2Velocity) : R3 → R3C) ξ) := by
  rw [r3StokesL2Path_of_nonneg hν X hτ]
  have hmap : inner ℂ ψ (r3StokesL2Operator hν hτ X) =
      inner ℂ (𝓕 ψ : R3L2Velocity) (𝓕 (r3StokesL2Operator hν hτ X) : R3L2Velocity) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).inner_map_map ψ _).symm
  rw [hmap, fourier_r3StokesL2Operator, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [r3StokesL2FrequencyMultiplier_ae hν hτ (𝓕 X : R3L2Velocity)]
    with ξ hξ
  rw [hξ]
  rw [inner_smul_right]
  unfold r3StokesScalarComplex r3StokesScalar
  rw [Complex.real_smul]

/-- The exponential smoothing bound `z e^{-zc} ≤ c⁻¹` for `z ≥ 0`, `c > 0`. -/
theorem mul_exp_neg_mul_le {c : ℝ} (hc : 0 < c) {z : ℝ} (_hz : 0 ≤ z) :
    z * Real.exp (-(z * c)) ≤ c⁻¹ := by
  have hw : z * c * Real.exp (-(z * c)) ≤ 1 := by
    have h1 : z * c ≤ Real.exp (z * c) := by
      have := Real.add_one_le_exp (z * c)
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos (z * c))]
    exact h1
  have h2 : z * Real.exp (-(z * c)) = c⁻¹ * (z * c * Real.exp (-(z * c))) := by
    field_simp
  rw [h2]
  calc c⁻¹ * (z * c * Real.exp (-(z * c))) ≤ c⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hc.le)
    _ = c⁻¹ := mul_one _

/-- **The generator identity for the Stokes semigroup, in pairing form**: at every
positive time, the pairing derivative of the heat flow of `X` is the pairing of the heat
flow of `Y`, whenever `𝓕Y = νΔ̂ • 𝓕X` almost everywhere. -/
theorem hasDerivAt_inner_r3StokesL2Path {ν : ℝ} (hν : 0 ≤ ν) {X Y : R3L2Velocity}
    (hXY : ((𝓕 Y : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => (((ν * r3LaplacianSymbol ξ : ℝ)) : ℂ) •
        ((𝓕 X : R3L2Velocity) : R3 → R3C) ξ)
    (ψ : R3L2Velocity) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun σ : ℝ => inner ℂ ψ (r3StokesL2Path hν X σ))
      (inner ℂ ψ (r3StokesL2Path hν Y τ)) τ := by
  set G : R3 → ℂ := fun ξ =>
    inner ℂ (((𝓕 ψ : R3L2Velocity) : R3 → R3C) ξ)
      (((𝓕 X : R3L2Velocity) : R3 → R3C) ξ) with hGdef
  have hGint : Integrable G volume := integrable_fourier_pairing ψ X
  have hGmeas : AEStronglyMeasurable G volume := hGint.aestronglyMeasurable
  have hacont : Continuous fun ξ : R3 => r3StokesDecayRate ν ξ := by
    unfold r3StokesDecayRate
    fun_prop
  have hann : ∀ ξ : R3, 0 ≤ r3StokesDecayRate ν ξ := fun ξ =>
    r3StokesDecayRate_nonneg hν ξ
  have hball : Metric.ball τ (τ / 2) ∈ nhds τ := Metric.ball_mem_nhds τ (by positivity)
  have hhalf : ∀ σ ∈ Metric.ball τ (τ / 2), τ / 2 ≤ σ := by
    intro σ hσ
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hσ
    linarith [hσ.2]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure R3))
    (F := fun σ ξ => Real.exp (-(r3StokesDecayRate ν ξ * σ)) • G ξ)
    (F' := fun σ ξ =>
      (Real.exp (-(r3StokesDecayRate ν ξ * σ)) * -r3StokesDecayRate ν ξ) • G ξ)
    (x₀ := τ) (bound := fun ξ => (τ / 2)⁻¹ * ‖G ξ‖) hball
    (Filter.Eventually.of_forall fun σ =>
      (((Real.continuous_exp.comp
        ((hacont.mul continuous_const).neg)).aestronglyMeasurable).smul hGmeas))
    (by
      refine Integrable.mono' hGint.norm
        (((Real.continuous_exp.comp
          ((hacont.mul continuous_const).neg)).aestronglyMeasurable).smul hGmeas)
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-(r3StokesDecayRate ν ξ * τ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have := mul_nonneg (hann ξ) hτ.le
          linarith)
      nlinarith [norm_nonneg (G ξ), Real.exp_pos (-(r3StokesDecayRate ν ξ * τ))])
    ((((Real.continuous_exp.comp
      ((hacont.mul continuous_const).neg)).mul hacont.neg).aestronglyMeasurable).smul
      hGmeas)
    (Filter.Eventually.of_forall fun ξ => by
      intro σ hσ
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_neg, abs_of_nonneg (hann ξ)]
      have hσhalf : τ / 2 ≤ σ := hhalf σ hσ
      have hmono : Real.exp (-(r3StokesDecayRate ν ξ * σ)) ≤
          Real.exp (-(r3StokesDecayRate ν ξ * (τ / 2))) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hσhalf (hann ξ)
        linarith
      have hkey : r3StokesDecayRate ν ξ *
          Real.exp (-(r3StokesDecayRate ν ξ * (τ / 2))) ≤ (τ / 2)⁻¹ :=
        mul_exp_neg_mul_le (by positivity) (hann ξ)
      have hstep : Real.exp (-(r3StokesDecayRate ν ξ * σ)) * r3StokesDecayRate ν ξ ≤
          (τ / 2)⁻¹ := by
        nlinarith [hann ξ, Real.exp_pos (-(r3StokesDecayRate ν ξ * (τ / 2)))]
      exact mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
    (hGint.norm.const_mul _)
    (Filter.Eventually.of_forall fun ξ => by
      intro σ hσ
      have hlin : HasDerivAt (fun σ : ℝ => -(r3StokesDecayRate ν ξ * σ))
          (-r3StokesDecayRate ν ξ) σ := by
        simpa using (hasDerivAt_id σ).const_mul (-r3StokesDecayRate ν ξ)
      exact (hlin.exp.smul_const (G ξ)))
  obtain ⟨-, hderiv⟩ := key
  have hfun : (fun σ : ℝ => inner ℂ ψ (r3StokesL2Path hν X σ)) =ᶠ[nhds τ]
      (fun σ : ℝ => ∫ ξ : R3, Real.exp (-(r3StokesDecayRate ν ξ * σ)) • G ξ) := by
    filter_upwards [Ioi_mem_nhds hτ] with σ hσ
    exact inner_r3StokesL2Path hν X ψ (le_of_lt hσ)
  have hval : (∫ ξ : R3,
      (Real.exp (-(r3StokesDecayRate ν ξ * τ)) * -r3StokesDecayRate ν ξ) • G ξ) =
      inner ℂ ψ (r3StokesL2Path hν Y τ) := by
    rw [inner_r3StokesL2Path hν Y ψ hτ.le]
    refine integral_congr_ae ?_
    filter_upwards [hXY] with ξ hξ
    rw [hξ, inner_smul_right]
    simp only [Complex.real_smul]
    rw [← neg_r3StokesDecayRate]
    push_cast
    ring
  rw [← hval]
  exact hderiv.congr_of_eventuallyEq hfun

/-- **Duhamel differentiation, integrated form**: on `[s, t]` the flowed increment of `X`
is the time integral of the flowed `νΔ`-image, in the pairing sense. -/
theorem integral_inner_r3StokesL2Path {ν : ℝ} (hν : 0 ≤ ν) {X Y : R3L2Velocity}
    (hXY : ((𝓕 Y : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => (((ν * r3LaplacianSymbol ξ : ℝ)) : ℂ) •
        ((𝓕 X : R3L2Velocity) : R3 → R3C) ξ)
    (ψ : R3L2Velocity) {s t : ℝ} (hst : s ≤ t) :
    (∫ σ in s..t, inner ℂ ψ (r3StokesL2Path hν Y (σ - s))) =
      inner ℂ ψ (r3StokesL2Path hν X (t - s)) - inner ℂ ψ X := by
  set g : ℝ → ℂ := fun σ => inner ℂ ψ (r3StokesL2Path hν X (σ - s)) with hgdef
  set g' : ℝ → ℂ := fun σ => inner ℂ ψ (r3StokesL2Path hν Y (σ - s)) with hg'def
  have hgcont : ContinuousOn g (Set.Icc s t) := by
    refine Continuous.continuousOn ?_
    exact ((innerSL ℂ ψ).continuous.comp
      ((continuous_r3StokesL2Path hν X).comp (continuous_id.sub continuous_const)))
  have hg'cont : Continuous g' :=
    (innerSL ℂ ψ).continuous.comp
      ((continuous_r3StokesL2Path hν Y).comp (continuous_id.sub continuous_const))
  have hderiv : ∀ σ ∈ Set.Ioo s t, HasDerivWithinAt g (g' σ) (Set.Ioi σ) σ := by
    intro σ hσ
    have hpos : 0 < σ - s := sub_pos.mpr hσ.1
    have hshift : HasDerivAt (fun σ : ℝ => σ - s) 1 σ := by
      simpa using (hasDerivAt_id σ).sub_const s
    have hcomp := (hasDerivAt_inner_r3StokesL2Path hν hXY ψ hpos).scomp σ hshift
    rw [one_smul] at hcomp
    exact hcomp.hasDerivWithinAt
  have hint : IntervalIntegrable g' volume s t :=
    hg'cont.intervalIntegrable s t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst hgcont hderiv hint
  rw [hFTC, hgdef]
  simp only [sub_self]
  rw [r3StokesL2Path_of_nonpos hν X (le_refl 0)]

/-! ## Swapping the Duhamel triangle -/

/-- **Triangle swap**: on a compact time square the iterated integral over the triangle
`{(s, σ) : s ≤ σ}` may be taken in either order. -/
theorem integral_triangle_swap {t : ℝ} (ht : 0 ≤ t) (Φ : ℝ → ℝ → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2)
      (Set.Icc 0 t ×ˢ Set.Icc 0 t))
    {C : ℝ} (hbound : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ s ∈ Set.Icc (0 : ℝ) t, ‖Φ σ s‖ ≤ C) :
    (∫ s in (0 : ℝ)..t, ∫ σ in s..t, Φ σ s) =
      ∫ σ in (0 : ℝ)..t, ∫ s in (0 : ℝ)..σ, Φ σ s := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, ht⟩ 0 ⟨le_rfl, ht⟩)
  set F : ℝ → ℝ → ℂ := fun s σ => Set.indicator (Set.Ioi s) (fun σ => Φ σ s) σ with hFdef
  have hFapp : ∀ s σ : ℝ, F s σ = if s < σ then Φ σ s else 0 := by
    intro s σ
    show Set.indicator (Set.Ioi s) (fun σ => Φ σ s) σ = _
    rw [Set.indicator_apply]
    rfl
  have hFalt : ∀ s σ : ℝ, F s σ = Set.indicator (Set.Iio σ) (fun s => Φ σ s) s := by
    intro s σ
    rw [hFapp, Set.indicator_apply]
    rfl
  have huIoc : Set.uIoc (0 : ℝ) t = Set.Ioc 0 t := Set.uIoc_of_le ht
  -- Integrability of the indicator on the square.
  have hswapcont : ContinuousOn (fun p : ℝ × ℝ => Φ p.2 p.1)
      (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t) := by
    have hmaps : Set.MapsTo (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t) (Set.Icc 0 t ×ˢ Set.Icc 0 t) := by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact ⟨⟨hb.1.le, hb.2⟩, ⟨ha.1.le, ha.2⟩⟩
    exact hcont.comp continuous_swap.continuousOn hmaps
  have hmeasSq : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hIntOn : IntegrableOn (Function.uncurry F)
      (Set.uIoc (0 : ℝ) t ×ˢ Set.uIoc (0 : ℝ) t) := by
    rw [huIoc]
    have hmeas : AEStronglyMeasurable (Function.uncurry F)
        ((volume : Measure (ℝ × ℝ)).restrict
          (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t)) := by
      have hbase : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.2 p.1)
          ((volume : Measure (ℝ × ℝ)).restrict
            (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t)) :=
        hswapcont.aestronglyMeasurable hmeasSq
      have hind := hbase.indicator
        (measurableSet_lt measurable_fst measurable_snd)
      refine hind.congr (Filter.Eventually.of_forall fun p => ?_)
      rcases p with ⟨a, b⟩
      show Set.indicator {q : ℝ × ℝ | q.1 < q.2} (fun q => Φ q.2 q.1) (a, b) =
        Function.uncurry F (a, b)
      rw [Set.indicator_apply]
      show (if a < b then Φ b a else 0) = F a b
      rw [hFapp]
    haveI : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioc (0 : ℝ) t ×ˢ Set.Ioc (0 : ℝ) t)) := by
      constructor
      rw [Measure.restrict_apply_univ]
      rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
        Measure.prod_prod, Real.volume_Ioc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine Integrable.mono' (integrable_const C) hmeas ?_
    rw [MeasureTheory.ae_restrict_iff' hmeasSq]
    filter_upwards with p hp
    rcases p with ⟨a, b⟩
    obtain ⟨ha, hb⟩ := hp
    show ‖F a b‖ ≤ C
    rw [hFapp]
    by_cases h : a < b
    · rw [if_pos h]
      exact hbound b ⟨hb.1.le, hb.2⟩ a ⟨ha.1.le, ha.2⟩
    · rw [if_neg h, norm_zero]
      exact hC
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := F) (a := (0 : ℝ)) (b := t) (c := (0 : ℝ)) (d := t) hIntOn
  -- Rewrite both sides as triangle integrals.
  have hleft : (∫ s in (0 : ℝ)..t, ∫ σ in (0 : ℝ)..t, F s σ) =
      ∫ s in (0 : ℝ)..t, ∫ σ in s..t, Φ σ s := by
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs.2,
      MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      Set.Ioc_inter_Ioi, sup_eq_right.mpr hs.1.le]
  have hright : (∫ σ in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, F s σ) =
      ∫ σ in (0 : ℝ)..t, ∫ s in (0 : ℝ)..σ, Φ σ s := by
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
    have hIocIio : Set.Ioc (0 : ℝ) t ∩ Set.Iio σ = Set.Ioo 0 σ := by
      ext x
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le.trans hσ.2⟩, h.2⟩⟩
    rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hσ.1.le]
    rw [show (fun s => F s σ) = Set.indicator (Set.Iio σ) (fun s => Φ σ s) from
      funext fun s => hFalt s σ]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iio, hIocIio,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [← hleft, ← hright]
  exact hswap

/-! ## The projected momentum equation along a mild solution -/

/-- The decoded physical velocity of a coordinate trajectory. -/
def r3MildDecodedVelocity (u : ℝ → R3HsVelocity 3) (s : ℝ) : R3L2Velocity :=
  r3H3ToL2Operator (u s)

/-- The decoded projected convection source `P((U·∇)U)` along the trajectory. -/
def r3MildConvectionSource (u : ℝ → R3HsVelocity 3) (s : ℝ) : R3L2Velocity :=
  r3H2ToL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s))

/-- **Edge-2b-i identification along the trajectory**: the decoded source is the Leray
projection of the literal pointwise convection of the decoded representatives. -/
theorem r3MildConvectionSource_eq (u : ℝ → R3HsVelocity 3) (s : ℝ) :
    r3MildConvectionSource u s =
      r3LerayL2Operator (r3DecodedConvectionL2 (u s) (u s)) :=
  r3H2ToL2Operator_r3ProjectedConvectionH3ToH2 (u s) (u s)

/-- Real scalars act on the `L²` carrier through their complex coercions. -/
theorem r3L2_real_smul (r : ℝ) (X : R3L2Velocity) : r • X = ((r : ℝ) : ℂ) • X := by
  rw [← algebraMap_smul ℂ r X]
  rfl

/-- The `νΔ` frequency relation at order three: the Fourier transform of the scaled decoded
Laplacian is the symbol multiple of the Fourier transform of the decoded velocity. -/
theorem fourier_r3H3Laplacian_ae (ν : ℝ) (f : R3HsVelocity 3) :
    ((𝓕 (ν • r3H3LaplacianL2Operator f) : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => (((ν * r3LaplacianSymbol ξ : ℝ)) : ℂ) •
        ((𝓕 (r3H3ToL2Operator f) : R3L2Velocity) : R3 → R3C) ξ := by
  have hsmul : (𝓕 (ν • r3H3LaplacianL2Operator f) : R3L2Velocity) =
      ((ν : ℝ) : ℂ) • (𝓕 (r3H3LaplacianL2Operator f) : R3L2Velocity) := by
    rw [r3L2_real_smul ν (r3H3LaplacianL2Operator f)]
    exact map_smul (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) _ _
  rw [hsmul, fourier_r3H3LaplacianL2Operator, fourier_r3H3ToL2Operator]
  filter_upwards [Lp.coeFn_smul (((ν : ℝ) : ℂ))
      (r3L2ScalarMultiplier r3H3LaplacianWeightLpTop (𝓕 f)),
    r3H3LaplacianMultiplier_ae ((𝓕 f : R3L2Velocity)),
    r3H3InverseBesselL2FrequencyOperator_ae ((𝓕 f : R3L2Velocity))] with ξ h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_smul, smul_smul]
  unfold r3H3LaplacianWeight
  push_cast
  ring_nf

/-- The `νΔ` frequency relation at order two. -/
theorem fourier_r3H2Laplacian_ae (ν : ℝ) (g : R3HsVelocity 2) :
    ((𝓕 (ν • r3H2LaplacianL2Operator g) : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ => (((ν * r3LaplacianSymbol ξ : ℝ)) : ℂ) •
        ((𝓕 (r3H2ToL2Operator g) : R3L2Velocity) : R3 → R3C) ξ := by
  have hsmul : (𝓕 (ν • r3H2LaplacianL2Operator g) : R3L2Velocity) =
      ((ν : ℝ) : ℂ) • (𝓕 (r3H2LaplacianL2Operator g) : R3L2Velocity) := by
    rw [r3L2_real_smul ν (r3H2LaplacianL2Operator g)]
    exact map_smul (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) _ _
  rw [hsmul, fourier_r3H2LaplacianL2Operator, fourier_r3H2ToL2Operator]
  filter_upwards [Lp.coeFn_smul (((ν : ℝ) : ℂ))
      (r3L2ScalarMultiplier r3H2LaplacianWeightLpTop (𝓕 g)),
    r3H2LaplacianMultiplier_ae ((𝓕 g : R3L2Velocity)),
    r3H2InverseBesselL2FrequencyOperator_ae ((𝓕 g : R3L2Velocity))] with ξ h1 h2 h3
  rw [h1, Pi.smul_apply, h2, h3, smul_smul, smul_smul]
  unfold r3H2LaplacianWeight
  push_cast
  ring_nf

variable {ν T : ℝ} {u₀ : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}

/-- **The decoded mild identity**: the decoded velocity is the heat-flowed initial datum
minus the heat-flowed convection source, integrated in time. -/
theorem r3MildDecodedVelocity_duhamel (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    r3MildDecodedVelocity u t =
      r3StokesL2Path hnu.le (r3MildDecodedVelocity u 0) t -
        ∫ s in (0 : ℝ)..t, r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s) := by
  obtain ⟨hint, heq⟩ := r3EndpointSafeProjectedMild_equation_at_time hnu hu ht
  have hu0 : u 0 = u₀ := hu.2.2.1
  have hdec := congrArg r3H3ToL2Operator heq
  rw [map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm r3H3ToL2Operator hint] at hdec
  rw [show r3MildDecodedVelocity u t = r3H3ToL2Operator (u t) from rfl, hdec]
  congr 1
  · rw [r3H3ToL2Operator_r3StokesH3Evolution hnu.le ⟨t, ht.1⟩ u₀,
      r3StokesL2Path_of_nonneg hnu.le _ ht.1]
    rw [show r3MildDecodedVelocity u 0 = r3H3ToL2Operator (u 0) from rfl, hu0]
  · refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ t := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with s hs hmem
    have hst : s < t := by
      rw [Set.uIoc_of_le ht.1] at hmem
      exact lt_of_le_of_ne hmem.2 hs
    rw [r3EndpointSafeProjectedDuhamelIntegrand_of_lt hnu t u hst,
      r3H3ToL2Operator_r3StokesH2ToH3Operator hnu (sub_pos.mpr hst),
      r3StokesL2Path_of_nonneg hnu.le _ (sub_nonneg.mpr hst.le)]
    rfl

/-- Joint continuity of the totalized heat action. -/
theorem continuous_r3StokesL2Path_action {ν : ℝ} (hν : 0 ≤ ν) :
    Continuous fun p : ℝ × R3L2Velocity => r3StokesL2Path hν p.2 p.1 := by
  have h : (fun p : ℝ × R3L2Velocity => r3StokesL2Path hν p.2 p.1) =
      (fun q : Set.Ici (0 : ℝ) × R3L2Velocity =>
          r3StokesL2Operator hν q.1.property q.2) ∘
        (fun p : ℝ × R3L2Velocity =>
          ((⟨max 0 p.1, le_max_left 0 p.1⟩ : Set.Ici (0 : ℝ)), p.2)) := rfl
  rw [h]
  exact (continuous_r3StokesL2Operator_action hν).comp
    ((Continuous.subtype_mk (continuous_const.max continuous_fst) _).prodMk continuous_snd)

/-- **Connection to edge 2a (pressure)**: the Helmholtz pressure of the identified
convection source along an arbitrary coordinate trajectory (no mild hypothesis)
satisfies the gradient equation
`∇p = −(I−P)((U·∇)U)` componentwise in `𝓢'`.  Assembling the *unprojected* momentum
equation with this pressure is edge 2b-ii.b and is not claimed here. -/
theorem r3HelmholtzPressure_gradient_trajectoryConvection
    (u : ℝ → R3HsVelocity 3) (t : ℝ) (j : Fin 3) :
    ∂_{r3StdBasis j} (r3HelmholtzPressure (r3DecodedConvectionL2 (u t) (u t))) =
      -(PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayComplementL2 (r3DecodedConvectionL2 (u t) (u t)) : R3L2Velocity) :
          𝓢'(R3, R3C))) :=
  r3HelmholtzPressure_gradient (r3DecodedConvectionL2 (u t) (u t)) j

end

end MNS2
