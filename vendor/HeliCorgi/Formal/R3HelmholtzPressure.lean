import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Formal.R3InversionConsistency
import Formal.R3LerayPointwiseProjectionIdentification

/-!
# Generic Helmholtz pressure reconstruction (Clay semantic-promotion edge 2a)

For an arbitrary `L²` vector source `F`, this file constructs an explicit pressure
tempered distribution from the Leray complement and proves the distributional gradient
identity `∇p = -(I - P)F` componentwise, under the repository's Fourier convention
(`𝐞 = e^{-2πi⟨x,ξ⟩}`, so `𝓕(∂ⱼp) = 2πi ξⱼ 𝓕p`).

Construction: the pressure frequency profile is the explicit scalar
`p̂(ξ) = (-(2πi))⁻¹ · (ξ·𝓕F(ξ)) / ‖ξ‖²` (with Lean's junk value `0` at `ξ = 0`), split
into its unit-ball part (in `L¹`, by Cauchy–Schwarz against the `3`-dimensional
integrability of `‖ξ‖⁻²` on the ball) and its exterior part (in `L²`, since `‖ξ‖⁻¹ ≤ 1`
there); both parts embed into tempered distributions and
`r3HelmholtzPressure F := 𝓕⁻ (embed(low) + embed(high))`.

The gradient theorem is proved entirely at the Schwartz-pairing level (the pattern of the
edge-1a and edge-3b files): both sides of `∂ⱼ p = -(component j of (I-P)F)` are paired
against a test function, moved to the frequency side (`𝓕⁻` of a derivative is an explicit
multiplier; the embedded `L²` complement moves by Plancherel), and the resulting
frequency integrands agree a.e. by the repository's explicit Leray symbol
(`r3LeraySymbolComplex_apply` + `inner_r3FrequencyVectorComplex_eq_rawDivergencePointwise`).

NOT claimed in this pass (per commission): identification of the source with the
Navier–Stokes nonlinearity `(u·∇)u`, any time-dependence, and any mild→strong PDE
statement. No phantom Sobolev inclusion is used; no rapid decay is claimed.
-/

namespace MNS2

open MeasureTheory FourierTransform LineDeriv Real
open scoped FourierTransform SchwartzMap ENNReal

noncomputable section

/-- The embedded complex frequency vector has the same norm as the real frequency. -/
theorem norm_r3FrequencyVectorComplex (ξ : R3) :
    ‖r3FrequencyVectorComplex ξ‖ = ‖ξ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (r3FrequencyVectorComplex ξ) i = ((ξ i : ℝ) : ℂ) from rfl, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Cauchy–Schwarz bound for the raw frequency divergence. -/
theorem norm_r3RawDivergencePointwise_le (ξ : R3) (v : R3C) :
    ‖r3RawDivergencePointwise ξ v‖ ≤ ‖ξ‖ * ‖v‖ := by
  rw [← inner_r3FrequencyVectorComplex_eq_rawDivergencePointwise,
    ← norm_r3FrequencyVectorComplex ξ]
  exact norm_inner_le_norm _ _

/-- The explicit Helmholtz pressure frequency profile of an `L²` source: the raw
frequency divergence of `𝓕F` divided by `-2πi ‖ξ‖²`. -/
def r3PressureFrequency (F : R3L2Velocity) : R3 → ℂ :=
  fun ξ => (-(2 * π * Complex.I))⁻¹ *
    (r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) /
      ((‖ξ‖ ^ 2 : ℝ) : ℂ))

theorem aestronglyMeasurable_r3PressureFrequency (F : R3L2Velocity) :
    AEStronglyMeasurable (r3PressureFrequency F) volume := by
  unfold r3PressureFrequency
  have hcoe : AEStronglyMeasurable ((𝓕 F : R3L2Velocity) : R3 → R3C) volume :=
    Lp.aestronglyMeasurable (𝓕 F)
  have hraw : AEStronglyMeasurable
      (fun ξ : R3 =>
        r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ)) volume := by
    unfold r3RawDivergencePointwise
    have hcomp : ∀ i : Fin 3, AEStronglyMeasurable
        (fun ξ : R3 => (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) i) volume := fun i =>
      ((EuclideanSpace.proj i : R3C →L[ℂ] ℂ).continuous).comp_aestronglyMeasurable hcoe
    have hcoord : ∀ i : Fin 3, AEStronglyMeasurable
        (fun ξ : R3 => ((ξ i : ℝ) : ℂ)) volume := fun i =>
      (Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous)).aestronglyMeasurable
    exact (((hcoord 0).mul (hcomp 0)).add ((hcoord 1).mul (hcomp 1))).add
      ((hcoord 2).mul (hcomp 2))
  have hden : AEStronglyMeasurable (fun ξ : R3 => (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) volume := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp (measurable_norm.pow_const 2)).inv
  have hprod : AEStronglyMeasurable (fun ξ : R3 => (-(2 * (π : ℂ) * Complex.I))⁻¹ *
      (r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) *
        (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹)) volume :=
    (hraw.mul hden).const_mul _
  exact hprod.congr (Filter.Eventually.of_forall fun ξ => by simp only [div_eq_mul_inv])

/-- The pressure frequency profile obeys the Riesz-kernel bound
`‖p̂(ξ)‖ ≤ (2π)⁻¹ ‖ξ‖⁻¹ ‖𝓕F(ξ)‖`. -/
theorem norm_r3PressureFrequency_le (F : R3L2Velocity) (ξ : R3) :
    ‖r3PressureFrequency F ξ‖ ≤
      (2 * π)⁻¹ * (‖ξ‖⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) := by
  unfold r3PressureFrequency
  rcases eq_or_ne ξ 0 with hξ | hξ
  · subst hξ
    have hzero : r3RawDivergencePointwise (0 : R3)
        (((𝓕 F : R3L2Velocity) : R3 → R3C) 0) = 0 := by
      unfold r3RawDivergencePointwise
      norm_num [show ((0 : R3) 0 : ℝ) = 0 from rfl, show ((0 : R3) 1 : ℝ) = 0 from rfl,
        show ((0 : R3) 2 : ℝ) = 0 from rfl]
    rw [hzero]
    simp
  · have hnorm : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
    rw [norm_mul, norm_inv, norm_div, Complex.norm_real]
    have hconst : ‖-(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
      simp [Real.pi_nonneg]
    rw [hconst]
    have hbound := norm_r3RawDivergencePointwise_le ξ
      (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ)
    have hden : ‖(‖ξ‖ ^ 2 : ℝ)‖ = ‖ξ‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hden]
    calc (2 * π)⁻¹ *
        (‖r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ)‖ / ‖ξ‖ ^ 2)
        ≤ (2 * π)⁻¹ *
          ((‖ξ‖ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) / ‖ξ‖ ^ 2) := by
          gcongr
      _ = (2 * π)⁻¹ * (‖ξ‖⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) := by
          field_simp

/-- The unit-ball (low-frequency) part of the pressure profile. -/
def r3PressureFrequencyLow (F : R3L2Velocity) : R3 → ℂ :=
  (Metric.ball (0 : R3) 1).indicator (r3PressureFrequency F)

/-- The exterior (high-frequency) part of the pressure profile. -/
def r3PressureFrequencyHigh (F : R3L2Velocity) : R3 → ℂ :=
  ((Metric.ball (0 : R3) 1)ᶜ).indicator (r3PressureFrequency F)

theorem r3PressureFrequency_low_add_high (F : R3L2Velocity) (ξ : R3) :
    r3PressureFrequencyLow F ξ + r3PressureFrequencyHigh F ξ = r3PressureFrequency F ξ := by
  unfold r3PressureFrequencyLow r3PressureFrequencyHigh
  exact congrFun (Set.indicator_self_add_compl (Metric.ball (0 : R3) 1)
    (r3PressureFrequency F)) ξ

/-- The inverse norm is square integrable on the unit ball in dimension three
(equivalently, `‖ξ‖⁻²` is integrable there). -/
theorem integrableOn_inv_norm_sq_ball :
    IntegrableOn (fun ξ : R3 => (‖ξ‖⁻¹) ^ 2) (Metric.ball (0 : R3) 1) volume := by
  refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure R3))
    (by norm_num [R3]) (α := 2) (C := 1) (by norm_num [R3]) ?_ ?_
  · filter_upwards with ξ
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      norm_num [Real.zero_rpow]
    · have h : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul,
        Real.rpow_neg h.le, Real.rpow_two]
      rw [inv_pow]
  · exact ((measurable_norm.inv.pow_const 2)).aestronglyMeasurable

/-- **The low-frequency pressure piece is integrable** (Cauchy–Schwarz on the ball). -/
theorem integrable_r3PressureFrequencyLow (F : R3L2Velocity) :
    Integrable (r3PressureFrequencyLow F) volume := by
  unfold r3PressureFrequencyLow
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  have h1 : MemLp (fun ξ : R3 => ‖ξ‖⁻¹) 2
      (volume.restrict (Metric.ball (0 : R3) 1)) := by
    have hmeas : AEStronglyMeasurable (fun ξ : R3 => ‖ξ‖⁻¹)
        (volume.restrict (Metric.ball (0 : R3) 1)) :=
      (measurable_norm.inv).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    exact integrableOn_inv_norm_sq_ball
  have h2 : MemLp (fun ξ : R3 => ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) 2
      (volume.restrict (Metric.ball (0 : R3) 1)) :=
    ((Lp.memLp (𝓕 F)).norm).mono_measure Measure.restrict_le_self
  have hmajor : Integrable
      (fun ξ : R3 => (2 * π)⁻¹ * (‖ξ‖⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖))
      (volume.restrict (Metric.ball (0 : R3) 1)) := by
    have hone : MemLp
        (fun ξ : R3 => ‖ξ‖⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) 1
        (volume.restrict (Metric.ball (0 : R3) 1)) := h2.mul h1
    exact (memLp_one_iff_integrable.mp hone).const_mul _
  refine Integrable.mono' hmajor
    ((aestronglyMeasurable_r3PressureFrequency F).mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall fun ξ => ?_)
  exact norm_r3PressureFrequency_le F ξ

/-- **The high-frequency pressure piece is square integrable.** -/
theorem memLp_two_r3PressureFrequencyHigh (F : R3L2Velocity) :
    MemLp (r3PressureFrequencyHigh F) 2 volume := by
  have hmeas : AEStronglyMeasurable (r3PressureFrequencyHigh F) volume :=
    (aestronglyMeasurable_r3PressureFrequency F).indicator
      Metric.isOpen_ball.measurableSet.compl
  refine MemLp.of_le (((Lp.memLp (𝓕 F)).norm).const_mul ((2 * π)⁻¹)) hmeas
    (Filter.Eventually.of_forall fun ξ => ?_)
  unfold r3PressureFrequencyHigh
  by_cases hmem : ξ ∈ (Metric.ball (0 : R3) 1)ᶜ
  case neg =>
    rw [Set.indicator_of_notMem hmem]
    simp only [norm_zero, Real.norm_eq_abs]
    positivity
  case pos =>
    rw [Set.indicator_of_mem hmem]
    have hξ : (1 : ℝ) ≤ ‖ξ‖ := by
      have hnot : ¬ dist ξ 0 < 1 := by
        simpa [Metric.mem_ball] using hmem
      simpa [dist_eq_norm] using not_lt.mp hnot
    calc ‖r3PressureFrequency F ξ‖
        ≤ (2 * π)⁻¹ * (‖ξ‖⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) :=
          norm_r3PressureFrequency_le F ξ
      _ ≤ (2 * π)⁻¹ * (1 * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖) := by
          gcongr
          exact inv_le_one_of_one_le₀ hξ
      _ ≤ ‖(2 * π)⁻¹ * ‖((𝓕 F : R3L2Velocity) : R3 → R3C) ξ‖‖ := by
          rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The low-frequency pressure piece bundled in `L¹`. -/
def r3PressureFrequencyLowL1 (F : R3L2Velocity) : Lp ℂ 1 (volume : Measure R3) :=
  (memLp_one_iff_integrable.mpr (integrable_r3PressureFrequencyLow F)).toLp
    (r3PressureFrequencyLow F)

/-- The high-frequency pressure piece bundled in `L²`. -/
def r3PressureFrequencyHighL2 (F : R3L2Velocity) : Lp ℂ 2 (volume : Measure R3) :=
  (memLp_two_r3PressureFrequencyHigh F).toLp (r3PressureFrequencyHigh F)

/-- **An explicit Helmholtz pressure witness for an `L²` source**: the inverse Fourier
transform of the (low + high) embedded pressure frequency profile, as a tempered
distribution — the canonical `‖ξ‖⁻²`-normalized choice (junk value `0` at `ξ = 0`);
the gradient identity below determines it up to additive constants (a nonconstant
harmonic distribution has nonzero gradient; the weaker induced Poisson equation
`Δp = −∇·F` would determine it only up to harmonic terms). -/
def r3HelmholtzPressure (F : R3L2Velocity) : 𝓢'(R3, ℂ) :=
  𝓕⁻ (((r3PressureFrequencyLowL1 F : Lp ℂ 1 (volume : Measure R3)) : 𝓢'(R3, ℂ)) +
    ((r3PressureFrequencyHighL2 F : Lp ℂ 2 (volume : Measure R3)) : 𝓢'(R3, ℂ)))

/-- The Leray complement `(I - P)F` of an `L²` source. -/
def r3LerayComplementL2 (F : R3L2Velocity) : R3L2Velocity :=
  F - r3LerayL2Operator F

/-- Almost-everywhere frequency realization of the Leray complement: the gradient part
of the Helmholtz decomposition. -/
theorem fourier_r3LerayComplementL2_ae (F : R3L2Velocity) :
    ((𝓕 (r3LerayComplementL2 F) : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun ξ =>
        (r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) /
            ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • r3FrequencyVectorComplex ξ := by
  have hsub : 𝓕 (r3LerayComplementL2 F) = 𝓕 F - 𝓕 (r3LerayL2Operator F) := by
    unfold r3LerayComplementL2
    exact (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C).map_sub F (r3LerayL2Operator F)
  rw [hsub]
  have hP := fourier_r3LerayL2Operator_ae F
  filter_upwards [MeasureTheory.Lp.coeFn_sub (𝓕 F) (𝓕 (r3LerayL2Operator F)), hP]
    with ξ hξsub hξP
  rw [hξsub]
  have hPnote : ((𝓕 (r3LerayL2Operator F) : R3L2Velocity) : R3 → R3C) ξ =
      r3LeraySymbolComplex ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) := hξP
  rw [Pi.sub_apply, hPnote, r3LeraySymbolComplex_apply, sub_sub_cancel,
    inner_r3FrequencyVectorComplex_eq_rawDivergencePointwise,
    norm_r3FrequencyVectorComplex]

/-- **Generic Helmholtz pressure reconstruction (Clay semantic-promotion edge 2a).**
For every `L²` source `F` and every coordinate `j`, the distributional partial
derivative of the explicit Helmholtz pressure is the negative of the `j`-th component
of the embedded Leray complement: `∇ (r3HelmholtzPressure F) = -(I - P)F`,
componentwise, in `𝓢'`. Edge 2a only: `F` is an arbitrary `L²` field, so nothing here
identifies `F` with the Navier–Stokes nonlinearity `(u·∇)u`; edge 2 proper —
momentum-equation semantics with this pressure witness — remains open. -/
theorem r3HelmholtzPressure_gradient (F : R3L2Velocity) (j : Fin 3) :
    ∂_{r3StdBasis j} (r3HelmholtzPressure F) =
      -(PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C))) := by
  ext φ
  -- The test multiplier: `𝓕⁻ (∂ⱼ φ) = -(2πI) • ξⱼ • 𝓕⁻ φ`.
  have hχ : 𝓕⁻ (∂_{r3StdBasis j} φ) =
      -(2 * π * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · (r3StdBasis j)) (𝓕⁻ φ) :=
    SchwartzMap.fourierInv_lineDerivOp_eq φ (r3StdBasis j)
  -- Left side: pairing of the pressure with `-∂ⱼφ`, moved to the frequency side.
  have hL : (∂_{r3StdBasis j} (r3HelmholtzPressure F)) φ =
      -(∫ ξ : R3,
          (-(2 * π * Complex.I) •
            SchwartzMap.smulLeftCLM ℂ (inner ℝ · (r3StdBasis j)) (𝓕⁻ φ)) ξ *
            r3PressureFrequency F ξ) := by
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
    congr 1
    unfold r3HelmholtzPressure
    rw [TemperedDistribution.fourierInv_apply, hχ]
    set χ : 𝓢(R3, ℂ) :=
      -(2 * π * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · (r3StdBasis j)) (𝓕⁻ φ) with hχdef
    rw [add_apply]
    rw [MeasureTheory.Lp.toTemperedDistribution_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hlow : (∫ ξ : R3, χ ξ • ((r3PressureFrequencyLowL1 F :
        Lp ℂ 1 (volume : Measure R3)) : R3 → ℂ) ξ) =
        ∫ ξ : R3, χ ξ * r3PressureFrequencyLow F ξ := by
      refine integral_congr_ae ?_
      unfold r3PressureFrequencyLowL1
      filter_upwards [MemLp.coeFn_toLp
        (memLp_one_iff_integrable.mpr (integrable_r3PressureFrequencyLow F))] with ξ hξ
      rw [hξ, smul_eq_mul]
    have hhigh : (∫ ξ : R3, χ ξ • ((r3PressureFrequencyHighL2 F :
        Lp ℂ 2 (volume : Measure R3)) : R3 → ℂ) ξ) =
        ∫ ξ : R3, χ ξ * r3PressureFrequencyHigh F ξ := by
      refine integral_congr_ae ?_
      unfold r3PressureFrequencyHighL2
      filter_upwards [MemLp.coeFn_toLp (memLp_two_r3PressureFrequencyHigh F)] with ξ hξ
      rw [hξ, smul_eq_mul]
    rw [hlow, hhigh, ← MeasureTheory.integral_add]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show χ ξ * r3PressureFrequencyLow F ξ + χ ξ * r3PressureFrequencyHigh F ξ =
        χ ξ * r3PressureFrequency F ξ
      rw [← mul_add, r3PressureFrequency_low_add_high]
    · have hone : MemLp (fun ξ : R3 => χ ξ * r3PressureFrequencyLow F ξ) 1 volume :=
        (memLp_one_iff_integrable.mpr (integrable_r3PressureFrequencyLow F)).mul
          (χ.memLp ⊤)
      exact memLp_one_iff_integrable.mp hone
    · have hone : MemLp (fun ξ : R3 => χ ξ * r3PressureFrequencyHigh F ξ) 1 volume :=
        (memLp_two_r3PressureFrequencyHigh F).mul (χ.memLp 2)
      exact memLp_one_iff_integrable.mp hone
  -- Right side: pairing of the embedded complement, moved to the frequency side.
  have hR : (-(PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)))) φ =
      -(∫ ξ : R3, (𝓕⁻ φ) ξ *
          (((𝓕 (r3LerayComplementL2 F) : R3L2Velocity) : R3 → R3C) ξ) j) := by
    rw [neg_apply]
    congr 1
    have hpair : ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)) φ =
        ∫ ξ : R3, (𝓕⁻ φ) ξ •
          ((𝓕 (r3LerayComplementL2 F) : R3L2Velocity) : R3 → R3C) ξ := by
      conv_lhs => rw [show φ = 𝓕 (𝓕⁻ φ) from (fourier_fourierInv_eq φ).symm,
        ← TemperedDistribution.fourier_apply,
        MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      exact MeasureTheory.Lp.toTemperedDistribution_apply _ _
    have hint : Integrable (fun ξ : R3 => (𝓕⁻ φ) ξ •
        ((𝓕 (r3LerayComplementL2 F) : R3L2Velocity) : R3 → R3C) ξ) volume := by
      have hone : MemLp (fun ξ : R3 => (𝓕⁻ φ) ξ •
          ((𝓕 (r3LerayComplementL2 F) : R3L2Velocity) : R3 → R3C) ξ) 1 volume :=
        (Lp.memLp (𝓕 (r3LerayComplementL2 F))).smul ((𝓕⁻ φ).memLp 2)
      exact memLp_one_iff_integrable.mp hone
    have hpost : (PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C))) φ =
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
          (((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)) φ) := rfl
    rw [hpost, hpair, ← ContinuousLinearMap.integral_comp_comm _ hint]
    congr 1
  -- The frequency integrands agree almost everywhere.
  rw [hL, hR]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [fourier_r3LerayComplementL2_ae F] with ξ hξ
  rw [hξ]
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_inner_r3StdBasis j) (𝓕⁻ φ) ξ, inner_r3StdBasis]
  rw [show ((r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) /
      ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • r3FrequencyVectorComplex ξ) j =
      (r3RawDivergencePointwise ξ (((𝓕 F : R3L2Velocity) : R3 → R3C) ξ) /
        ((‖ξ‖ ^ 2 : ℝ) : ℂ)) * ((ξ j : ℝ) : ℂ) from by
    rw [PiLp.smul_apply, smul_eq_mul]
    rfl]
  unfold r3PressureFrequency
  have h2πI : (-(2 * (π : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp
  simp only [Complex.real_smul]
  ring

/-- Coordinate bound on `R3`: each coordinate is dominated by the Euclidean norm. -/
theorem abs_coord_le_norm_r3 (v : R3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : |v i| ^ 2 ≤ ∑ j : Fin 3, ‖v j‖ ^ 2 := by
    have := Finset.single_le_sum
      (f := fun j : Fin 3 => ‖v j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    simpa [Real.norm_eq_abs, sq_abs] using this
  calc |v i| = Real.sqrt (|v i| ^ 2) := by
        rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt hle

/-- **Non-vacuity witness**: the Leray complement is not identically zero — the
Helmholtz gradient equation `∇p = -(I-P)F` is not the trivial identity `0 = -0`.
The witness is the continuous compactly supported field
`f(ξ) = max (1/4 - dist ξ c) 0 • e₀` (with `c = e₀`), pushed to physical space by the
inverse `L²` Fourier transform; its raw frequency divergence `ξ₀ ψ(ξ)` is nonzero on a
ball of positive measure. -/
theorem exists_r3LerayComplementL2_ne_zero :
    ∃ F : R3L2Velocity, r3LerayComplementL2 F ≠ 0 := by
  classical
  set c : R3 := EuclideanSpace.single 0 (1 : ℝ) with hc
  set ψ : R3 → ℝ := fun ξ => max (1 / 4 - dist ξ c) 0 with hψ
  have hψcont : Continuous ψ := by
    rw [hψ]
    fun_prop
  set fvec : R3 → R3C := fun ξ => ((ψ ξ : ℝ) : ℂ) • EuclideanSpace.single 0 (1 : ℂ)
    with hfvec
  have hfcont : Continuous fvec := by
    rw [hfvec]
    exact (Complex.continuous_ofReal.comp hψcont).smul continuous_const
  have hfsupp : HasCompactSupport fvec := by
    refine HasCompactSupport.intro (isCompact_closedBall c (1 / 4)) fun ξ hξ => ?_
    have hdist : ¬ dist ξ c ≤ 1 / 4 := by
      simpa [Metric.mem_closedBall] using hξ
    have hzero : ψ ξ = 0 := by
      rw [hψ]
      have : 1 / 4 - dist ξ c ≤ 0 := by linarith [not_le.mp hdist]
      exact max_eq_right this
    simp [hfvec, hzero]
  have hfmem : MemLp fvec 2 (volume : Measure R3) :=
    hfcont.memLp_of_hasCompactSupport hfsupp
  set G : R3L2Velocity := hfmem.toLp fvec with hG
  refine ⟨𝓕⁻ G, fun hzero => ?_⟩
  -- complement zero forces membership in the solenoidal submodule
  have hmem : (𝓕⁻ G : R3L2Velocity) ∈ r3L2SolenoidalSubmodule := by
    have heq : (𝓕⁻ G : R3L2Velocity) = r3LerayL2Operator (𝓕⁻ G) := by
      have := sub_eq_zero.mp hzero
      exact this
    rw [heq]
    exact r3LerayL2Operator_mem_solenoidal (𝓕⁻ G)
  -- membership gives a.e. vanishing raw divergence of the Fourier data
  have hker : r3NormalizedDivergenceFrequencyAux (𝓕 (𝓕⁻ G : R3L2Velocity)) = 0 := by
    have h := LinearMap.mem_ker.mp hmem
    simpa [r3NormalizedDivergenceL2OperatorAux] using h
  have hFF : 𝓕 (𝓕⁻ G : R3L2Velocity) = G := fourier_fourierInv_eq G
  have hraw : ∀ᵐ ξ : R3 ∂(volume : Measure R3),
      r3RawDivergencePointwise ξ ((G : R3 → R3C) ξ) = 0 := by
    have hae := r3NormalizedDivergenceFrequencyAux_ae G
    have hzeroae : (r3NormalizedDivergenceFrequencyAux G : R3 → ℂ) =ᵐ[volume] 0 := by
      rw [← hFF] at hG ⊢
      rw [hker]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [hae, hzeroae] with ξ h1 h2
    have hnorm : r3NormalizedDivergencePointwise ξ ((G : R3 → R3C) ξ) = 0 := by
      rw [← h1]
      simpa using h2
    exact (r3NormalizedDivergencePointwise_eq_zero_iff ξ _).mp hnorm
  -- transfer to the explicit witness profile
  have hprofile : ∀ᵐ ξ : R3 ∂(volume : Measure R3),
      ((ξ 0 : ℝ) : ℂ) * ((ψ ξ : ℝ) : ℂ) = 0 := by
    filter_upwards [hraw, MemLp.coeFn_toLp hfmem] with ξ h1 h2
    have hval : r3RawDivergencePointwise ξ (fvec ξ) = ((ξ 0 : ℝ) : ℂ) * ((ψ ξ : ℝ) : ℂ) := by
      rw [hfvec]
      unfold r3RawDivergencePointwise
      simp
    rw [← hval, ← h2]
    exact h1
  -- but the profile is nonzero on a ball of positive measure
  have hball : Metric.ball c (1 / 8) ⊆
      {ξ : R3 | ¬ (((ξ 0 : ℝ) : ℂ) * ((ψ ξ : ℝ) : ℂ) = 0)} := by
    intro ξ hξ
    have hdist : dist ξ c < 1 / 8 := Metric.mem_ball.mp hξ
    have hψpos : 0 < ψ ξ := by
      rw [hψ]
      have : (0 : ℝ) < 1 / 4 - dist ξ c := by linarith [dist_nonneg (x := ξ) (y := c)]
      exact lt_max_of_lt_left this
    have hcoord : (0 : ℝ) < ξ 0 := by
      have hc0 : c 0 = 1 := by
        rw [hc]
        simp
      have hbound : |ξ 0 - c 0| ≤ ‖ξ - c‖ := by
        have := abs_coord_le_norm_r3 (ξ - c) 0
        simpa using this
      have hdist' : ‖ξ - c‖ = dist ξ c := (dist_eq_norm ξ c).symm
      rw [hdist', hc0] at hbound
      have := abs_le.mp hbound
      linarith [this.1]
    intro habs
    rcases mul_eq_zero.mp habs with h | h
    · exact absurd (Complex.ofReal_eq_zero.mp h) (ne_of_gt hcoord)
    · exact absurd (Complex.ofReal_eq_zero.mp h) (ne_of_gt hψpos)
  have hpos : (0 : ℝ≥0∞) < volume (Metric.ball c (1 / 8)) :=
    Metric.measure_ball_pos volume c (by norm_num)
  have hnull : volume {ξ : R3 | ¬ (((ξ 0 : ℝ) : ℂ) * ((ψ ξ : ℝ) : ℂ) = 0)} = 0 :=
    hprofile
  exact absurd (measure_mono_null hball hnull) (ne_of_gt hpos)
