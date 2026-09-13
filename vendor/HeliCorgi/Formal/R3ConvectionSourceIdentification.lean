import Formal.R3HelmholtzPressure
import Formal.R3ProjectedSobolevConvection

/-!
# General `H³` convection source identification (Clay semantic-promotion edge 2b-i)

The completed bilinear coordinate operator `r3ConvectionH3ToH2` was built by abstract
extension from the Schwartz core, so a Clay-grade reading needs an *identification*: for
arbitrary order-three Bessel coordinates `u, v`, what physical field does its decoded
output actually equal?  This file answers that with the literal physical convection of the
decoded representatives.

For an order-three coordinate `f`, the decoded physical representative is
`U_f := 𝓕⁻ (r3DecodedFrequency 3 f)` — the explicit inverse-Fourier integral of edges
1b/3a/3b, which is `C¹` with the explicit Fréchet derivative
`r3RepresentativeDeriv (r3DecodedFrequency 3 f) x` at every point
(`hasFDerivAt_r3PhysicalRepresentative`).  The pointwise convection field

`r3DecodedConvectionPointwise u v x = ∑ i, (U_u x)ᵢ • (∂ᵢ U_v)(x)`

(with `∂ᵢ` the explicit derivative applied to the `i`-th standard basis vector, equal to
the genuine `fderiv` by `r3DecodedConvectionPointwise_eq_fderiv`) is square integrable and
bundles as `r3DecodedConvectionL2 u v : L²(R³; ℂ³)`.  The main theorem

`r3H2ToL2Operator_r3ConvectionH3ToH2 :
  r3H2ToL2Operator (r3ConvectionH3ToH2 u v) = r3DecodedConvectionL2 u v`

identifies the genuine `J⁻²` decode of the completed coordinate operator with this
pointwise-constructed `(U·∇)V` for **all** `u, v`, by continuity from the Schwartz core:
on canonical Schwartz coordinates both sides are literal physical convection
(`r3H2ToL2Operator_r3SchwartzToHsCLM` + `r3ConvectionH3ToH2_apply_schwartz` on the
coordinate side; exact Fourier inversion on the decoded side), and both sides are
continuous in each slot (the coordinate side is a composition of continuous linear maps;
the decoded side is realized as `∑ i, (U_u)ᵢ^{L∞} • Dᵢ v` with `Dᵢ` an explicit bounded
frequency-multiplier operator, plus a quantitative Cauchy–Schwarz `L¹` decoder bound for
the Lipschitz estimate in the first slot).

The projected corollary `r3H2ToL2Operator_r3ProjectedConvectionH3ToH2` identifies the
decode of `r3ProjectedConvectionH3ToH2 u v` with `P((U·∇)V)`, and
`r3HelmholtzPressure_gradient_decodedConvection` instantiates the edge-2a Helmholtz
pressure gradient theorem at the source `F := (U·∇)V`, exhibiting the pressure witness for
the identified convection source — the shape edge 2b proper will consume.

NOT claimed in this pass (per commission): any time dependence, differentiation of the
Duhamel formula, or a mild→strong PDE statement.  The definitional equality
`R3HsVelocity s = R3L2Velocity` is nowhere used as a physical Sobolev embedding: every
physical object passes through the explicit decoders (`r3DecodedFrequency`,
`r3H2ToL2Operator`), and all regularity is carried by explicit integrability statements.
No rapid decay is claimed.
-/

namespace MNS2

open MeasureTheory FourierTransform Real VectorFourier LineDeriv
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

/-! ## Pointwise and integral preliminaries -/

/-- Coordinate bound on `R3C`: each component is dominated by the Euclidean norm. -/
theorem norm_coord_le_norm_r3C (v : R3C) (i : Fin 3) : ‖v i‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have hle : ‖v i‖ ^ 2 ≤ ∑ j : Fin 3, ‖v j‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun j : Fin 3 => ‖v j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  calc ‖v i‖ = Real.sqrt (‖v i‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt hle

/-- The explicit physical representative only depends on the frequency data almost
everywhere (it is an integral). -/
theorem r3PhysicalRepresentative_congr_ae {g₁ g₂ : R3 → R3C}
    (h : g₁ =ᵐ[volume] g₂) :
    r3PhysicalRepresentative g₁ = r3PhysicalRepresentative g₂ := by
  funext x
  unfold r3PhysicalRepresentative
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  refine integral_congr_ae ?_
  filter_upwards [h] with ξ hξ
  rw [hξ]

/-- The sup bound for the inverse Fourier integral: the physical representative is
everywhere dominated by the `L¹` norm of the frequency data. -/
theorem norm_r3PhysicalRepresentative_le (g : R3 → R3C) (x : R3) :
    ‖r3PhysicalRepresentative g x‖ ≤ ∫ ξ : R3, ‖g ξ‖ := by
  unfold r3PhysicalRepresentative
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp [Circle.norm_smul]

/-! ## Quantitative decoder `L¹` bound (Cauchy–Schwarz, order three) -/

/-- The complex order-three inverse Bessel weight is square integrable in dimension
three. -/
theorem r3H3InverseBesselWeightComplex_memLp_two :
    MemLp r3H3InverseBesselWeightComplex 2 (volume : Measure R3) := by
  have heq : (fun ξ : R3 => ((r3InverseBesselWeight 3 ξ : ℝ) : ℂ)) =
      r3H3InverseBesselWeightComplex := by
    funext ξ
    exact r3InverseBesselWeight_eq_sobolevWeight 3 ξ
  rw [← heq]
  exact memLp_two_r3InverseBesselWeight_three.ofReal

/-- The complex order-three inverse Bessel weight as an `L²` scalar field. -/
def r3H3InverseBesselWeightL2 : Lp ℂ 2 (volume : Measure R3) :=
  r3H3InverseBesselWeightComplex_memLp_two.toLp r3H3InverseBesselWeightComplex

theorem r3H3InverseBesselWeightL2_ae :
    r3H3InverseBesselWeightL2 =ᵐ[volume] r3H3InverseBesselWeightComplex :=
  MemLp.coeFn_toLp r3H3InverseBesselWeightComplex_memLp_two

/-- **Quantitative decoder `L¹` bound**: the `L¹` norm of the order-three decoded
frequency data is controlled by the coordinate `L²` norm, with the fixed Cauchy–Schwarz
constant `‖J⁻³‖_{L²}`. -/
theorem integral_norm_r3DecodedFrequency_le (f : R3L2Velocity) :
    (∫ ξ : R3, ‖r3DecodedFrequency 3 f ξ‖) ≤ ‖r3H3InverseBesselWeightL2‖ * ‖f‖ := by
  have hint : Integrable (r3DecodedFrequency 3 f) volume := integrable_r3DecodedFrequency f
  have hL1 : hint.toL1 (r3DecodedFrequency 3 f) =
      r3H3InverseBesselWeightL2 • (𝓕 f : R3L2Velocity) := by
    apply Lp.ext
    filter_upwards [hint.coeFn_toL1,
      Lp.coeFn_lpSMul (r := (1 : ENNReal)) r3H3InverseBesselWeightL2 (𝓕 f : R3L2Velocity),
      r3H3InverseBesselWeightL2_ae] with ξ h1 h2 h3
    rw [h1, h2, Pi.smul_apply', h3]
    unfold r3DecodedFrequency
    rw [r3RealSmul_eq_complexSmul, r3InverseBesselWeight_eq_sobolevWeight]
    rfl
  calc (∫ ξ : R3, ‖r3DecodedFrequency 3 f ξ‖)
      = ‖hint.toL1 (r3DecodedFrequency 3 f)‖ :=
        (L1.norm_of_fun_eq_integral_norm hint).symm
    _ = ‖r3H3InverseBesselWeightL2 • (𝓕 f : R3L2Velocity)‖ := by rw [hL1]
    _ ≤ ‖r3H3InverseBesselWeightL2‖ * ‖(𝓕 f : R3L2Velocity)‖ :=
        MeasureTheory.Lp.norm_smul_le _ _
    _ = ‖r3H3InverseBesselWeightL2‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]

/-- Sup bound for the decoded representative: `‖U_f(x)‖ ≤ ‖J⁻³‖_{L²} ‖f‖` everywhere.
Here `‖f‖` is the coordinate `L²` norm of the stored Bessel coordinate — the bound is the
honest Cauchy–Schwarz route through the explicit `J⁻³ ∈ L²` decoder weight, not a
phantom-order Sobolev-embedding shortcut. -/
theorem norm_r3DecodedRepresentative_le (f : R3HsVelocity 3) (x : R3) :
    ‖r3PhysicalRepresentative (r3DecodedFrequency 3 f) x‖ ≤
      ‖r3H3InverseBesselWeightL2‖ * ‖f‖ :=
  (norm_r3PhysicalRepresentative_le _ x).trans (integral_norm_r3DecodedFrequency_le f)

/-! ## The decoded velocity components as bounded scalar fields -/

theorem continuous_r3DecodedRepresentative (f : R3HsVelocity 3) :
    Continuous (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) :=
  continuous_r3PhysicalRepresentative (integrable_r3DecodedFrequency f)

theorem memLp_top_r3DecodedComponent (f : R3HsVelocity 3) (i : Fin 3) :
    MemLp (fun x : R3 =>
      (r3PhysicalRepresentative (r3DecodedFrequency 3 f) x) i) ⊤ volume := by
  refine memLp_top_of_bound ?_ (‖r3H3InverseBesselWeightL2‖ * ‖f‖)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((EuclideanSpace.proj i : R3C →L[ℂ] ℂ).continuous.comp
      (continuous_r3DecodedRepresentative f)).aestronglyMeasurable
  · exact (norm_coord_le_norm_r3C _ i).trans (norm_r3DecodedRepresentative_le f x)

/-- The `i`-th component of the decoded representative as an `L∞` scalar field. -/
def r3DecodedComponentLpTop (f : R3HsVelocity 3) (i : Fin 3) :
    Lp ℂ ⊤ (volume : Measure R3) :=
  (memLp_top_r3DecodedComponent f i).toLp
    (fun x : R3 => (r3PhysicalRepresentative (r3DecodedFrequency 3 f) x) i)

theorem r3DecodedComponentLpTop_ae (f : R3HsVelocity 3) (i : Fin 3) :
    r3DecodedComponentLpTop f i =ᵐ[volume]
      fun x : R3 => (r3PhysicalRepresentative (r3DecodedFrequency 3 f) x) i :=
  MemLp.coeFn_toLp (memLp_top_r3DecodedComponent f i)

theorem norm_r3DecodedComponentLpTop_le (f : R3HsVelocity 3) (i : Fin 3) :
    ‖r3DecodedComponentLpTop f i‖ ≤ ‖r3H3InverseBesselWeightL2‖ * ‖f‖ := by
  unfold r3DecodedComponentLpTop
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x =>
    (norm_coord_le_norm_r3C _ i).trans (norm_r3DecodedRepresentative_le f x))

/-- The decoded representative is additive-in-differences at every point: decoding and the
inverse Fourier integral are both linear at the level of a.e.-classes and integrals. -/
theorem r3DecodedRepresentative_sub (u u' : R3HsVelocity 3) (x : R3) :
    r3PhysicalRepresentative (r3DecodedFrequency 3 (u - u')) x =
      r3PhysicalRepresentative (r3DecodedFrequency 3 u) x -
        r3PhysicalRepresentative (r3DecodedFrequency 3 u') x := by
  have hae : r3DecodedFrequency 3 (u - u') =ᵐ[volume]
      fun ξ => r3DecodedFrequency 3 u ξ - r3DecodedFrequency 3 u' ξ := by
    have hsub : (𝓕 (u - u') : R3L2Velocity) = 𝓕 u - 𝓕 u' :=
      map_sub (MeasureTheory.Lp.fourierTransformₗᵢ R3 R3C) u u'
    unfold r3DecodedFrequency
    rw [hsub]
    filter_upwards [Lp.coeFn_sub (𝓕 u : R3L2Velocity) (𝓕 u' : R3L2Velocity)] with ξ hξ
    rw [hξ, Pi.sub_apply, smul_sub]
  rw [show r3PhysicalRepresentative (r3DecodedFrequency 3 (u - u')) =
      r3PhysicalRepresentative
        (fun ξ => r3DecodedFrequency 3 u ξ - r3DecodedFrequency 3 u' ξ) from
    r3PhysicalRepresentative_congr_ae hae]
  unfold r3PhysicalRepresentative
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  have hker : ∀ g : R3 → R3C, Integrable g volume →
      Integrable (fun ξ : R3 => 𝐞 (inner ℝ ξ x) • g ξ) volume := by
    intro g hg
    refine Integrable.mono' hg.norm
      (((continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
        hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Circle.norm_smul]
  rw [show (fun ξ : R3 => 𝐞 (inner ℝ ξ x) •
      (r3DecodedFrequency 3 u ξ - r3DecodedFrequency 3 u' ξ)) =
      fun ξ : R3 => 𝐞 (inner ℝ ξ x) • r3DecodedFrequency 3 u ξ -
        𝐞 (inner ℝ ξ x) • r3DecodedFrequency 3 u' ξ from
    funext fun ξ => smul_sub _ _ _]
  exact integral_sub (hker _ (integrable_r3DecodedFrequency u))
    (hker _ (integrable_r3DecodedFrequency u'))

theorem r3DecodedComponentLpTop_sub (u u' : R3HsVelocity 3) (i : Fin 3) :
    r3DecodedComponentLpTop u i - r3DecodedComponentLpTop u' i =
      r3DecodedComponentLpTop (u - u') i := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (r3DecodedComponentLpTop u i) (r3DecodedComponentLpTop u' i),
    r3DecodedComponentLpTop_ae u i, r3DecodedComponentLpTop_ae u' i,
    r3DecodedComponentLpTop_ae (u - u') i] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4, r3DecodedRepresentative_sub u u' x]
  simp

/-! ## Generic `L¹ ∩ L²` inversion consistency (the edge-3b pairing argument, generalized) -/

/-- Pairing a Schwartz test function against the `L²` inverse Fourier transform moves the
transform to the test side (the generic form of the edge-3b `L²` pairing). -/
theorem integral_smul_fourierInvL2 (h : R3L2Velocity) (ψ : 𝓢(R3, ℂ)) :
    ∫ x : R3, ψ x • ((𝓕⁻ h : R3L2Velocity) : R3 → R3C) x =
      ∫ ξ : R3, 𝓕⁻ (⇑ψ) ξ • ((h : R3L2Velocity) : R3 → R3C) ξ := by
  calc ∫ x : R3, ψ x • ((𝓕⁻ h : R3L2Velocity) : R3 → R3C) x
      = ((𝓕⁻ h : R3L2Velocity) : 𝓢'(R3, R3C)) ψ :=
        (MeasureTheory.Lp.toTemperedDistribution_apply _ ψ).symm
    _ = (𝓕⁻ ((h : R3L2Velocity) : 𝓢'(R3, R3C))) ψ := by
        rw [MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq]
    _ = ((h : R3L2Velocity) : 𝓢'(R3, R3C)) (𝓕⁻ ψ) :=
        TemperedDistribution.fourierInv_apply _ ψ
    _ = ∫ ξ : R3, (𝓕⁻ ψ) ξ • ((h : R3L2Velocity) : R3 → R3C) ξ :=
        MeasureTheory.Lp.toTemperedDistribution_apply _ _
    _ = ∫ ξ : R3, 𝓕⁻ (⇑ψ) ξ • ((h : R3L2Velocity) : R3 → R3C) ξ := by
        rw [SchwartzMap.fourierInv_coe]

/-- **Generic `L¹ ∩ L²` inversion consistency**: for a frequency profile that is both
integrable and square integrable, the pointwise inverse Fourier integral is an a.e.
representative of the `L²` inverse transform. -/
theorem r3PhysicalRepresentative_ae_fourierInv {g : R3 → R3C}
    (hg₁ : Integrable g volume) (hg₂ : MemLp g 2 volume) :
    r3PhysicalRepresentative g =ᵐ[volume]
      ((𝓕⁻ (hg₂.toLp g) : R3L2Velocity) : R3 → R3C) := by
  have hloc1 : LocallyIntegrable (r3PhysicalRepresentative g) volume :=
    (continuous_r3PhysicalRepresentative hg₁).locallyIntegrable
  have hloc2 : LocallyIntegrable ((𝓕⁻ (hg₂.toLp g) : R3L2Velocity) : R3 → R3C) volume :=
    (Lp.memLp (𝓕⁻ (hg₂.toLp g) : R3L2Velocity)).locallyIntegrable one_le_two
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun w w_diff w_supp => ?_
  have hw₁ : HasCompactSupport (Complex.ofRealCLM ∘ w) := w_supp.comp_left rfl
  have hw₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ w) := by fun_prop
  have hψcoe : ⇑(hw₁.toSchwartzMap hw₂) = Complex.ofRealCLM ∘ w := rfl
  have hsmul : ∀ F : R3 → R3C,
      (∫ x : R3, w x • F x) = ∫ x : R3, (hw₁.toSchwartzMap hw₂) x • F x := by
    intro F
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hψcoe]
    exact r3RealSmul_eq_complexSmul (w x) (F x)
  rw [hsmul, hsmul,
    integral_smul_r3PhysicalRepresentative hg₁ (hw₁.toSchwartzMap hw₂),
    integral_smul_fourierInvL2 (hg₂.toLp g) (hw₁.toSchwartzMap hw₂)]
  refine integral_congr_ae ?_
  filter_upwards [hg₂.coeFn_toLp] with ξ hξ
  rw [hξ]

/-! ## The explicit derivative as a frequency multiplier -/

/-- The explicit derivative of the physical representative in a standard basis direction
is the physical representative of the `2πiξᵢ`-multiplied frequency profile. -/
theorem r3RepresentativeDeriv_stdBasis {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) (x : R3) (i : Fin 3) :
    r3RepresentativeDeriv g x (r3StdBasis i) =
      r3PhysicalRepresentative
        (fun ξ : R3 => ((2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) • g ξ) x := by
  set h : R3 → R3C := fun ξ => g (-ξ) with hhdef
  have hh₁ : Integrable h volume := r3Integrable_comp_neg hg₁
  have hh₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖h ξ‖) volume :=
    r3WeightedIntegrable_comp_neg hg₂
  have hF : Integrable (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ) volume := by
    refine Integrable.mono'
      (hh₂.const_mul (2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖))
      hh₁.aestronglyMeasurable.fourierSMulRight
      (Filter.Eventually.of_forall fun ξ => ?_)
    calc ‖fourierSMulRight (innerSL ℝ) h ξ‖
        ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ‖ξ‖ * ‖h ξ‖ :=
          norm_fourierSMulRight_le _ _ _
      _ = 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * (‖ξ‖ * ‖h ξ‖) := by ring
  have heval : r3RepresentativeDeriv g x (r3StdBasis i) =
      𝓕 (fun ξ : R3 => fourierSMulRight (innerSL ℝ) h ξ (r3StdBasis i)) x :=
    Real.fourier_continuousLinearMap_apply hF
  rw [heval, r3PhysicalRepresentative_eq_fourier_comp_neg]
  refine congrArg (fun F : R3 → R3C => 𝓕 F x) (funext fun ξ => ?_)
  have hinner : (innerSL ℝ) ξ (r3StdBasis i) = ξ i := by
    simpa using inner_r3StdBasis ξ i
  have hnegcoord : (((-ξ : R3) i : ℝ) : ℂ) = -((ξ i : ℝ) : ℂ) := by
    push_cast [show ((-ξ : R3) i : ℝ) = -(ξ i) from rfl]
    ring
  rw [fourierSMulRight_apply, hinner, hnegcoord]
  rw [r3RealSmul_eq_complexSmul, smul_smul]
  congr 1
  ring

/-- The frequency weight of the decoded coordinate derivative: `2πi ξᵢ (1+‖ξ‖²)^{-3/2}`. -/
def r3DecodedDerivativeWeight (i : Fin 3) : R3 → ℂ :=
  fun ξ => (2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ) * r3H3InverseBesselWeightComplex ξ

theorem continuous_r3DecodedDerivativeWeight (i : Fin 3) :
    Continuous (r3DecodedDerivativeWeight i) := by
  unfold r3DecodedDerivativeWeight
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous))).mul
    continuous_r3H3InverseBesselWeightComplex

/-- The derivative weight is uniformly bounded: one frequency power is absorbed by the
order-three inverse Bessel weight. -/
theorem norm_r3DecodedDerivativeWeight_le (i : Fin 3) (ξ : R3) :
    ‖r3DecodedDerivativeWeight i ξ‖ ≤ 2 * π := by
  unfold r3DecodedDerivativeWeight
  have hb : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hconst : ‖2 * (π : ℂ) * Complex.I‖ = 2 * π := by
    simp [Real.pi_nonneg]
  have hcoord : ‖((ξ i : ℝ) : ℂ)‖ = |ξ i| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hweight : ‖r3H3InverseBesselWeightComplex ξ‖ = (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) := by
    unfold r3H3InverseBesselWeightComplex r3SobolevWeightComplex
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hb.le _)]
  have hξi : |ξ i| ≤ (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    refine (abs_coord_le_norm_r3 ξ i).trans ?_
    rw [← Real.sqrt_eq_rpow]
    calc ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖ξ‖])
  have hcollapse : (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) =
      (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hb]
    norm_num
  have hle1 : ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-1 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)
  calc ‖2 * (π : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ) * r3H3InverseBesselWeightComplex ξ‖
      = (2 * π) * (|ξ i| * ((1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2))) := by
        rw [norm_mul, norm_mul, hconst, hcoord, hweight, mul_assoc]
    _ ≤ (2 * π) * ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) * ((1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2))) := by
        have hwnn : (0 : ℝ) ≤ (1 + ‖ξ‖ ^ 2) ^ ((-3 : ℝ) / 2) := Real.rpow_nonneg hb.le _
        have := mul_le_mul_of_nonneg_right hξi hwnn
        nlinarith [Real.pi_nonneg]
    _ ≤ (2 * π) * 1 := by
        rw [hcollapse]
        have := hle1
        nlinarith [Real.pi_nonneg]
    _ = 2 * π := mul_one _

theorem r3DecodedDerivativeWeight_memLp_top (i : Fin 3) :
    MemLp (r3DecodedDerivativeWeight i) ⊤ (volume : Measure R3) :=
  memLp_top_of_bound (continuous_r3DecodedDerivativeWeight i).aestronglyMeasurable
    (2 * π) (Filter.Eventually.of_forall (norm_r3DecodedDerivativeWeight_le i))

/-- The derivative weight bundled as an `L∞` multiplier element. -/
def r3DecodedDerivativeWeightLpTop (i : Fin 3) : Lp ℂ ⊤ (volume : Measure R3) :=
  (r3DecodedDerivativeWeight_memLp_top i).toLp (r3DecodedDerivativeWeight i)

theorem r3DecodedDerivativeWeightLpTop_ae (i : Fin 3) :
    r3DecodedDerivativeWeightLpTop i =ᵐ[volume] r3DecodedDerivativeWeight i :=
  MemLp.coeFn_toLp (r3DecodedDerivativeWeight_memLp_top i)

/-- The decoded coordinate-derivative operator: conjugation of the bounded multiplier
`2πi ξᵢ J⁻³` by the Fourier transform.  For an order-three coordinate `v` this realizes
`∂ᵢ U_v` in `L²` (`r3DecodedDerivativeL2Operator_ae_deriv`). -/
def r3DecodedDerivativeL2Operator (i : Fin 3) :
    R3HsVelocity 3 →L[ℂ] R3L2Velocity :=
  fourierInvCLM ℂ R3L2Velocity ∘L
    r3L2ScalarMultiplier (r3DecodedDerivativeWeightLpTop i) ∘L
      fourierCLM ℂ R3L2Velocity

/-- Exact a.e. pointwise realization of the bundled derivative-weight multiplier. -/
theorem r3DecodedDerivativeMultiplier_ae (i : Fin 3) (g : R3L2Velocity) :
    r3L2ScalarMultiplier (r3DecodedDerivativeWeightLpTop i) g =ᵐ[volume]
      fun ξ => r3DecodedDerivativeWeight i ξ • g ξ := by
  rw [r3L2ScalarMultiplier_apply]
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  filter_upwards
    [Lp.coeFn_lpSMul (r := (2 : ENNReal)) (r3DecodedDerivativeWeightLpTop i) g,
      r3DecodedDerivativeWeightLpTop_ae i]
    with ξ hmul hweight
  rw [hmul]
  exact congrArg (fun c : ℂ => c • g ξ) hweight

/-- The multiplied frequency profile of the derivative equals the `2πiξᵢ`-scaling of the
decoded frequency data. -/
theorem r3DecodedDerivativeWeight_smul_fourier (i : Fin 3) (v : R3HsVelocity 3) (ξ : R3) :
    r3DecodedDerivativeWeight i ξ • ((𝓕 v : R3L2Velocity) : R3 → R3C) ξ =
      ((2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) • r3DecodedFrequency 3 v ξ := by
  unfold r3DecodedDerivativeWeight r3DecodedFrequency
  rw [r3RealSmul_eq_complexSmul, smul_smul, r3InverseBesselWeight_eq_sobolevWeight]
  rfl

/-- The `2πiξᵢ`-scaled decoded frequency data is integrable (edge 3a's weighted bound). -/
theorem integrable_r3DecodedDerivativeProfile (i : Fin 3) (v : R3HsVelocity 3) :
    Integrable (fun ξ : R3 =>
      ((2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) • r3DecodedFrequency 3 v ξ)
      volume := by
  have hsc : AEStronglyMeasurable
      (fun ξ : R3 => (2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) volume :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).continuous))).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (r3DecodedFrequency 3 v) volume :=
    (integrable_r3DecodedFrequency v).aestronglyMeasurable
  refine Integrable.mono'
    ((integrable_weighted_r3DecodedFrequency v).const_mul (2 * π))
    (hsc.smul hgm) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_smul, norm_mul]
  have h1 : ‖2 * (π : ℂ) * Complex.I‖ = 2 * π := by simp [Real.pi_nonneg]
  have h2 : ‖((ξ i : ℝ) : ℂ)‖ ≤ ‖ξ‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_coord_le_norm_r3 ξ i
  rw [h1]
  calc 2 * π * ‖((ξ i : ℝ) : ℂ)‖ * ‖r3DecodedFrequency 3 v ξ‖
      ≤ 2 * π * ‖ξ‖ * ‖r3DecodedFrequency 3 v ξ‖ := by gcongr
    _ = 2 * π * (‖ξ‖ * ‖r3DecodedFrequency 3 v ξ‖) := by ring

/-- **The decoded derivative operator realizes the explicit derivative**: for every
order-three coordinate `v`, the `L²` element `Dᵢ v` is an a.e. representative of
`x ↦ r3RepresentativeDeriv (r3DecodedFrequency 3 v) x (eᵢ)`. -/
theorem r3DecodedDerivativeL2Operator_ae_deriv (i : Fin 3) (v : R3HsVelocity 3) :
    ((r3DecodedDerivativeL2Operator i v : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      fun x : R3 =>
        r3RepresentativeDeriv (r3DecodedFrequency 3 v) x (r3StdBasis i) := by
  set h : R3 → R3C := fun ξ =>
    ((2 * (π : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) • r3DecodedFrequency 3 v ξ with hhdef
  have hInt : Integrable h volume := integrable_r3DecodedDerivativeProfile i v
  have hMem : MemLp h 2 volume := by
    refine (memLp_congr_ae ?_).mp
      (Lp.memLp (r3L2ScalarMultiplier (r3DecodedDerivativeWeightLpTop i)
        (𝓕 v : R3L2Velocity)))
    filter_upwards [r3DecodedDerivativeMultiplier_ae i (𝓕 v : R3L2Velocity)] with ξ hξ
    rw [hξ, r3DecodedDerivativeWeight_smul_fourier]
  have hop : r3DecodedDerivativeL2Operator i v = 𝓕⁻ (hMem.toLp h) := by
    unfold r3DecodedDerivativeL2Operator
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      FourierTransform.fourierCLM_apply, FourierTransform.fourierInvCLM_apply]
    congr 1
    apply Lp.ext
    filter_upwards [r3DecodedDerivativeMultiplier_ae i (𝓕 v : R3L2Velocity),
      hMem.coeFn_toLp] with ξ h1 h2
    rw [h1, h2, r3DecodedDerivativeWeight_smul_fourier]
  have hderiv : ∀ x : R3,
      r3RepresentativeDeriv (r3DecodedFrequency 3 v) x (r3StdBasis i) =
        r3PhysicalRepresentative h x := fun x =>
    r3RepresentativeDeriv_stdBasis (integrable_r3DecodedFrequency v)
      (integrable_weighted_r3DecodedFrequency v) x i
  rw [hop]
  filter_upwards [r3PhysicalRepresentative_ae_fourierInv hInt hMem] with x hx
  rw [hderiv x]
  exact hx.symm

/-! ## The pointwise convection field and its `L²` bundling -/

/-- **The pointwise convection of the decoded representatives** `(U_u · ∇) U_v`, built
from the explicit derivative of edge 1b. -/
def r3DecodedConvectionPointwise (u v : R3HsVelocity 3) : R3 → R3C :=
  fun x => ∑ i : Fin 3,
    (r3PhysicalRepresentative (r3DecodedFrequency 3 u) x) i •
      r3RepresentativeDeriv (r3DecodedFrequency 3 v) x (r3StdBasis i)

/-- The explicit derivative in the convection field is the genuine Fréchet derivative of
the decoded representative. -/
theorem r3DecodedConvectionPointwise_eq_fderiv (u v : R3HsVelocity 3) (x : R3) :
    r3DecodedConvectionPointwise u v x = ∑ i : Fin 3,
      (r3PhysicalRepresentative (r3DecodedFrequency 3 u) x) i •
        fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 v)) x (r3StdBasis i) := by
  unfold r3DecodedConvectionPointwise
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hasFDerivAt_r3PhysicalRepresentative (integrable_r3DecodedFrequency v)
    (integrable_weighted_r3DecodedFrequency v) x).fderiv]

/-- The `L²` bundling of the convection field through the component multipliers and the
derivative operators. -/
def r3DecodedConvectionSum (u v : R3HsVelocity 3) : R3L2Velocity :=
  ∑ i : Fin 3,
    r3L2ScalarMultiplier (r3DecodedComponentLpTop u i) (r3DecodedDerivativeL2Operator i v)

theorem coeFn_r3DecodedConvectionSum (u v : R3HsVelocity 3) :
    ((r3DecodedConvectionSum u v : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      r3DecodedConvectionPointwise u v := by
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  have hsum : r3DecodedConvectionSum u v =
      r3L2ScalarMultiplier (r3DecodedComponentLpTop u 0)
          (r3DecodedDerivativeL2Operator 0 v) +
        r3L2ScalarMultiplier (r3DecodedComponentLpTop u 1)
          (r3DecodedDerivativeL2Operator 1 v) +
        r3L2ScalarMultiplier (r3DecodedComponentLpTop u 2)
          (r3DecodedDerivativeL2Operator 2 v) := by
    unfold r3DecodedConvectionSum
    rw [Fin.sum_univ_three]
  rw [hsum]
  have hterm : ∀ i : Fin 3,
      (r3L2ScalarMultiplier (r3DecodedComponentLpTop u i)
        (r3DecodedDerivativeL2Operator i v) : R3 → R3C) =ᵐ[volume]
      fun x : R3 =>
        (r3PhysicalRepresentative (r3DecodedFrequency 3 u) x) i •
          r3RepresentativeDeriv (r3DecodedFrequency 3 v) x (r3StdBasis i) := by
    intro i
    rw [r3L2ScalarMultiplier_apply]
    filter_upwards
      [Lp.coeFn_lpSMul (r := (2 : ENNReal)) (r3DecodedComponentLpTop u i)
        (r3DecodedDerivativeL2Operator i v),
        r3DecodedComponentLpTop_ae u i,
        r3DecodedDerivativeL2Operator_ae_deriv i v]
      with x hmul hcomp hderiv
    rw [hmul, Pi.smul_apply', hcomp, hderiv]
  filter_upwards
    [Lp.coeFn_add
      (r3L2ScalarMultiplier (r3DecodedComponentLpTop u 0)
          (r3DecodedDerivativeL2Operator 0 v) +
        r3L2ScalarMultiplier (r3DecodedComponentLpTop u 1)
          (r3DecodedDerivativeL2Operator 1 v))
      (r3L2ScalarMultiplier (r3DecodedComponentLpTop u 2)
        (r3DecodedDerivativeL2Operator 2 v)),
      Lp.coeFn_add
        (r3L2ScalarMultiplier (r3DecodedComponentLpTop u 0)
          (r3DecodedDerivativeL2Operator 0 v))
        (r3L2ScalarMultiplier (r3DecodedComponentLpTop u 1)
          (r3DecodedDerivativeL2Operator 1 v)),
      hterm 0, hterm 1, hterm 2] with x h1 h2 t0 t1 t2
  rw [h1, Pi.add_apply, h2, Pi.add_apply, t0, t1, t2]
  unfold r3DecodedConvectionPointwise
  rw [Fin.sum_univ_three]

theorem memLp_two_r3DecodedConvectionPointwise (u v : R3HsVelocity 3) :
    MemLp (r3DecodedConvectionPointwise u v) 2 volume :=
  (memLp_congr_ae (coeFn_r3DecodedConvectionSum u v)).mp
    (Lp.memLp (r3DecodedConvectionSum u v))

/-- **The convection source `(U·∇)V` as an `L²` element**, constructed pointwise from the
decoded representatives and their explicit derivatives. -/
def r3DecodedConvectionL2 (u v : R3HsVelocity 3) : R3L2Velocity :=
  (memLp_two_r3DecodedConvectionPointwise u v).toLp (r3DecodedConvectionPointwise u v)

theorem coeFn_r3DecodedConvectionL2 (u v : R3HsVelocity 3) :
    ((r3DecodedConvectionL2 u v : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      r3DecodedConvectionPointwise u v :=
  MemLp.coeFn_toLp (memLp_two_r3DecodedConvectionPointwise u v)

theorem r3DecodedConvectionL2_eq_sum (u v : R3HsVelocity 3) :
    r3DecodedConvectionL2 u v = r3DecodedConvectionSum u v := by
  apply Lp.ext
  filter_upwards [coeFn_r3DecodedConvectionL2 u v, coeFn_r3DecodedConvectionSum u v]
    with x h1 h2
  rw [h1, h2]

/-! ## Continuity of the decoded convection in each slot -/

/-- Scalar multipliers subtract on the multiplier side. -/
theorem r3L2ScalarMultiplier_sub_left (a b : Lp ℂ ⊤ (volume : Measure R3))
    (x : R3L2Velocity) :
    r3L2ScalarMultiplier a x - r3L2ScalarMultiplier b x =
      r3L2ScalarMultiplier (a - b) x := by
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  simp only [r3L2ScalarMultiplier_apply]
  rw [sub_eq_add_neg a b, MeasureTheory.Lp.smul_add, MeasureTheory.Lp.neg_smul,
    ← sub_eq_add_neg]

theorem norm_r3L2ScalarMultiplier_apply_le (a : Lp ℂ ⊤ (volume : Measure R3))
    (x : R3L2Velocity) :
    ‖r3L2ScalarMultiplier a x‖ ≤ ‖a‖ * ‖x‖ := by
  letI : ENNReal.HolderTriple (⊤ : ENNReal) 2 2 := ⟨by simp⟩
  rw [r3L2ScalarMultiplier_apply]
  exact MeasureTheory.Lp.norm_smul_le a x

/-- The decoded convection is Lipschitz (hence continuous) in the first slot, with the
quantitative Cauchy–Schwarz decoder constant. -/
theorem continuous_r3DecodedConvectionL2_left (v : R3HsVelocity 3) :
    Continuous fun u : R3HsVelocity 3 => r3DecodedConvectionL2 u v := by
  set K : ℝ := ‖r3H3InverseBesselWeightL2‖ *
    ∑ i : Fin 3, ‖r3DecodedDerivativeL2Operator i v‖ with hKdef
  have hK0 : 0 ≤ K :=
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal K)
    (f := fun u : R3HsVelocity 3 => r3DecodedConvectionL2 u v) fun u u' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hK0]
  rw [r3DecodedConvectionL2_eq_sum, r3DecodedConvectionL2_eq_sum]
  unfold r3DecodedConvectionSum
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i : Fin 3,
      ‖r3L2ScalarMultiplier (r3DecodedComponentLpTop u i)
          (r3DecodedDerivativeL2Operator i v) -
        r3L2ScalarMultiplier (r3DecodedComponentLpTop u' i)
          (r3DecodedDerivativeL2Operator i v)‖ ≤
      (‖r3H3InverseBesselWeightL2‖ * ‖u - u'‖) *
        ‖r3DecodedDerivativeL2Operator i v‖ := by
    intro i
    rw [r3L2ScalarMultiplier_sub_left, r3DecodedComponentLpTop_sub]
    refine (norm_r3L2ScalarMultiplier_apply_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_r3DecodedComponentLpTop_le (u - u') i)
      (norm_nonneg _)
  calc ∑ i : Fin 3,
        ‖r3L2ScalarMultiplier (r3DecodedComponentLpTop u i)
            (r3DecodedDerivativeL2Operator i v) -
          r3L2ScalarMultiplier (r3DecodedComponentLpTop u' i)
            (r3DecodedDerivativeL2Operator i v)‖
      ≤ ∑ i : Fin 3, (‖r3H3InverseBesselWeightL2‖ * ‖u - u'‖) *
          ‖r3DecodedDerivativeL2Operator i v‖ :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = K * ‖u - u'‖ := by
        rw [hKdef, ← Finset.mul_sum]
        ring

/-- The decoded convection is continuous in the second slot (it is a fixed finite sum of
continuous linear operators there). -/
theorem continuous_r3DecodedConvectionL2_right (u : R3HsVelocity 3) :
    Continuous fun v : R3HsVelocity 3 => r3DecodedConvectionL2 u v := by
  have hrw : (fun v : R3HsVelocity 3 => r3DecodedConvectionL2 u v) =
      ⇑(∑ i : Fin 3,
        (r3L2ScalarMultiplier (r3DecodedComponentLpTop u i)).comp
          (r3DecodedDerivativeL2Operator i)) := by
    funext v
    rw [r3DecodedConvectionL2_eq_sum]
    unfold r3DecodedConvectionSum
    rw [sum_apply]
    rfl
  rw [hrw]
  exact (∑ i : Fin 3,
    (r3L2ScalarMultiplier (r3DecodedComponentLpTop u i)).comp
      (r3DecodedDerivativeL2Operator i)).continuous

/-! ## The Schwartz base case -/

/-- The order-three inverse weight cancels the order-three Sobolev multiplier
pointwise. -/
theorem r3H3InverseBesselWeightComplex_mul_weight_three (ξ : R3) :
    r3H3InverseBesselWeightComplex ξ * r3SobolevWeightComplex 3 ξ = 1 := by
  unfold r3H3InverseBesselWeightComplex r3SobolevWeightComplex
  rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  norm_num

/-- On a canonical Schwartz coordinate, the decoded frequency data is a.e. the Fourier
transform of the original Schwartz field: the decoder weight exactly cancels the encoding
weight. -/
theorem r3DecodedFrequency_r3SchwartzToHsCLM_ae (φ : R3SchwartzVelocity) :
    r3DecodedFrequency 3 (r3SchwartzToHsCLM 3 φ) =ᵐ[volume]
      ⇑(𝓕 φ : R3SchwartzVelocity) := by
  have hfour : (𝓕 (r3SchwartzToHsCLM 3 φ) : R3L2Velocity) =
      (r3SchwartzSobolevFrequencyCoordinate 3 φ).toLp 2 := by
    rw [r3SchwartzToHsCLM_apply, SchwartzMap.toLp_fourier_eq,
      fourier_r3SchwartzBesselCoordinate]
  unfold r3DecodedFrequency
  rw [hfour]
  filter_upwards
    [(r3SchwartzSobolevFrequencyCoordinate 3 φ).coeFn_toLp 2 (volume : Measure R3)]
    with ξ hξ
  rw [hξ]
  unfold r3SchwartzSobolevFrequencyCoordinate
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  rw [r3RealSmul_eq_complexSmul, smul_smul, r3InverseBesselWeight_eq_sobolevWeight]
  rw [show r3SobolevWeightComplex (-3) ξ *
      Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2)) =
      r3H3InverseBesselWeightComplex ξ * r3SobolevWeightComplex 3 ξ from rfl]
  rw [r3H3InverseBesselWeightComplex_mul_weight_three, one_smul]

/-- **Exact inversion on the Schwartz core**: the decoded physical representative of a
canonical Schwartz coordinate is the original Schwartz field, pointwise everywhere. -/
theorem r3DecodedRepresentative_schwartz (φ : R3SchwartzVelocity) :
    r3PhysicalRepresentative (r3DecodedFrequency 3 (r3SchwartzToHsCLM 3 φ)) = ⇑φ := by
  rw [r3PhysicalRepresentative_congr_ae (r3DecodedFrequency_r3SchwartzToHsCLM_ae φ)]
  unfold r3PhysicalRepresentative
  rw [show ⇑(𝓕 φ : R3SchwartzVelocity) = 𝓕 (⇑φ) from SchwartzMap.fourier_coe φ]
  exact φ.continuous.fourierInv_fourier_eq φ.integrable
    (by simpa [SchwartzMap.fourier_coe] using (𝓕 φ : R3SchwartzVelocity).integrable)

/-- On the Schwartz core, the explicit derivative of the decoded representative is the
Fréchet derivative of the original Schwartz field. -/
theorem r3RepresentativeDeriv_schwartz (ψ : R3SchwartzVelocity) (x : R3) :
    r3RepresentativeDeriv (r3DecodedFrequency 3 (r3SchwartzToHsCLM 3 ψ)) x =
      fderiv ℝ (⇑ψ) x := by
  have hder := hasFDerivAt_r3PhysicalRepresentative
    (integrable_r3DecodedFrequency (r3SchwartzToHsCLM 3 ψ))
    (integrable_weighted_r3DecodedFrequency (r3SchwartzToHsCLM 3 ψ)) x
  rw [r3DecodedRepresentative_schwartz ψ] at hder
  exact hder.fderiv.symm

/-- The concrete coordinate direction of the Schwartz layer is the standard basis
vector. -/
theorem r3CoordinateDirection_eq_stdBasis (i : Fin 3) :
    r3CoordinateDirection i = r3StdBasis i := by
  ext j
  simp [r3CoordinateDirection, r3StdBasis, eq_comm]

/-- **The Schwartz base case**: on canonical order-three Schwartz coordinates, the
decoded convection is the literal physical Schwartz convection. -/
theorem r3DecodedConvectionL2_schwartz (φ ψ : R3SchwartzVelocity) :
    r3DecodedConvectionL2 (r3SchwartzToHsCLM 3 φ) (r3SchwartzToHsCLM 3 ψ) =
      (r3SchwartzConvection φ ψ).toLp 2 := by
  apply Lp.ext
  filter_upwards [coeFn_r3DecodedConvectionL2 (r3SchwartzToHsCLM 3 φ)
      (r3SchwartzToHsCLM 3 ψ),
    (r3SchwartzConvection φ ψ).coeFn_toLp 2 (volume : Measure R3)] with x h1 h2
  rw [h1, h2]
  unfold r3DecodedConvectionPointwise
  rw [r3SchwartzConvection_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r3DecodedRepresentative_schwartz φ, r3RepresentativeDeriv_schwartz ψ x]
  congr 1
  rw [show r3SchwartzCoordinateDerivative i ψ x =
      fderiv ℝ (⇑ψ) x (r3CoordinateDirection i) from rfl,
    r3CoordinateDirection_eq_stdBasis]

/-! ## The identification theorem -/

/-- **Clay semantic-promotion edge 2b-i: general `H³` convection source
identification.**  For arbitrary order-three Bessel coordinates `u, v`, the genuine
`J⁻²` decode of the completed coordinate convection is exactly the pointwise convection
`(U_u · ∇) U_v` of the decoded physical representatives, as an `L²` identity. -/
theorem r3H2ToL2Operator_r3ConvectionH3ToH2 (u v : R3HsVelocity 3) :
    r3H2ToL2Operator (r3ConvectionH3ToH2 u v) = r3DecodedConvectionL2 u v := by
  refine (r3SchwartzToHsCLM_denseRange 3).induction_on v ?_ ?_
  · refine isClosed_eq ?_ (continuous_r3DecodedConvectionL2_right u)
    exact r3H2ToL2Operator.continuous.comp (r3ConvectionH3ToH2 u).continuous
  · intro ψ
    refine (r3SchwartzToHsCLM_denseRange 3).induction_on u ?_ ?_
    · refine isClosed_eq ?_ (continuous_r3DecodedConvectionL2_left _)
      exact r3H2ToL2Operator.continuous.comp
        (r3ConvectionH3ToH2.flip (r3SchwartzToHsCLM 3 ψ)).continuous
    · intro φ
      rw [r3ConvectionH3ToH2_apply_schwartz, r3H2ToL2Operator_r3SchwartzToHsCLM,
        r3DecodedConvectionL2_schwartz]

/-- Pointwise a.e. form of the identification: the decoded completed convection
coordinate is a.e. the literal pointwise convection of the decoded representatives. -/
theorem coeFn_r3H2ToL2Operator_r3ConvectionH3ToH2 (u v : R3HsVelocity 3) :
    ((r3H2ToL2Operator (r3ConvectionH3ToH2 u v) : R3L2Velocity) : R3 → R3C) =ᵐ[volume]
      r3DecodedConvectionPointwise u v := by
  rw [r3H2ToL2Operator_r3ConvectionH3ToH2]
  exact coeFn_r3DecodedConvectionL2 u v

/-- **Projected corollary**: the decode of the projected completed convection is the
physical `L²` Leray projection of the identified convection source `P((U·∇)V)`. -/
theorem r3H2ToL2Operator_r3ProjectedConvectionH3ToH2 (u v : R3HsVelocity 3) :
    r3H2ToL2Operator (r3ProjectedConvectionH3ToH2 u v) =
      r3LerayL2Operator (r3DecodedConvectionL2 u v) := by
  rw [r3ProjectedConvectionH3ToH2_apply, r3H2ToL2Operator_commutes_leray,
    r3H2ToL2Operator_r3ConvectionH3ToH2]

/-- The Leray complement of the identified convection source is the difference of the
decoded unprojected and projected coordinates — the exact input shape of the edge-2a
pressure reconstruction. -/
theorem r3LerayComplementL2_r3DecodedConvectionL2 (u v : R3HsVelocity 3) :
    r3LerayComplementL2 (r3DecodedConvectionL2 u v) =
      r3H2ToL2Operator (r3ConvectionH3ToH2 u v) -
        r3H2ToL2Operator (r3ProjectedConvectionH3ToH2 u v) := by
  unfold r3LerayComplementL2
  rw [r3H2ToL2Operator_r3ConvectionH3ToH2, r3H2ToL2Operator_r3ProjectedConvectionH3ToH2]

/-- **Direct instantiation of edge 2a at the identified source** (no new mathematical
content): the Helmholtz pressure of the convection source `(U·∇)V` satisfies the gradient
equation `∇p = -(I-P)((U·∇)V)` componentwise in `𝓢'`. -/
theorem r3HelmholtzPressure_gradient_decodedConvection
    (u v : R3HsVelocity 3) (j : Fin 3) :
    ∂_{r3StdBasis j} (r3HelmholtzPressure (r3DecodedConvectionL2 u v)) =
      -(PointwiseConvergenceCLM.postcomp 𝓢(R3, ℂ)
        (EuclideanSpace.proj j : R3C →L[ℂ] ℂ)
        ((r3LerayComplementL2 (r3DecodedConvectionL2 u v) : R3L2Velocity) :
          𝓢'(R3, R3C))) :=
  r3HelmholtzPressure_gradient (r3DecodedConvectionL2 u v) j

/-! ## Non-vacuity witness

The identification is not the trivial identity `0 = 0`: a concrete smooth bump field
(complexified, pointing in the `e₀` direction) has nonzero decoded convection.  The
argument needs no derivative evaluation: if the convection `½∂₀(b²) • e₀` vanished
identically, the square of the bump would be constant along the `e₀`-axis, contradicting
`b = 1` at the centre and `b = 0` outside the support. -/

/-- The witness bump: plateau of radius one, support of radius two, centred at the
origin. -/
def r3ConvectionWitnessBump : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The complexified witness bump has compact support. -/
theorem r3ConvectionWitnessBump_hasCompactSupport :
    HasCompactSupport (fun x : R3 => ((r3ConvectionWitnessBump x : ℝ) : ℂ)) :=
  HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ))
    r3ConvectionWitnessBump.hasCompactSupport rfl

/-- The complexified witness bump is smooth. -/
theorem contDiff_r3ConvectionWitnessBumpC :
    ContDiff ℝ ∞ (fun x : R3 => ((r3ConvectionWitnessBump x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp r3ConvectionWitnessBump.contDiff

/-- The complexified witness bump as a scalar Schwartz function. -/
def r3ConvectionWitnessScalar : 𝓢(R3, ℂ) :=
  r3ConvectionWitnessBump_hasCompactSupport.toSchwartzMap
    contDiff_r3ConvectionWitnessBumpC

/-- The witness velocity field: the bump profile in the `e₀` direction. -/
def r3ConvectionWitnessField : R3SchwartzVelocity :=
  r3ConvectionWitnessScalar.postcompCLM
    (ContinuousLinearMap.toSpanSingleton ℂ
      (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C))

theorem r3ConvectionWitnessField_apply (x : R3) :
    r3ConvectionWitnessField x =
      ((r3ConvectionWitnessBump x : ℝ) : ℂ) •
        (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) := rfl

/-- The full Fréchet derivative of the witness field, through the scalar chain rule. -/
theorem hasFDerivAt_r3ConvectionWitnessField (x : R3) :
    HasFDerivAt (⇑r3ConvectionWitnessField)
      (((ContinuousLinearMap.toSpanSingleton ℂ
          (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C)).restrictScalars ℝ) ∘L
        (Complex.ofRealCLM ∘L fderiv ℝ (⇑r3ConvectionWitnessBump) x)) x := by
  have hb : HasFDerivAt (⇑r3ConvectionWitnessBump)
      (fderiv ℝ (⇑r3ConvectionWitnessBump) x) x :=
    ((r3ConvectionWitnessBump.contDiff (n := 1)).differentiable one_ne_zero x).hasFDerivAt
  have hreal : HasFDerivAt (fun x : R3 => ((r3ConvectionWitnessBump x : ℝ) : ℂ))
      (Complex.ofRealCLM ∘L fderiv ℝ (⇑r3ConvectionWitnessBump) x) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hb
  exact ((ContinuousLinearMap.toSpanSingleton ℂ
    (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C)).restrictScalars
      ℝ).hasFDerivAt.comp x hreal

/-- If the witness convection vanished at every point, the directional derivative
product `b · ∂₀b` would vanish everywhere. -/
theorem r3ConvectionWitness_pointwise_product {x : R3}
    (hx : r3SchwartzConvection r3ConvectionWitnessField r3ConvectionWitnessField x = 0) :
    (r3ConvectionWitnessBump x : ℝ) *
      fderiv ℝ (⇑r3ConvectionWitnessBump) x (r3CoordinateDirection 0) = 0 := by
  rw [r3SchwartzConvection_apply] at hx
  have hderiv : ∀ i : Fin 3, r3SchwartzCoordinateDerivative i r3ConvectionWitnessField x =
      (((fderiv ℝ (⇑r3ConvectionWitnessBump) x (r3CoordinateDirection i) : ℝ) : ℂ)) •
        (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) := by
    intro i
    show fderiv ℝ (⇑r3ConvectionWitnessField) x (r3CoordinateDirection i) = _
    rw [(hasFDerivAt_r3ConvectionWitnessField x).fderiv]
    rfl
  have hcomp : ∀ i : Fin 3, r3ConvectionWitnessField x i =
      ((r3ConvectionWitnessBump x : ℝ) : ℂ) *
        ((EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) i) := by
    intro i
    rw [r3ConvectionWitnessField_apply]
    simp
  rw [Fin.sum_univ_three, hderiv 0, hderiv 1, hderiv 2, hcomp 0, hcomp 1, hcomp 2] at hx
  have h1 : ((EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) (1 : Fin 3)) = 0 := by
    simp
  have h2 : ((EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) (2 : Fin 3)) = 0 := by
    simp
  have h0 : ((EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) (0 : Fin 3)) = 1 := by
    simp
  rw [h0, h1, h2] at hx
  simp only [mul_one, mul_zero, zero_mul, zero_smul, add_zero, smul_smul] at hx
  have hsingle : (EuclideanSpace.single (0 : Fin 3) (1 : ℂ) : R3C) ≠ 0 := by
    intro h
    have := congrArg (fun v : R3C => v 0) h
    simp at this
  have hscalar : ((r3ConvectionWitnessBump x : ℝ) : ℂ) *
      (((fderiv ℝ (⇑r3ConvectionWitnessBump) x (r3CoordinateDirection 0) : ℝ) : ℂ)) = 0 :=
    (smul_eq_zero.mp hx).resolve_right hsingle
  have : (((r3ConvectionWitnessBump x : ℝ) *
      fderiv ℝ (⇑r3ConvectionWitnessBump) x (r3CoordinateDirection 0) : ℝ) : ℂ) = 0 := by
    push_cast
    exact hscalar
  exact_mod_cast this

/-- **Non-vacuity witness for edge 2b-i**: the identified convection source is not
identically zero — there are order-three coordinates with nonzero `(U·∇)V`. -/
theorem exists_r3DecodedConvectionL2_ne_zero :
    ∃ u v : R3HsVelocity 3, r3DecodedConvectionL2 u v ≠ 0 := by
  refine ⟨r3SchwartzToHsCLM 3 r3ConvectionWitnessField,
    r3SchwartzToHsCLM 3 r3ConvectionWitnessField, fun hzero => ?_⟩
  rw [r3DecodedConvectionL2_schwartz] at hzero
  -- The Lp class vanishing forces a.e. vanishing of the continuous convection field.
  have hae : ⇑(r3SchwartzConvection r3ConvectionWitnessField r3ConvectionWitnessField)
      =ᵐ[volume] (fun _ : R3 => (0 : R3C)) := by
    have h1 := (r3SchwartzConvection r3ConvectionWitnessField
      r3ConvectionWitnessField).coeFn_toLp 2 (volume : Measure R3)
    rw [hzero] at h1
    filter_upwards [h1, Lp.coeFn_zero R3C 2 (volume : Measure R3)] with y hy hz
    rw [← hy]
    exact hz
  -- Continuity upgrades a.e. vanishing to everywhere vanishing.
  have hall : ∀ x : R3,
      r3SchwartzConvection r3ConvectionWitnessField r3ConvectionWitnessField x = 0 := by
    intro x
    by_contra hx
    have hopen : IsOpen {y : R3 |
        r3SchwartzConvection r3ConvectionWitnessField r3ConvectionWitnessField y ≠ 0} :=
      isOpen_ne.preimage (r3SchwartzConvection r3ConvectionWitnessField
        r3ConvectionWitnessField).continuous
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
    have hnull : volume {y : R3 |
        r3SchwartzConvection r3ConvectionWitnessField r3ConvectionWitnessField y ≠ 0} = 0 :=
      MeasureTheory.ae_iff.mp hae
    exact absurd (measure_mono_null hball hnull)
      (Metric.measure_ball_pos volume x hε).ne'
  -- The product `b · ∂₀b = ½ ∂₀(b²)` vanishes everywhere; integrate along the axis.
  have hprod : ∀ x : R3, (r3ConvectionWitnessBump x : ℝ) *
      fderiv ℝ (⇑r3ConvectionWitnessBump) x (r3CoordinateDirection 0) = 0 := fun x =>
    r3ConvectionWitness_pointwise_product (hall x)
  set d : R3 := r3CoordinateDirection 0 with hd
  have hbdiff : Differentiable ℝ (⇑r3ConvectionWitnessBump) :=
    (r3ConvectionWitnessBump.contDiff (n := 1)).differentiable one_ne_zero
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • d) d t := by
    intro t
    have h := (hasDerivAt_id t).smul_const d
    rwa [one_smul] at h
  have hB : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => r3ConvectionWitnessBump (s • d) * r3ConvectionWitnessBump (s • d))
      (2 * (r3ConvectionWitnessBump (t • d) *
        fderiv ℝ (⇑r3ConvectionWitnessBump) (t • d) d)) t := by
    intro t
    have hcomp := (hbdiff (t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have hmul := hcomp.mul hcomp
    have h2 : 2 * (r3ConvectionWitnessBump (t • d) *
        fderiv ℝ (⇑r3ConvectionWitnessBump) (t • d) d) =
        (fderiv ℝ (⇑r3ConvectionWitnessBump) (t • d)) d *
            ((⇑r3ConvectionWitnessBump ∘ fun s : ℝ => s • d) t) +
          ((⇑r3ConvectionWitnessBump ∘ fun s : ℝ => s • d) t) *
            (fderiv ℝ (⇑r3ConvectionWitnessBump) (t • d)) d := by
      simp only [Function.comp_apply]
      ring
    rw [h2]
    exact hmul
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s : ℝ =>
      r3ConvectionWitnessBump (s • d) * r3ConvectionWitnessBump (s • d))
    (fun t => ((hB t).differentiableAt))
    (fun t => by
      rw [(hB t).deriv]
      rw [hprod (t • d)]
      ring) 0 2
  have hnormd : ‖d‖ = 1 := by
    rw [hd]
    rw [r3CoordinateDirection_eq_stdBasis]
    simp [r3StdBasis]
  have hcenter : r3ConvectionWitnessBump ((0 : ℝ) • d) = 1 := by
    rw [zero_smul]
    exact r3ConvectionWitnessBump.one_of_mem_closedBall
      (by simp [r3ConvectionWitnessBump])
  have houter : r3ConvectionWitnessBump ((2 : ℝ) • d) = 0 := by
    refine r3ConvectionWitnessBump.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, hnormd]
    simp [r3ConvectionWitnessBump]
  rw [hcenter, houter, mul_zero, mul_one] at hconst
  exact one_ne_zero hconst

/-- Through the identification, the completed coordinate convection operator itself is
nontrivial: the witness pair has nonzero coordinate output as well (its decode is the
nonzero identified source), so the identification theorem is not the identity `0 = 0`. -/
theorem exists_r3ConvectionH3ToH2_ne_zero :
    ∃ u v : R3HsVelocity 3, r3ConvectionH3ToH2 u v ≠ 0 := by
  obtain ⟨u, v, huv⟩ := exists_r3DecodedConvectionL2_ne_zero
  exact ⟨u, v, fun h => huv (by rw [← r3H2ToL2Operator_r3ConvectionH3ToH2, h, map_zero])⟩

end

end MNS2
