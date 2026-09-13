import Formal.R3ConvectionSourceIdentification

/-!
# The decoded gradient-sup functional and the T-SEL embedding (SEL-2, SEL-7 parts)

T-SEL (`docs/gates/STAGE9_REVERSE_GAP_AUDIT_2026-09-02.md`, SS-5/SS-6) is the
time-integrated velocity-gradient bound `∫₀^{T′} ‖∇U(s)‖_{L∞} ds ≤ G(T)` for the decoded
physical velocity `U = J⁻³ ∘ u` along certified mild solutions.  Before the bridge can
even be **stated**, the quantity `‖∇U‖_{L∞}` needs an honest formal carrier.  This file
builds it on the repository's existing explicit decoded representative
(`r3PhysicalRepresentative (r3DecodedFrequency 3 f)` — the pointwise inverse-Fourier
integral of the inverse-Bessel-weighted frequency data, `C¹` at every point by
`hasFDerivAt_r3PhysicalRepresentative`, and a.e. equal to the `L²` decode
`r3H3ToL2Operator f` by `r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity`):

* `r3DecodedSup f = ⨆ x, ‖U_f(x)‖` and `r3DecodedGradSup f = ⨆ x, ‖(DU_f)(x)‖` — the
  sup and gradient-sup of the decoded representative, genuine finite reals;
* **SEL-2 is closed quantitatively**: `r3DecodedSup f + r3DecodedGradSup f ≤ C_emb ‖f‖`
  with the explicit constant
  `C_emb = ‖J⁻³‖_{L²} + 2π ‖innerSL ℝ‖ ‖ξ ↦ ‖ξ‖(1+‖ξ‖²)^{-3/2}‖_{L²}` — Cauchy–Schwarz
  against the two square-integrable decoder weights (`3 > 5/2` enters exactly as the
  square integrability of the weighted weight in dimension three, mathlib's
  Japanese-bracket lemma via `memLp_two_weighted_r3InverseBesselWeight_three`); no
  compactness and no nonconstructive embedding constant;
* the gradient-sup functional is Lipschitz on the carrier
  (`abs_r3DecodedGradSup_sub_le`), hence continuous, hence continuous and interval
  integrable along every certified trajectory — the SEL-7 well-definedness half of the
  audit record;
* `r3TSelGradIntegral u t = ∫ s in 0..t, r3DecodedGradSup (u s)` — the quantity `Q` of
  T-SEL — with nonnegativity and monotonicity in the horizon;
* Schwartz-core pinning: on canonical coordinates of Schwartz fields both functionals
  are literally the sup/gradient-sup of the field itself
  (`r3DecodedSup_schwartz`, `r3DecodedGradSup_schwartz`), because the decoded
  representative of `r3SchwartzToHsCLM 3 φ` **is** `φ` pointwise.

Scope guards.  The phantom alias `R3HsVelocity 3 = R3L2Velocity` is nowhere used as a
physical embedding: every bound goes through the explicit decoder weights, exactly as in
`Formal/R3DecoderFrequencyBridge.lean`.  `r3DecodedGradSup` is the gradient-sup of the
**explicit representative**; its identification with an intrinsic `W^{1,∞}` seminorm of
the abstract distribution is not claimed (and not needed by the bridge).  Nothing here
mentions solutions of any PDE; no Clay-level statement.
-/

namespace MNS2

open MeasureTheory FourierTransform Real VectorFourier
open scoped FourierTransform SchwartzMap ENNReal NNReal

noncomputable section

/-! ## The weighted decoder weight as an `L²` field -/

/-- The first-moment-weighted order-three inverse Bessel weight, complexified:
`ξ ↦ ‖ξ‖ (1+‖ξ‖²)^{-3/2}`. -/
def r3TSelWeightedBesselWeightComplex : R3 → ℂ :=
  fun ξ => ((‖ξ‖ * r3InverseBesselWeight 3 ξ : ℝ) : ℂ)

/-- The weighted decoder weight is square integrable in dimension three (this is exactly
where `3 > 5/2` is spent). -/
theorem r3TSelWeightedBesselWeightComplex_memLp_two :
    MemLp r3TSelWeightedBesselWeightComplex 2 (volume : Measure R3) :=
  memLp_two_weighted_r3InverseBesselWeight_three.ofReal

/-- The weighted decoder weight as an `L²` scalar field. -/
def r3TSelWeightedBesselWeightL2 : Lp ℂ 2 (volume : Measure R3) :=
  r3TSelWeightedBesselWeightComplex_memLp_two.toLp r3TSelWeightedBesselWeightComplex

theorem r3TSelWeightedBesselWeightL2_ae :
    r3TSelWeightedBesselWeightL2 =ᵐ[volume] r3TSelWeightedBesselWeightComplex :=
  MemLp.coeFn_toLp r3TSelWeightedBesselWeightComplex_memLp_two

/-- **Quantitative weighted decoder `L¹` bound** (Cauchy–Schwarz): the first moment of
the order-three decoded frequency data is controlled by the coordinate `L²` norm. -/
theorem integral_weighted_norm_r3DecodedFrequency_le (f : R3L2Velocity) :
    (∫ ξ : R3, ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖) ≤
      ‖r3TSelWeightedBesselWeightL2‖ * ‖f‖ := by
  have hint : Integrable
      (fun ξ : R3 => r3TSelWeightedBesselWeightComplex ξ •
        ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) volume := by
    have hone : MemLp (fun ξ : R3 => r3TSelWeightedBesselWeightComplex ξ •
        ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) 1 volume :=
      (Lp.memLp (𝓕 f)).smul r3TSelWeightedBesselWeightComplex_memLp_two
    exact memLp_one_iff_integrable.mp hone
  have hL1 : hint.toL1 (fun ξ : R3 => r3TSelWeightedBesselWeightComplex ξ •
      ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ) =
      r3TSelWeightedBesselWeightL2 • (𝓕 f : R3L2Velocity) := by
    apply Lp.ext
    filter_upwards [hint.coeFn_toL1,
      Lp.coeFn_lpSMul (r := (1 : ENNReal)) r3TSelWeightedBesselWeightL2
        (𝓕 f : R3L2Velocity),
      r3TSelWeightedBesselWeightL2_ae] with ξ h1 h2 h3
    rw [h1, h2, Pi.smul_apply', h3]
  have hnorm : ∀ ξ : R3, ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖ =
      ‖r3TSelWeightedBesselWeightComplex ξ •
        ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖ := by
    intro ξ
    unfold r3TSelWeightedBesselWeightComplex r3DecodedFrequency
    rw [norm_smul, norm_smul,
      Complex.norm_of_nonneg
        (mul_nonneg (norm_nonneg ξ) (r3InverseBesselWeight_pos 3 ξ).le),
      Real.norm_eq_abs, abs_of_pos (r3InverseBesselWeight_pos 3 ξ)]
    ring
  calc (∫ ξ : R3, ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖)
      = ∫ ξ : R3, ‖r3TSelWeightedBesselWeightComplex ξ •
          ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ‖ :=
        integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ = ‖hint.toL1 (fun ξ : R3 => r3TSelWeightedBesselWeightComplex ξ •
          ((𝓕 f : R3L2Velocity) : R3 → R3C) ξ)‖ :=
        (L1.norm_of_fun_eq_integral_norm hint).symm
    _ = ‖r3TSelWeightedBesselWeightL2 • (𝓕 f : R3L2Velocity)‖ := by rw [hL1]
    _ ≤ ‖r3TSelWeightedBesselWeightL2‖ * ‖(𝓕 f : R3L2Velocity)‖ :=
        MeasureTheory.Lp.norm_smul_le _ _
    _ = ‖r3TSelWeightedBesselWeightL2‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]

/-! ## Operator-norm bound for the explicit representative derivative -/

/-- Sup bound for the explicit representative derivative: at every point its operator
norm is dominated by `2π ‖innerSL ℝ‖` times the first moment of the frequency data. -/
theorem norm_r3RepresentativeDeriv_le {g : R3 → R3C}
    (hg₁ : Integrable g volume)
    (hg₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g ξ‖) volume) (x : R3) :
    ‖r3RepresentativeDeriv g x‖ ≤
      2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ∫ ξ : R3, ‖ξ‖ * ‖g ξ‖ := by
  have hh₁ : Integrable (fun ξ : R3 => g (-ξ)) volume := r3Integrable_comp_neg hg₁
  have hh₂ : Integrable (fun ξ : R3 => ‖ξ‖ * ‖g (-ξ)‖) volume :=
    r3WeightedIntegrable_comp_neg hg₂
  have hF : Integrable
      (fun ξ : R3 => fourierSMulRight (innerSL ℝ) (fun η : R3 => g (-η)) ξ) volume := by
    refine Integrable.mono'
      (hh₂.const_mul (2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖))
      hh₁.aestronglyMeasurable.fourierSMulRight
      (Filter.Eventually.of_forall fun ξ => ?_)
    calc ‖fourierSMulRight (innerSL ℝ) (fun η : R3 => g (-η)) ξ‖
        ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ‖ξ‖ * ‖g (-ξ)‖ :=
          norm_fourierSMulRight_le _ _ _
      _ = 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * (‖ξ‖ * ‖g (-ξ)‖) := by ring
  have hbound : ‖r3RepresentativeDeriv g x‖ ≤
      ∫ ξ : R3, ‖fourierSMulRight (innerSL ℝ) (fun η : R3 => g (-η)) ξ‖ := by
    unfold r3RepresentativeDeriv
    rw [Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp [Circle.norm_smul]
  refine hbound.trans ?_
  have hmono : (∫ ξ : R3, ‖fourierSMulRight (innerSL ℝ) (fun η : R3 => g (-η)) ξ‖) ≤
      ∫ ξ : R3, 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * (‖ξ‖ * ‖g (-ξ)‖) := by
    refine integral_mono hF.norm
      (hh₂.const_mul (2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖)) fun ξ => ?_
    calc ‖fourierSMulRight (innerSL ℝ) (fun η : R3 => g (-η)) ξ‖
        ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ‖ξ‖ * ‖g (-ξ)‖ :=
          norm_fourierSMulRight_le _ _ _
      _ = 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * (‖ξ‖ * ‖g (-ξ)‖) := by ring
  refine hmono.trans ?_
  rw [integral_const_mul]
  have hneg : (∫ ξ : R3, ‖ξ‖ * ‖g (-ξ)‖) = ∫ ξ : R3, ‖ξ‖ * ‖g ξ‖ := by
    have hfun : (fun ξ : R3 => ‖ξ‖ * ‖g (-ξ)‖) =
        fun ξ : R3 => (fun η : R3 => ‖η‖ * ‖g η‖) (-ξ) :=
      funext fun ξ => by rw [← norm_neg ξ]
    rw [hfun, integral_neg_eq_self (fun η : R3 => ‖η‖ * ‖g η‖) volume]
  rw [hneg]

/-! ## The decoded representative is differentiable with a norm-controlled derivative -/

/-- The decoded representative of every order-three coordinate has the explicit Fréchet
derivative at every point. -/
theorem hasFDerivAt_r3DecodedRepresentative (f : R3HsVelocity 3) (x : R3) :
    HasFDerivAt (r3PhysicalRepresentative (r3DecodedFrequency 3 f))
      (r3RepresentativeDeriv (r3DecodedFrequency 3 f) x) x :=
  hasFDerivAt_r3PhysicalRepresentative (integrable_r3DecodedFrequency f)
    (integrable_weighted_r3DecodedFrequency f) x

/-- The genuine `fderiv` of the decoded representative is the explicit derivative. -/
theorem fderiv_r3DecodedRepresentative (f : R3HsVelocity 3) (x : R3) :
    fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x =
      r3RepresentativeDeriv (r3DecodedFrequency 3 f) x :=
  (hasFDerivAt_r3DecodedRepresentative f x).fderiv

/-- The explicit gradient-sup constant of the order-three decoder. -/
def r3DecodedGradSupConstant : ℝ :=
  2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ * ‖r3TSelWeightedBesselWeightL2‖

theorem r3DecodedGradSupConstant_nonneg : 0 ≤ r3DecodedGradSupConstant := by
  unfold r3DecodedGradSupConstant
  positivity

/-- Pointwise gradient bound: `‖(DU_f)(x)‖ ≤ C ‖f‖` everywhere, with the explicit
Cauchy–Schwarz constant. -/
theorem norm_fderiv_r3DecodedRepresentative_le (f : R3HsVelocity 3) (x : R3) :
    ‖fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x‖ ≤
      r3DecodedGradSupConstant * ‖f‖ := by
  rw [fderiv_r3DecodedRepresentative]
  refine (norm_r3RepresentativeDeriv_le (integrable_r3DecodedFrequency f)
    (integrable_weighted_r3DecodedFrequency f) x).trans ?_
  have hc : (0 : ℝ) ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ := by positivity
  calc 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ *
        ∫ ξ : R3, ‖ξ‖ * ‖r3DecodedFrequency 3 f ξ‖
      ≤ 2 * π * ‖(innerSL ℝ : R3 →L[ℝ] R3 →L[ℝ] ℝ)‖ *
        (‖r3TSelWeightedBesselWeightL2‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left (integral_weighted_norm_r3DecodedFrequency_le f) hc
    _ = r3DecodedGradSupConstant * ‖f‖ := by
        unfold r3DecodedGradSupConstant
        ring

/-! ## The sup and gradient-sup functionals -/

/-- The sup of the decoded representative: the formal carrier of `‖U‖_{L∞}`. -/
def r3DecodedSup (f : R3HsVelocity 3) : ℝ :=
  ⨆ x : R3, ‖r3PhysicalRepresentative (r3DecodedFrequency 3 f) x‖

/-- The gradient-sup of the decoded representative: the formal carrier of `‖∇U‖_{L∞}`,
the T-SEL integrand. -/
def r3DecodedGradSup (f : R3HsVelocity 3) : ℝ :=
  ⨆ x : R3, ‖fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x‖

theorem bddAbove_range_norm_r3DecodedRepresentative (f : R3HsVelocity 3) :
    BddAbove (Set.range fun x : R3 =>
      ‖r3PhysicalRepresentative (r3DecodedFrequency 3 f) x‖) := by
  refine ⟨‖r3H3InverseBesselWeightL2‖ * ‖f‖, ?_⟩
  rintro r ⟨x, rfl⟩
  exact norm_r3DecodedRepresentative_le f x

theorem bddAbove_range_norm_fderiv_r3DecodedRepresentative (f : R3HsVelocity 3) :
    BddAbove (Set.range fun x : R3 =>
      ‖fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x‖) := by
  refine ⟨r3DecodedGradSupConstant * ‖f‖, ?_⟩
  rintro r ⟨x, rfl⟩
  exact norm_fderiv_r3DecodedRepresentative_le f x

theorem norm_r3DecodedRepresentative_le_r3DecodedSup (f : R3HsVelocity 3) (x : R3) :
    ‖r3PhysicalRepresentative (r3DecodedFrequency 3 f) x‖ ≤ r3DecodedSup f :=
  le_ciSup (bddAbove_range_norm_r3DecodedRepresentative f) x

theorem norm_fderiv_le_r3DecodedGradSup (f : R3HsVelocity 3) (x : R3) :
    ‖fderiv ℝ (r3PhysicalRepresentative (r3DecodedFrequency 3 f)) x‖ ≤
      r3DecodedGradSup f :=
  le_ciSup (bddAbove_range_norm_fderiv_r3DecodedRepresentative f) x

theorem r3DecodedSup_nonneg (f : R3HsVelocity 3) : 0 ≤ r3DecodedSup f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem r3DecodedGradSup_nonneg (f : R3HsVelocity 3) : 0 ≤ r3DecodedGradSup f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem r3DecodedSup_le (f : R3HsVelocity 3) :
    r3DecodedSup f ≤ ‖r3H3InverseBesselWeightL2‖ * ‖f‖ :=
  ciSup_le fun x => norm_r3DecodedRepresentative_le f x

theorem r3DecodedGradSup_le (f : R3HsVelocity 3) :
    r3DecodedGradSup f ≤ r3DecodedGradSupConstant * ‖f‖ :=
  ciSup_le fun x => norm_fderiv_r3DecodedRepresentative_le f x

/-- **SEL-2, closed quantitatively**: the decoded sup and gradient-sup are dominated by
the carrier norm with the explicit Cauchy–Schwarz embedding constant.  This is the
`H³(ℝ³) ↪ C¹ ∩ W^{1,∞}` estimate of the T-SEL bridge in the repository's own decoded
form; it also witnesses the audit's non-banned check (`Q` is finite per horizon and
strictly lower order than the carrier norm). -/
theorem r3TSel_decoded_embedding (f : R3HsVelocity 3) :
    r3DecodedSup f + r3DecodedGradSup f ≤
      (‖r3H3InverseBesselWeightL2‖ + r3DecodedGradSupConstant) * ‖f‖ := by
  have h1 := r3DecodedSup_le f
  have h2 := r3DecodedGradSup_le f
  have h3 : (‖r3H3InverseBesselWeightL2‖ + r3DecodedGradSupConstant) * ‖f‖ =
      ‖r3H3InverseBesselWeightL2‖ * ‖f‖ + r3DecodedGradSupConstant * ‖f‖ := by ring
  linarith

/-- Semantic pinning: the representative whose gradient-sup is measured is a.e. exactly
the decoded physical velocity `r3H3ToL2Operator f` consumed by the Navier–Stokes
capstone. -/
theorem r3DecodedRepresentative_ae_r3H3ToL2Operator (f : R3HsVelocity 3) :
    r3PhysicalRepresentative (r3DecodedFrequency 3 f) =ᵐ[volume]
      ((r3H3ToL2Operator f : R3L2Velocity) : R3 → R3C) := by
  have h := r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity f
  rwa [r3Decoded3PhysicalVelocity_eq] at h

/-! ## Schwartz-core pinning -/

/-- The gradient-sup of a Schwartz velocity field itself. -/
def r3SchwartzGradSup (φ : R3SchwartzVelocity) : ℝ :=
  ⨆ x : R3, ‖fderiv ℝ (⇑φ) x‖

/-- On the Schwartz core the decoded sup is literally the sup of the field. -/
theorem r3DecodedSup_schwartz (φ : R3SchwartzVelocity) :
    r3DecodedSup (r3SchwartzToHsCLM 3 φ) = ⨆ x : R3, ‖φ x‖ := by
  unfold r3DecodedSup
  rw [r3DecodedRepresentative_schwartz φ]

/-- On the Schwartz core the decoded gradient-sup is literally the gradient-sup of the
field: the T-SEL integrand has the intended classical meaning on the dense core. -/
theorem r3DecodedGradSup_schwartz (φ : R3SchwartzVelocity) :
    r3DecodedGradSup (r3SchwartzToHsCLM 3 φ) = r3SchwartzGradSup φ := by
  unfold r3DecodedGradSup r3SchwartzGradSup
  rw [r3DecodedRepresentative_schwartz φ]

/-! ## Lipschitz continuity of the gradient-sup on the carrier -/

/-- Subadditivity across a difference: pointwise the decoded representative is additive
(`r3DecodedRepresentative_sub`), so the gradient-sup splits against any comparison
coordinate. -/
theorem r3DecodedGradSup_le_add_sub (u v : R3HsVelocity 3) :
    r3DecodedGradSup u ≤ r3DecodedGradSup (u - v) + r3DecodedGradSup v := by
  refine ciSup_le fun x => ?_
  have hfun : r3PhysicalRepresentative (r3DecodedFrequency 3 u) =
      fun y => r3PhysicalRepresentative (r3DecodedFrequency 3 (u - v)) y +
        r3PhysicalRepresentative (r3DecodedFrequency 3 v) y := by
    funext y
    rw [r3DecodedRepresentative_sub u v y]
    abel
  have hsum : HasFDerivAt (r3PhysicalRepresentative (r3DecodedFrequency 3 u))
      (r3RepresentativeDeriv (r3DecodedFrequency 3 (u - v)) x +
        r3RepresentativeDeriv (r3DecodedFrequency 3 v) x) x := by
    rw [hfun]
    exact (hasFDerivAt_r3DecodedRepresentative (u - v) x).add
      (hasFDerivAt_r3DecodedRepresentative v x)
  rw [hsum.fderiv]
  have h1 : ‖r3RepresentativeDeriv (r3DecodedFrequency 3 (u - v)) x‖ ≤
      r3DecodedGradSup (u - v) := by
    rw [← fderiv_r3DecodedRepresentative]
    exact norm_fderiv_le_r3DecodedGradSup (u - v) x
  have h2 : ‖r3RepresentativeDeriv (r3DecodedFrequency 3 v) x‖ ≤ r3DecodedGradSup v := by
    rw [← fderiv_r3DecodedRepresentative]
    exact norm_fderiv_le_r3DecodedGradSup v x
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- The gradient-sup functional is Lipschitz on the carrier with the explicit embedding
constant. -/
theorem abs_r3DecodedGradSup_sub_le (u v : R3HsVelocity 3) :
    |r3DecodedGradSup u - r3DecodedGradSup v| ≤ r3DecodedGradSupConstant * ‖u - v‖ := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 := r3DecodedGradSup_le_add_sub u v
    have h2 := r3DecodedGradSup_le (u - v)
    linarith
  · have h1 := r3DecodedGradSup_le_add_sub v u
    have h2 := r3DecodedGradSup_le (v - u)
    rw [norm_sub_rev] at h2
    linarith

theorem lipschitzWith_r3DecodedGradSup :
    LipschitzWith (Real.toNNReal r3DecodedGradSupConstant) r3DecodedGradSup := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ r3DecodedGradSupConstant_nonneg, dist_eq_norm]
  exact abs_r3DecodedGradSup_sub_le u v

theorem continuous_r3DecodedGradSup : Continuous r3DecodedGradSup :=
  lipschitzWith_r3DecodedGradSup.continuous

/-! ## The T-SEL integrand along a trajectory (SEL-7 well-definedness half) -/

/-- Along any carrier-continuous trajectory the T-SEL integrand is continuous. -/
theorem continuousOn_r3DecodedGradSup_comp {s : Set ℝ} {u : ℝ → R3HsVelocity 3}
    (hu : ContinuousOn u s) :
    ContinuousOn (fun t => r3DecodedGradSup (u t)) s :=
  continuous_r3DecodedGradSup.comp_continuousOn hu

/-- Along any carrier-continuous trajectory the T-SEL integrand is interval integrable
up to every time of the horizon. -/
theorem intervalIntegrable_r3DecodedGradSup_comp {T t : ℝ} {u : ℝ → R3HsVelocity 3}
    (hu : ContinuousOn u (Set.Icc 0 T)) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => r3DecodedGradSup (u s)) volume 0 t := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  exact ((continuousOn_r3DecodedGradSup_comp hu).mono hsub).intervalIntegrable_of_Icc ht.1

/-- **The T-SEL quantity `Q`**: the time integral of the decoded gradient-sup along a
trajectory, `Q(u, t) = ∫ s in 0..t, ‖∇U(s)‖_{L∞}`. -/
def r3TSelGradIntegral (u : ℝ → R3HsVelocity 3) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, r3DecodedGradSup (u s)

theorem r3TSelGradIntegral_nonneg (u : ℝ → R3HsVelocity 3) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ r3TSelGradIntegral u t :=
  intervalIntegral.integral_nonneg ht fun s _ => r3DecodedGradSup_nonneg (u s)

/-- `Q` is monotone in the horizon along carrier-continuous trajectories. -/
theorem r3TSelGradIntegral_mono {T t t' : ℝ} {u : ℝ → R3HsVelocity 3}
    (hu : ContinuousOn u (Set.Icc 0 T)) (h0 : 0 ≤ t) (htt' : t ≤ t') (ht'T : t' ≤ T) :
    r3TSelGradIntegral u t ≤ r3TSelGradIntegral u t' := by
  have h1 : IntervalIntegrable (fun s => r3DecodedGradSup (u s)) volume 0 t :=
    intervalIntegrable_r3DecodedGradSup_comp hu ⟨h0, htt'.trans ht'T⟩
  have h2 : IntervalIntegrable (fun s => r3DecodedGradSup (u s)) volume t t' := by
    have hsub : Set.Icc t t' ⊆ Set.Icc 0 T := Set.Icc_subset_Icc h0 ht'T
    exact ((continuousOn_r3DecodedGradSup_comp hu).mono hsub).intervalIntegrable_of_Icc
      htt'
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hpos : 0 ≤ ∫ s in t..t', r3DecodedGradSup (u s) :=
    intervalIntegral.integral_nonneg htt' fun s _ => r3DecodedGradSup_nonneg (u s)
  unfold r3TSelGradIntegral
  rw [← hadd]
  linarith

end

end MNS2
