import NSFormalization.Section3.T11.ConvolutionBoundReal
import NSFormalization.Section3.T11.EnergyIdentity

/-!
# T11 unit U12b — the tame pairing bound for the periodic convection term

`paper/sections/appendix-a-local-theory.tex:131-138` (`eq:Rhigh`), nonlinear term.

Lane 322 (`Section3/T11/HighOrder.lean`) reduced the `higherOrderBound` field of
`PeriodicContinuationAPI` to one hypothesis, the periodic `eq:Rhigh`, and
recorded two missing facts.  This module supplies the second of them: the
**tame estimate at the pairing level**,

`|⟪Q(A,A), A⟫_{H^m}| ≤ C_m ‖A‖_{H²} ‖A‖_{H^m} ‖A‖_{H^{m+1}}`,

for the convection datum `Q` of lane 328 (`ConvolutionBoundReal.lean`), on the
canonical coefficient carrier and with an explicit constant.

## Route

All three norms are read off a **single** datum `A` at the top order `m+1`:
the torus carrier is a phantom-indexed weighted `ℓ²` sequence, so the `H^s`
datum of the same field is `torusOrderDown (m+1) s A` for every `s ≤ m+1`, and
the paper's `‖u‖_{H²}`, `‖u‖_{H^m}`, `‖u‖_{H^{m+1}}` are the norms of
`torusOrderDown (m+1) 2 A`, `torusOrderDown (m+1) m A` and `A`.

On the Fourier side, with `c = W^{-(m+1)/2} A` the raw coefficients,

* the symbol is `W(k)^{m/2} ∑ⱼ 2πi kⱼ (ĉⱼ ∗ ĉᵢ)(k)`, and `|2πkⱼ| ≤ W(k)^{1/2}`
  absorbs one derivative into the `H^{m+1}` factor (`torusDerivativeSymbol_le`);
* Peetre's inequality `W(k)^{m/2} ≤ 4^{m/2}(W(l)^{m/2} + W(k-l)^{m/2})`
  (`torusWeightPeetre`) splits the remaining weight so that in each half exactly
  one factor carries the full `H^m` weight and the other stays unweighted;
* an unweighted factor is summed in `ℓ¹` against the `H²` datum through
  `∑ₖ W(k)^{-2} < ∞` (`torusInverseWeight_summable`, new: the tree only had the
  exponent `3`, and the tame estimate needs `2`, i.e. any exponent `> 3/2`);
* the three-factor lattice sum is closed by one Cauchy--Schwarz on the lattice
  square with the convolution measure, `torusTrilinearConvolution`:
  `∑_{k,l} X(k) Y(l) β(k-l) ≤ ‖X‖_{ℓ²} ‖Y‖_{ℓ²} ‖β‖_{ℓ¹}`.

The divergence-free cancellation `⟪(u·∇)v, v⟫_{L²} = 0` is **not** used: the
bound holds for every real datum, solenoidal or not.

## Two shapes

The derivative can be charged to either factor, and the two choices give
genuinely different estimates:

* charging it to the **output** frequency (§1's additive Peetre) gives the third
  factor `‖u‖_{H^{m+1}}` — this is `torusPairingBound`, stated for lane 328's
  canonical convection datum `torusConvectionDatumReal`;
* charging it to the **larger of the two summand** frequencies (§8's `Peetre with
  one derivative`, i.e. the region split `|l| ≤ |k-l|` versus `>`) gives the third
  factor `‖∇u‖_{H^m}` — this is `torusPairingBound_advection`, the shape
  `eq:Rhigh` needs, because the dissipation it must be absorbed into is
  `ν‖∇u‖²_{H^m}`.

The two are **not** interchangeable: `‖u‖²_{H^{m+1}} = ‖u‖²_{H^m} + ‖∇u‖²_{H^m}`,
so a nonzero constant field has `‖u‖_{H^{m+1}} > 0 = ‖∇u‖_{H^m}`.  Both are
proved.

## What is proved

* `torusInverseWeight_summable` — `∑ₖ W(k)^{-r} < ∞` for every real `r > 3/2`
  (new: the tree only had `r = 3`, which would force an `H³` low factor).
* `torusTrilinearConvolution` — `∑_{k,l} X(k)Y(l)β(k-l) ≤ ‖X‖₂‖Y‖₂‖β‖₁`.
* `torusWeightPeetre` / `torusWeightPeetre_grad` — Peetre at a real exponent, and
  its derivative-carrying form.
* `torusPairingBound`, `torusPairingBound_nat`, `torusPairingBound_of_reweights`,
  `torusPairingBound_enorm`, `torusPairingBound_profile` — the `‖u‖_{H^{m+1}}`
  estimate for lane 328's datum, on the carrier and in the physical norms.
* `torusProjectedPairing_eq` / `torusProjectedPairingBound` — the same for the
  Leray-projected convection datum against a solenoidal partner.
* `velocityCoeffT_advection` — the Fourier coefficient of `(u·∇)u` is the
  convolution `∑ⱼ ∑ₗ û ⱼ(l) · 2πi(k-l)ⱼ · û ᵢ(k-l)` (periodic convolution theorem
  plus the derivative rule).
* `torusPairingBound_advection` / `torusPairingBound_slice` —
  `|⟪Gm, Nm⟫_{H^m}| ≤ C(m) ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m}` with `Nm` the order-`m`
  datum of the **physical** advection `convectionFieldT u`.
* `torusPairingBound_classical` — the `hpair` hypothesis of lane 335's
  `EnergyIdentity.higherOrderBound_of_pairingBound`, discharged.
* `torusHigherOrderBound` — hence the `higherOrderBound` field of
  `PeriodicContinuationAPI`, **unconditionally** (lane 322 reduced it to
  `eq:Rhigh`, lane 335 reduced `eq:Rhigh` to the pairing bound, this lane proves
  the pairing bound).

The constant is `torusPairingConstant s = 15 · 4^{s/2} · (∑ₖ W(k)^{-2})^{1/2}` in
both shapes.  The divergence-free cancellation `⟪(u·∇)v, v⟫_{L²} = 0` is **not**
used anywhere.

No `sorry`, no axiom, no named `Prop` input: every statement below is
unconditional.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open NSFormalization.Section3.T10
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open scoped BigOperators ContDiff ENNReal ComplexConjugate

-- Named, so that the normed structures on the datum carrier never collide with
-- the ones another module of this namespace installs (`logs/LESSONS.md`, 09-17).
local instance pairingNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance pairingNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Weight arithmetic

`ConvolutionBoundReal.lean` proves the same four facts as `private` lemmas, so
they are reproved here rather than exported from there. -/

private lemma wpos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight; positivity

private lemma wrpow_pos (k : PeriodicFrequency) (a : ℝ) :
    0 < periodicFrequencyWeight k ^ a :=
  Real.rpow_pos_of_pos (wpos k) a

private lemma one_le_w (k : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have h : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

/-- `1 + n² ≤ W k` for each coordinate `n = k i`. -/
private lemma coord_le (k : PeriodicFrequency) (i : Fin 3) :
    1 + (k i : ℝ) ^ 2 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have hsum : (k i : ℝ) ^ 2 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (k j : ℝ)) (Finset.mem_univ i)
  have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (k j : ℝ))]

/-- One-dimensional summability of `(1+n²)^(-a)` at every exponent `a > 1/2`. -/
private lemma coord_summable {a : ℝ} (ha : 1 / 2 < a) :
    Summable (fun n : ℤ ↦ (1 + (n : ℝ) ^ 2) ^ (-a)) := by
  have hz : Summable (fun n : ℤ ↦ if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hr : Summable (fun n : ℤ ↦ |(n : ℝ)| ^ (-(2 * a))) :=
    Real.summable_abs_int_rpow (by linarith)
  refine (hz.add hr).of_nonneg_of_le (fun n ↦ Real.rpow_nonneg (by positivity) _) ?_
  intro n
  by_cases hn : n = 0
  · subst hn
    have h1 : ((1 : ℝ) + (((0 : ℤ) : ℝ)) ^ 2) ^ (-a) = 1 := by norm_num
    have h2 : (0 : ℝ) ≤ |(((0 : ℤ)) : ℝ)| ^ (-(2 * a)) := Real.rpow_nonneg (abs_nonneg _) _
    have h3 : (if ((0 : ℤ)) = 0 then (1 : ℝ) else 0) = 1 := by norm_num
    rw [h1, h3]
    linarith
  · have hna : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    have hbase : |(n : ℝ)| ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have h1 : |(n : ℝ)| ^ (2 * a) = ((n : ℝ) ^ 2) ^ a := by
      rw [Real.rpow_mul (abs_nonneg _), hbase]
    have hle : |(n : ℝ)| ^ (2 * a) ≤ (1 + (n : ℝ) ^ 2) ^ a := by
      rw [h1]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
    have h4 : (if n = 0 then (1 : ℝ) else 0) = 0 := by rw [ite_eq_right (by exact hn)]
    rw [h4, zero_add, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2),
      Real.rpow_neg (abs_nonneg _), inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hna _) hle

/-- **Lattice summability of `W^(-r)` at every real exponent `r > 3/2`.**
`Paper1.PeriodicInverseWeightSummable` only covers `r = 3`; the tame estimate
needs `r = 2`, which is what makes the `H²` factor (rather than an `H³` factor)
legitimate.  The proof splits the weight across the three coordinates,
`W(k)^r ≥ ∏ᵢ (1 + kᵢ²)^(r/3)`, and each coordinate series converges because
`2r/3 > 1`. -/
theorem torusInverseWeight_summable {r : ℝ} (hr : 3 / 2 < r) :
    Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ (-r)) := by
  have ha : 1 / 2 < r / 3 := by linarith
  have hc := coord_summable ha
  have hn : ∀ n : ℤ, 0 ≤ (1 + (n : ℝ) ^ 2) ^ (-(r / 3)) :=
    fun n ↦ Real.rpow_nonneg (by positivity) _
  have hprod : Summable (fun k : PeriodicFrequency ↦
      (1 + (k 0 : ℝ) ^ 2) ^ (-(r / 3)) * (1 + (k 1 : ℝ) ^ 2) ^ (-(r / 3)) *
        (1 + (k 2 : ℝ) ^ 2) ^ (-(r / 3))) := by
    have hab := hc.mul_of_nonneg hc hn hn
    have habc := hab.mul_of_nonneg hc (fun q ↦ mul_nonneg (hn q.1) (hn q.2)) hn
    apply habc.comp_injective (i := fun k : PeriodicFrequency ↦ ((k 0, k 1), k 2))
    intro k l h
    have h0 : k 0 = l 0 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.1.1) h
    have h1 : k 1 = l 1 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.1.2) h
    have h2 : k 2 = l 2 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.2) h
    funext i
    fin_cases i <;> assumption
  refine hprod.of_nonneg_of_le (fun k ↦ Real.rpow_nonneg (wpos k).le _) ?_
  intro k
  have hr0 : 0 < r / 3 := by linarith
  have hstep : ∀ i : Fin 3,
      (1 + (k i : ℝ) ^ 2) ^ (r / 3) ≤ periodicFrequencyWeight k ^ (r / 3) := fun i ↦
    Real.rpow_le_rpow (by positivity) (coord_le k i) hr0.le
  have hcube : periodicFrequencyWeight k ^ (r / 3) *
      periodicFrequencyWeight k ^ (r / 3) * periodicFrequencyWeight k ^ (r / 3) =
      periodicFrequencyWeight k ^ r := by
    rw [← Real.rpow_add (wpos k), ← Real.rpow_add (wpos k)]
    ring_nf
  have hle : (1 + (k 0 : ℝ) ^ 2) ^ (r / 3) * (1 + (k 1 : ℝ) ^ 2) ^ (r / 3) *
      (1 + (k 2 : ℝ) ^ 2) ^ (r / 3) ≤ periodicFrequencyWeight k ^ r := by
    rw [← hcube]
    have p1 : (0 : ℝ) ≤ (1 + (k 1 : ℝ) ^ 2) ^ (r / 3) := Real.rpow_nonneg (by positivity) _
    have p2 : (0 : ℝ) ≤ (1 + (k 2 : ℝ) ^ 2) ^ (r / 3) := Real.rpow_nonneg (by positivity) _
    have q0 : (0 : ℝ) ≤ periodicFrequencyWeight k ^ (r / 3) := Real.rpow_nonneg (wpos k).le _
    exact mul_le_mul (mul_le_mul (hstep 0) (hstep 1) p1 q0) (hstep 2) p2 (by positivity)
  have hpos : (0 : ℝ) < (1 + (k 0 : ℝ) ^ 2) ^ (r / 3) * (1 + (k 1 : ℝ) ^ 2) ^ (r / 3) *
      (1 + (k 2 : ℝ) ^ 2) ^ (r / 3) := by
    have p0 : (0 : ℝ) < (1 + (k 0 : ℝ) ^ 2) ^ (r / 3) := Real.rpow_pos_of_pos (by positivity) _
    have p1 : (0 : ℝ) < (1 + (k 1 : ℝ) ^ 2) ^ (r / 3) := Real.rpow_pos_of_pos (by positivity) _
    have p2 : (0 : ℝ) < (1 + (k 2 : ℝ) ^ 2) ^ (r / 3) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  rw [Real.rpow_neg (wpos k).le, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (k 0 : ℝ) ^ 2),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (k 1 : ℝ) ^ 2),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (k 2 : ℝ) ^ 2),
    ← mul_inv, ← mul_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hle

/-- The lattice tail constant of the tame estimate, `∑ₖ W(k)^{-2}`. -/
def torusInverseWeightSum : ℝ := ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ (-2 : ℝ)

theorem torusInverseWeightSum_summable :
    Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ (-2 : ℝ)) :=
  torusInverseWeight_summable (by norm_num)

theorem torusInverseWeightSum_pos : 0 < torusInverseWeightSum := by
  have h : periodicFrequencyWeight 0 ^ (-2 : ℝ) ≤ torusInverseWeightSum :=
    torusInverseWeightSum_summable.le_tsum 0 (fun b _ ↦ (wrpow_pos b _).le)
  exact lt_of_lt_of_le (wrpow_pos 0 _) h

/-- **Peetre's inequality at a nonnegative real exponent.**  `W(k) ≤ 4 max (W l) (W (k-l))`
on the lattice, so `W(k)^a ≤ 4^a (W(l)^a + W(k-l)^a)`. -/
theorem torusWeightPeetre {a : ℝ} (ha : 0 ≤ a) (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ^ a ≤
      (4 : ℝ) ^ a *
        (periodicFrequencyWeight l ^ a + periodicFrequencyWeight (k - l) ^ a) := by
  have hmax : periodicFrequencyWeight k ≤
      4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) := by
    have h := NSFormalization.Paper1.PeriodicWeightShift.weight_add_le l (k - l)
    rw [add_sub_cancel] at h
    rw [← torus_weight_eq, ← torus_weight_eq, ← torus_weight_eq] at h
    have h1 := le_max_left (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
    have h2 := le_max_right (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
    linarith
  have hMpos : 0 < max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) :=
    lt_of_lt_of_le (wpos l) (le_max_left _ _)
  have h1 : periodicFrequencyWeight k ^ a ≤
      (4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a :=
    Real.rpow_le_rpow (wpos k).le hmax ha
  have h2 : (4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a =
      (4 : ℝ) ^ a * (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a :=
    Real.mul_rpow (by norm_num) hMpos.le
  have h3 : (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a ≤
      periodicFrequencyWeight l ^ a + periodicFrequencyWeight (k - l) ^ a := by
    rcases max_cases (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith [(wrpow_pos (k - l) a).le]
    · rw [he]; linarith [(wrpow_pos l a).le]
  calc periodicFrequencyWeight k ^ a ≤ _ := h1
    _ = (4 : ℝ) ^ a * (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) a)

/-- **One derivative costs half a weight.**  `|2πkⱼ| ≤ W(k)^{1/2}`. -/
theorem torusDerivativeSymbol_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ ≤ periodicFrequencyWeight k ^ ((1 : ℝ) / 2) := by
  have hsq : ‖periodicDerivativeSymbol j k‖ ^ 2 ≤ periodicFrequencyWeight k := by
    have h := Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
    simp only [periodicDerivativeSymbol, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, mul_one, Complex.norm_intCast, mul_pow, sq_abs]
    unfold periodicFrequencyWeight
    nlinarith [sq_nonneg Real.pi]
  rw [← Real.sqrt_eq_rpow]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

/-! ## 2. The trilinear convolution estimate on the lattice square

`∑_{k,l} X(k) Y(l) β(k-l) ≤ ‖X‖_{ℓ²} ‖Y‖_{ℓ²} ‖β‖_{ℓ¹}`: one Cauchy--Schwarz on
`Z³ × Z³` against the convolution measure `β(k-l)`, whose two marginals are
`(∑X²)(∑β)` and `(∑Y²)(∑β)`.  This is the only place where the three factors of
the tame estimate are separated. -/

private lemma tsum_prod_mul {f g : PeriodicFrequency → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k) :
    (∑' q : PeriodicFrequency × PeriodicFrequency, f q.1 * g q.2) = (∑' k, f k) * (∑' k, g k) := by
  rw [(hf.mul_of_nonneg hg hf0 hg0).tsum_prod]
  simp only [tsum_mul_left, tsum_mul_right]

private def shiftEquivFst : PeriodicFrequency × PeriodicFrequency ≃
    PeriodicFrequency × PeriodicFrequency where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def shiftEquivSnd : PeriodicFrequency × PeriodicFrequency ≃
    PeriodicFrequency × PeriodicFrequency where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private lemma shiftFst_inj : Function.Injective
    (fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.1, p.1 - p.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  have h3 : a.2 = b.2 := by
    have hz : a.1 - (a.1 - a.2) = b.1 - (b.1 - b.2) := by rw [h.2, h.1]
    simpa using hz
  exact Prod.ext h.1 h3

private lemma shiftSnd_inj : Function.Injective
    (fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.2, p.1 - p.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  have h3 : a.1 = b.1 := by
    have hz : a.1 - a.2 + a.2 = b.1 - b.2 + b.2 := by rw [h.2, h.1]
    simpa using hz
  exact Prod.ext h3 h.1

private lemma sq_shift_sum {X β : PeriodicFrequency → ℝ} (hβ0 : ∀ k, 0 ≤ β k)
    (hX : Summable (fun k ↦ X k ^ 2)) (hβ : Summable β) :
    Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦ X p.1 ^ 2 * β (p.1 - p.2)) ∧
      (∑' p : PeriodicFrequency × PeriodicFrequency, X p.1 ^ 2 * β (p.1 - p.2)) =
        (∑' k, X k ^ 2) * (∑' k, β k) := by
  have hb := hX.mul_of_nonneg hβ (fun k ↦ sq_nonneg (X k)) hβ0
  have hs : Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦
      X p.1 ^ 2 * β (p.1 - p.2)) :=
    hb.comp_injective (i := fun p : PeriodicFrequency × PeriodicFrequency ↦
      (p.1, p.1 - p.2)) shiftFst_inj
  have he1 : (∑' p : PeriodicFrequency × PeriodicFrequency, X p.1 ^ 2 * β (p.1 - p.2)) =
      ∑' q : PeriodicFrequency × PeriodicFrequency, X q.1 ^ 2 * β q.2 :=
    shiftEquivFst.tsum_eq (fun q : PeriodicFrequency × PeriodicFrequency ↦ X q.1 ^ 2 * β q.2)
  have he2 : (∑' q : PeriodicFrequency × PeriodicFrequency, X q.1 ^ 2 * β q.2) =
      (∑' k, X k ^ 2) * (∑' k, β k) :=
    tsum_prod_mul hX hβ (fun k ↦ sq_nonneg (X k)) hβ0
  exact ⟨hs, he1.trans he2⟩

private lemma sq_shift_sum' {Y β : PeriodicFrequency → ℝ} (hβ0 : ∀ k, 0 ≤ β k)
    (hY : Summable (fun k ↦ Y k ^ 2)) (hβ : Summable β) :
    Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦ Y p.2 ^ 2 * β (p.1 - p.2)) ∧
      (∑' p : PeriodicFrequency × PeriodicFrequency, Y p.2 ^ 2 * β (p.1 - p.2)) =
        (∑' k, Y k ^ 2) * (∑' k, β k) := by
  have hb := hY.mul_of_nonneg hβ (fun k ↦ sq_nonneg (Y k)) hβ0
  have hs : Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦
      Y p.2 ^ 2 * β (p.1 - p.2)) :=
    hb.comp_injective (i := fun p : PeriodicFrequency × PeriodicFrequency ↦
      (p.2, p.1 - p.2)) shiftSnd_inj
  have he1 : (∑' p : PeriodicFrequency × PeriodicFrequency, Y p.2 ^ 2 * β (p.1 - p.2)) =
      ∑' q : PeriodicFrequency × PeriodicFrequency, Y q.1 ^ 2 * β q.2 :=
    shiftEquivSnd.tsum_eq (fun q : PeriodicFrequency × PeriodicFrequency ↦ Y q.1 ^ 2 * β q.2)
  have he2 : (∑' q : PeriodicFrequency × PeriodicFrequency, Y q.1 ^ 2 * β q.2) =
      (∑' k, Y k ^ 2) * (∑' k, β k) :=
    tsum_prod_mul hY hβ (fun k ↦ sq_nonneg (Y k)) hβ0
  exact ⟨hs, he1.trans he2⟩

/-- **The trilinear convolution estimate.** -/
theorem torusTrilinearConvolution {X Y β : PeriodicFrequency → ℝ}
    (hX0 : ∀ k, 0 ≤ X k) (hY0 : ∀ k, 0 ≤ Y k) (hβ0 : ∀ k, 0 ≤ β k)
    (hX : Summable (fun k ↦ X k ^ 2)) (hY : Summable (fun k ↦ Y k ^ 2))
    (hβ : Summable β) :
    Summable (fun p : PeriodicFrequency × PeriodicFrequency ↦
        X p.1 * Y p.2 * β (p.1 - p.2)) ∧
      (∑' p : PeriodicFrequency × PeriodicFrequency, X p.1 * Y p.2 * β (p.1 - p.2)) ≤
        Real.sqrt (∑' k, X k ^ 2) * Real.sqrt (∑' k, Y k ^ 2) * (∑' k, β k) := by
  have hsqβ : ∀ n : PeriodicFrequency, Real.sqrt (β n) * Real.sqrt (β n) = β n :=
    fun n ↦ Real.mul_self_sqrt (hβ0 n)
  have hFval : ∀ p : PeriodicFrequency × PeriodicFrequency,
      ‖X p.1 * Real.sqrt (β (p.1 - p.2))‖ ^ (2 : ℝ≥0∞).toReal = X p.1 ^ 2 * β (p.1 - p.2) := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX0 _) (Real.sqrt_nonneg _))]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow, sq, sq, hsqβ]
  have hGval : ∀ p : PeriodicFrequency × PeriodicFrequency,
      ‖Y p.2 * Real.sqrt (β (p.1 - p.2))‖ ^ (2 : ℝ≥0∞).toReal = Y p.2 ^ 2 * β (p.1 - p.2) := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hY0 _) (Real.sqrt_nonneg _))]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow, sq, sq, hsqβ]
  obtain ⟨hFs, hFe⟩ := sq_shift_sum (X := X) hβ0 hX hβ
  obtain ⟨hGs, hGe⟩ := sq_shift_sum' (Y := Y) hβ0 hY hβ
  let F : lp (fun _ : PeriodicFrequency × PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun p ↦ X p.1 * Real.sqrt (β (p.1 - p.2)), memℓp_gen (hFs.congr (fun p ↦ (hFval p).symm))⟩
  let G : lp (fun _ : PeriodicFrequency × PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun p ↦ Y p.2 * Real.sqrt (β (p.1 - p.2)), memℓp_gen (hGs.congr (fun p ↦ (hGval p).symm))⟩
  have hFn : ‖F‖ = Real.sqrt ((∑' k, X k ^ 2) * (∑' k, β k)) := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) F
    rw [show (∑' p : PeriodicFrequency × PeriodicFrequency,
        ‖F p‖ ^ (2 : ℝ≥0∞).toReal) = (∑' k, X k ^ 2) * (∑' k, β k) from
      Eq.trans (tsum_congr fun p ↦ hFval p) hFe] at h
    rw [← h]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sqrt_sq (norm_nonneg F)]
  have hGn : ‖G‖ = Real.sqrt ((∑' k, Y k ^ 2) * (∑' k, β k)) := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) G
    rw [show (∑' p : PeriodicFrequency × PeriodicFrequency,
        ‖G p‖ ^ (2 : ℝ≥0∞).toReal) = (∑' k, Y k ^ 2) * (∑' k, β k) from
      Eq.trans (tsum_congr fun p ↦ hGval p) hGe] at h
    rw [← h]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sqrt_sq (norm_nonneg G)]
  have hprodval : ∀ p : PeriodicFrequency × PeriodicFrequency,
      ‖F p‖ * ‖G p‖ = X p.1 * Y p.2 * β (p.1 - p.2) := by
    intro p
    change ‖X p.1 * Real.sqrt (β (p.1 - p.2))‖ * ‖Y p.2 * Real.sqrt (β (p.1 - p.2))‖ = _
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hX0 _) (Real.sqrt_nonneg _)),
      abs_of_nonneg (mul_nonneg (hY0 _) (Real.sqrt_nonneg _))]
    calc X p.1 * Real.sqrt (β (p.1 - p.2)) * (Y p.2 * Real.sqrt (β (p.1 - p.2)))
        = X p.1 * Y p.2 * (Real.sqrt (β (p.1 - p.2)) * Real.sqrt (β (p.1 - p.2))) := by ring
      _ = X p.1 * Y p.2 * β (p.1 - p.2) := by rw [hsqβ]
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two) F G
  refine ⟨hh.1.congr hprodval, ?_⟩
  have hb := hh.2
  rw [tsum_congr hprodval, hFn, hGn] at hb
  refine hb.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (tsum_nonneg fun k ↦ sq_nonneg (X k)),
    Real.sqrt_mul (tsum_nonneg fun k ↦ sq_nonneg (Y k))]
  have hβs : Real.sqrt (∑' k, β k) * Real.sqrt (∑' k, β k) = ∑' k, β k :=
    Real.mul_self_sqrt (tsum_nonneg hβ0)
  calc Real.sqrt (∑' k, X k ^ 2) * Real.sqrt (∑' k, β k) *
        (Real.sqrt (∑' k, Y k ^ 2) * Real.sqrt (∑' k, β k))
      = Real.sqrt (∑' k, X k ^ 2) * Real.sqrt (∑' k, Y k ^ 2) *
        (Real.sqrt (∑' k, β k) * Real.sqrt (∑' k, β k)) := by ring
    _ = _ := by rw [hβs]


/-! ## 3. Weighted absolute coefficients of one datum

The torus carrier is phantom-indexed, so one datum `A` at order `r` carries the
whole scale: `wAbs r s A i k = W(k)^((s-r)/2) |Aᵢ(k)|` is the absolute value of
the order-`s` coefficient of the same field, i.e. of `torusOrderDown r s A`. -/

private lemma rpow_two_norm (x : ℝ) : ‖x‖ ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

private lemma lp_norm_eq_sqrt (F : lp (fun _ : PeriodicFrequency ↦ ℝ) 2) :
    ‖F‖ = Real.sqrt (∑' k, (F k) ^ 2) := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) F
  rw [show (∑' k : PeriodicFrequency, ‖F k‖ ^ (2 : ℝ≥0∞).toReal) = ∑' k, (F k) ^ 2 from
    tsum_congr fun k ↦ rpow_two_norm (F k)] at h
  rw [← h]
  simp only [ENNReal.toReal_ofNat]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.sqrt_sq (norm_nonneg F)]

private def realLp (f : PeriodicFrequency → ℝ) (hf : Summable (fun k ↦ f k ^ 2)) :
    lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
  ⟨f, memℓp_gen (hf.congr fun k ↦ (rpow_two_norm (f k)).symm)⟩

private lemma realLp_apply (f : PeriodicFrequency → ℝ) (hf : Summable (fun k ↦ f k ^ 2))
    (k : PeriodicFrequency) : (realLp f hf) k = f k := rfl

/-- The `H^s`-weighted absolute Fourier coefficient of the order-`r` datum `A`. -/
private def wAbs (r s : ℝ) (A : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k ^ ((s - r) / 2) * ‖A.1 i k‖

private lemma wAbs_nonneg (r s : ℝ) (A : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) : 0 ≤ wAbs r s A i k :=
  mul_nonneg (wrpow_pos k _).le (norm_nonneg _)

/-- `wAbs` is the absolute coefficient of the order-descended datum. -/
private lemma wAbs_eq_down {r s : ℝ} (h : s ≤ r) (A : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    wAbs r s A i k = ‖(torusOrderDown r s h A).1 i k‖ := by
  rw [torusOrderDown_reweight r s h A i k, norm_smul, Real.norm_eq_abs,
    abs_of_pos (wrpow_pos k _)]
  rfl

/-- Multiplying `wAbs` by a power of the weight shifts the order. -/
private lemma wAbs_shift (r s a : ℝ) (A : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ a * wAbs r s A i k = wAbs r (s + 2 * a) A i k := by
  unfold wAbs
  rw [← mul_assoc, ← Real.rpow_add (wpos k)]
  ring_nf

/-- The order-`s` energy of one component. -/
private lemma wAbs_energy {r s : ℝ} (h : s ≤ r) (A : PeriodicSobolev r) (i : Fin 3) :
    Summable (fun k ↦ (wAbs r s A i k) ^ 2) ∧
      (∑' k, (wAbs r s A i k) ^ 2) = ‖(torusOrderDown r s h A).1 i‖ ^ 2 := by
  have hfun : (fun k ↦ (wAbs r s A i k) ^ 2) =
      fun k ↦ ‖(torusOrderDown r s h A).1 i k‖ ^ 2 := by
    funext k; rw [wAbs_eq_down h A i k]
  rw [hfun]
  refine ⟨by simpa using (lp.memℓp ((torusOrderDown r s h A).1 i)).summable (by norm_num), ?_⟩
  simpa using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      ((torusOrderDown r s h A).1 i)).symm

private lemma wAbs_energy_le {r s : ℝ} (h : s ≤ r) (A : PeriodicSobolev r) (i : Fin 3) :
    Real.sqrt (∑' k, (wAbs r s A i k) ^ 2) ≤ ‖torusOrderDown r s h A‖ := by
  rw [(wAbs_energy h A i).2]
  have hc : ‖(torusOrderDown r s h A).1 i‖ ≤ ‖torusOrderDown r s h A‖ :=
    PiLp.norm_apply_le (torusOrderDown r s h A).1 i
  rw [Real.sqrt_sq (norm_nonneg _)]
  exact hc

/-- The `ℓ¹` norm of the **unweighted** coefficients is controlled by the `H²`
datum, through `∑ₖ W(k)^{-2} < ∞`.  This is the factor that makes the estimate
tame. -/
private lemma wAbs_zero_l1 {r : ℝ} (hr : (2 : ℝ) ≤ r) (A : PeriodicSobolev r) (i : Fin 3) :
    Summable (fun k ↦ wAbs r 0 A i k) ∧
      (∑' k, wAbs r 0 A i k) ≤
        Real.sqrt torusInverseWeightSum * ‖torusOrderDown r 2 hr A‖ := by
  have hsplit : ∀ k, periodicFrequencyWeight k ^ (-1 : ℝ) * wAbs r 2 A i k = wAbs r 0 A i k := by
    intro k
    rw [wAbs_shift r 2 (-1) A i k]
    norm_num
  have hinv : ∀ k : PeriodicFrequency,
      (periodicFrequencyWeight k ^ (-1 : ℝ)) ^ 2 = periodicFrequencyWeight k ^ (-2 : ℝ) := by
    intro k
    rw [← Real.rpow_natCast (periodicFrequencyWeight k ^ (-1 : ℝ)) 2,
      ← Real.rpow_mul (wpos k).le]
    norm_num
  have hu : Summable (fun k ↦ (periodicFrequencyWeight k ^ (-1 : ℝ)) ^ 2) :=
    torusInverseWeightSum_summable.congr fun k ↦ (hinv k).symm
  have hv := (wAbs_energy (s := 2) hr A i).1
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two)
    (realLp (fun k ↦ periodicFrequencyWeight k ^ (-1 : ℝ)) hu) (realLp (fun k ↦ wAbs r 2 A i k) hv)
  have hval : ∀ k, ‖(realLp (fun k ↦ periodicFrequencyWeight k ^ (-1 : ℝ)) hu) k‖ *
      ‖(realLp (fun k ↦ wAbs r 2 A i k) hv) k‖ = wAbs r 0 A i k := by
    intro k
    rw [realLp_apply, realLp_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (wrpow_pos k _), abs_of_nonneg (wAbs_nonneg r 2 A i k), hsplit k]
  refine ⟨hh.1.congr hval, ?_⟩
  have hb := hh.2
  rw [tsum_congr hval] at hb
  have hUn : ‖realLp (fun k ↦ periodicFrequencyWeight k ^ (-1 : ℝ)) hu‖ =
      Real.sqrt torusInverseWeightSum := by
    rw [lp_norm_eq_sqrt]
    congr 1
    exact tsum_congr fun k ↦ by rw [realLp_apply]; exact hinv k
  have hVn : ‖realLp (fun k ↦ wAbs r 2 A i k) hv‖ ≤ ‖torusOrderDown r 2 hr A‖ := by
    rw [lp_norm_eq_sqrt]
    have heq : (∑' k, ((realLp (fun k ↦ wAbs r 2 A i k) hv) k) ^ 2) =
        ∑' k, (wAbs r 2 A i k) ^ 2 := tsum_congr fun k ↦ by rw [realLp_apply]
    rw [heq]
    exact wAbs_energy_le (s := 2) hr A i
  rw [hUn] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hVn (Real.sqrt_nonneg _))

/-- The three components together: the convection sums over `j`, so the `j`-sum
is absorbed into the coefficient function once and for all. -/
private def wTot (r s : ℝ) (A : PeriodicSobolev r) (k : PeriodicFrequency) : ℝ :=
  ∑ j : Fin 3, wAbs r s A j k

private lemma wTot_eq (r s : ℝ) (A : PeriodicSobolev r) (k : PeriodicFrequency) :
    wTot r s A k = wAbs r s A 0 k + wAbs r s A 1 k + wAbs r s A 2 k :=
  Fin.sum_univ_three _

private lemma wTot_nonneg (r s : ℝ) (A : PeriodicSobolev r) (k : PeriodicFrequency) :
    0 ≤ wTot r s A k :=
  Finset.sum_nonneg fun j _ ↦ wAbs_nonneg r s A j k

private lemma wAbs_sum_energy {r s : ℝ} (h : s ≤ r) (A : PeriodicSobolev r) :
    (∑' k, (wAbs r s A 0 k) ^ 2) + (∑' k, (wAbs r s A 1 k) ^ 2) +
      (∑' k, (wAbs r s A 2 k) ^ 2) = ‖torusOrderDown r s h A‖ ^ 2 := by
  have hnorm : ‖torusOrderDown r s h A‖ ^ 2 =
      ∑ i : Fin 3, ‖(torusOrderDown r s h A).1 i‖ ^ 2 := by
    change ‖(torusOrderDown r s h A).1‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
  rw [hnorm, Fin.sum_univ_three, (wAbs_energy h A 0).2, (wAbs_energy h A 1).2,
    (wAbs_energy h A 2).2]

private lemma wTot_energy {r s : ℝ} (h : s ≤ r) (A : PeriodicSobolev r) :
    Summable (fun k ↦ (wTot r s A k) ^ 2) ∧
      Real.sqrt (∑' k, (wTot r s A k) ^ 2) ≤ 2 * ‖torusOrderDown r s h A‖ := by
  have h0 := (wAbs_energy h A 0).1
  have h1 := (wAbs_energy h A 1).1
  have h2 := (wAbs_energy h A 2).1
  have hmaj : Summable (fun k ↦ 3 * ((wAbs r s A 0 k) ^ 2 + (wAbs r s A 1 k) ^ 2 +
      (wAbs r s A 2 k) ^ 2)) := ((h0.add h1).add h2).mul_left 3
  have hle : ∀ k, (wTot r s A k) ^ 2 ≤
      3 * ((wAbs r s A 0 k) ^ 2 + (wAbs r s A 1 k) ^ 2 + (wAbs r s A 2 k) ^ 2) := by
    intro k
    rw [wTot_eq]
    nlinarith [sq_nonneg (wAbs r s A 0 k - wAbs r s A 1 k),
      sq_nonneg (wAbs r s A 0 k - wAbs r s A 2 k),
      sq_nonneg (wAbs r s A 1 k - wAbs r s A 2 k)]
  have hsum : Summable (fun k ↦ (wTot r s A k) ^ 2) :=
    hmaj.of_nonneg_of_le (fun k ↦ sq_nonneg _) hle
  refine ⟨hsum, ?_⟩
  have hbound : (∑' k, (wTot r s A k) ^ 2) ≤ 3 * ‖torusOrderDown r s h A‖ ^ 2 := by
    refine (hsum.tsum_le_tsum hle hmaj).trans (le_of_eq ?_)
    rw [tsum_mul_left, (h0.add h1).tsum_add h2, h0.tsum_add h1, wAbs_sum_energy h A]
  have hsq : (∑' k, (wTot r s A k) ^ 2) ≤ (2 * ‖torusOrderDown r s h A‖) ^ 2 := by
    nlinarith [norm_nonneg (torusOrderDown r s h A)]
  calc Real.sqrt (∑' k, (wTot r s A k) ^ 2)
      ≤ Real.sqrt ((2 * ‖torusOrderDown r s h A‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * ‖torusOrderDown r s h A‖ := Real.sqrt_sq (by positivity)

private lemma wTot_l1 {r : ℝ} (hr : (2 : ℝ) ≤ r) (A : PeriodicSobolev r) :
    Summable (fun k ↦ wTot r 0 A k) ∧
      (∑' k, wTot r 0 A k) ≤
        3 * Real.sqrt torusInverseWeightSum * ‖torusOrderDown r 2 hr A‖ := by
  obtain ⟨s0, b0⟩ := wAbs_zero_l1 hr A 0
  obtain ⟨s1, b1⟩ := wAbs_zero_l1 hr A 1
  obtain ⟨s2, b2⟩ := wAbs_zero_l1 hr A 2
  have hfun : (fun k ↦ wTot r 0 A k) =
      fun k ↦ wAbs r 0 A 0 k + wAbs r 0 A 1 k + wAbs r 0 A 2 k := funext (wTot_eq r 0 A)
  rw [hfun]
  refine ⟨(s0.add s1).add s2, ?_⟩
  rw [(s0.add s1).tsum_add s2, s0.tsum_add s1]
  linarith

/-! ## 4. The pointwise bound on the convection symbol -/

private lemma wAbs_zero_eq (r : ℝ) (A : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) :
    wAbs r 0 A i k = periodicFrequencyWeight k ^ (-r / 2) * ‖A.1 i k‖ := by
  unfold wAbs
  norm_num

private lemma wAbs_self (r : ℝ) (A : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) :
    wAbs r r A i k = ‖A.1 i k‖ := by
  unfold wAbs
  rw [sub_self, zero_div, Real.rpow_zero, one_mul]

private lemma wAbs_top_energy (r : ℝ) (A : PeriodicSobolev r) (i : Fin 3) :
    Summable (fun k ↦ (wAbs r r A i k) ^ 2) ∧
      Real.sqrt (∑' k, (wAbs r r A i k) ^ 2) ≤ ‖A‖ := by
  have hfun : (fun k ↦ (wAbs r r A i k) ^ 2) = fun k ↦ ‖A.1 i k‖ ^ 2 := by
    funext k; rw [wAbs_self]
  rw [hfun]
  refine ⟨by simpa using (lp.memℓp (A.1 i)).summable (by norm_num), ?_⟩
  have heq : (∑' k, ‖A.1 i k‖ ^ 2) = ‖A.1 i‖ ^ 2 := by
    simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A.1 i)).symm
  rw [heq, Real.sqrt_sq (norm_nonneg _)]
  exact PiLp.norm_apply_le A.1 i

private lemma wTot_shift (r s a : ℝ) (A : PeriodicSobolev r) (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ a * wTot r s A k = wTot r (s + 2 * a) A k := by
  unfold wTot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ wAbs_shift r s a A j k

private lemma conv_summable {r : ℝ} (hr : (2 : ℝ) ≤ r) (A : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    Summable (fun l ↦ wTot r 0 A l * wAbs r 0 A i (k - l)) := by
  obtain ⟨hs, _⟩ := wTot_l1 hr A
  obtain ⟨hi, _⟩ := wAbs_zero_l1 hr A i
  have hb : ∀ n, wAbs r 0 A i n ≤ ∑' n, wAbs r 0 A i n :=
    fun n ↦ hi.le_tsum n fun b _ ↦ wAbs_nonneg r 0 A i b
  refine (hs.mul_right (∑' n, wAbs r 0 A i n)).of_nonneg_of_le
    (fun l ↦ mul_nonneg (wTot_nonneg r 0 A l) (wAbs_nonneg r 0 A i (k - l))) ?_
  intro l
  exact mul_le_mul_of_nonneg_left (hb (k - l)) (wTot_nonneg r 0 A l)

private lemma conv_summable' {r : ℝ} (hr : (2 : ℝ) ≤ r) (A : PeriodicSobolev r) (i j : Fin 3)
    (k : PeriodicFrequency) :
    Summable (fun l ↦ wAbs r 0 A j l * wAbs r 0 A i (k - l)) := by
  obtain ⟨hs, _⟩ := wAbs_zero_l1 hr A j
  obtain ⟨hi, _⟩ := wAbs_zero_l1 hr A i
  have hb : ∀ n, wAbs r 0 A i n ≤ ∑' n, wAbs r 0 A i n :=
    fun n ↦ hi.le_tsum n fun b _ ↦ wAbs_nonneg r 0 A i b
  refine (hs.mul_right (∑' n, wAbs r 0 A i n)).of_nonneg_of_le
    (fun l ↦ mul_nonneg (wAbs_nonneg r 0 A j l) (wAbs_nonneg r 0 A i (k - l))) ?_
  intro l
  exact mul_le_mul_of_nonneg_left (hb (k - l)) (wAbs_nonneg r 0 A j l)

private lemma conv_term_norm {r : ℝ} (A : PeriodicSobolev r) (i j : Fin 3)
    (k l : PeriodicFrequency) :
    ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
        ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * A.1 i (k - l)‖ =
      wAbs r 0 A j l * wAbs r 0 A i (k - l) := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (wrpow_pos l _),
    abs_of_pos (wrpow_pos (k - l) _), wAbs_zero_eq, wAbs_zero_eq]
  ring

/-- **The convection symbol is bounded by the unweighted convolution.**
The derivative symbol `2πi kⱼ` costs `W(k)^{1/2}`, which together with the output
weight `W(k)^{(r-1)/2}` gives `W(k)^{r/2}`; the `j`-sum is absorbed into `wTot`. -/
private lemma symbol_norm_le {r : ℝ} (hr : (2 : ℝ) ≤ r) (A : PeriodicSobolev r) (i : Fin 3)
    (k : PeriodicFrequency) :
    ‖torusConvectionSymbolReal r A A i k‖ ≤
      periodicFrequencyWeight k ^ (r / 2) * ∑' l, wTot r 0 A l * wAbs r 0 A i (k - l) := by
  have hinner : ∀ j : Fin 3,
      ‖∑' l : PeriodicFrequency,
        ((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * A.1 i (k - l)‖ ≤
        ∑' l, wAbs r 0 A j l * wAbs r 0 A i (k - l) := by
    intro j
    have hs : Summable (fun l : PeriodicFrequency ↦
        ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * A.1 j l *
          ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * A.1 i (k - l)‖) :=
      (conv_summable' hr A i j k).congr fun l ↦ (conv_term_norm A i j k l).symm
    refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
    exact tsum_congr fun l ↦ conv_term_norm A i j k l
  have hstep : ‖torusConvectionSymbolReal r A A i k‖ ≤
      periodicFrequencyWeight k ^ ((r - 1) / 2) *
        ∑ j : Fin 3, periodicFrequencyWeight k ^ ((1 : ℝ) / 2) *
          (∑' l, wAbs r 0 A j l * wAbs r 0 A i (k - l)) := by
    unfold torusConvectionSymbolReal
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wrpow_pos k _)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (wrpow_pos k _).le
    refine Finset.sum_le_sum fun j _ ↦ ?_
    rw [norm_mul]
    exact mul_le_mul (torusDerivativeSymbol_le j k) (hinner j) (norm_nonneg _)
      (wrpow_pos k _).le
  refine hstep.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← mul_assoc, ← Real.rpow_add (wpos k)]
  rw [show (r - 1) / 2 + (1 : ℝ) / 2 = r / 2 by ring]
  congr 1
  rw [← Summable.tsum_finsetSum fun j (_ : j ∈ Finset.univ) ↦ conv_summable' hr A i j k]
  exact tsum_congr fun l ↦ by rw [wTot]; rw [Finset.sum_mul]

/-! ## 8. Peetre with one derivative

The tame estimate of `eq:Rhigh` measures the top factor in `‖∇u‖_{H^m}`, not in
`‖u‖_{H^{m+1}}` — and the two are *not* interchangeable (a nonzero constant field
has zero gradient).  The additive Peetre inequality of §1 puts the derivative on
the output frequency and therefore produces `‖u‖_{H^{m+1}}`; what produces the
gradient norm is the *region* split `|l| ≤ |k-l|` versus `>`, which the following
single inequality packages: on each region the larger of the two summand
frequencies dominates both the weight and the derivative amplitude. -/

/-- `|2πk|`, the amplitude of the gradient symbol at frequency `k`. -/
def torusFreqAmp (k : PeriodicFrequency) : ℝ := Real.sqrt (periodicAngularFrequencySq k)

theorem torusFreqAmp_nonneg (k : PeriodicFrequency) : 0 ≤ torusFreqAmp k := Real.sqrt_nonneg _

theorem weight_eq_one_add_angular (k : PeriodicFrequency) :
    periodicFrequencyWeight k = 1 + periodicAngularFrequencySq k := rfl

theorem norm_periodicDerivativeSymbol (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ = 2 * Real.pi * |(k j : ℝ)| := by
  simp only [periodicDerivativeSymbol, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast]

theorem twoPi_abs_le_amp (j : Fin 3) (k : PeriodicFrequency) :
    2 * Real.pi * |(k j : ℝ)| ≤ torusFreqAmp k := by
  have hsq : (2 * Real.pi * |(k j : ℝ)|) ^ 2 ≤ periodicAngularFrequencySq k := by
    have h := Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
      (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
    unfold periodicAngularFrequencySq
    nlinarith [sq_nonneg Real.pi, sq_abs ((k j : ℝ)), Real.pi_pos]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at this

theorem amp_mono {k l : PeriodicFrequency}
    (h : periodicFrequencyWeight k ≤ periodicFrequencyWeight l) :
    torusFreqAmp k ≤ torusFreqAmp l := by
  apply Real.sqrt_le_sqrt
  rw [weight_eq_one_add_angular, weight_eq_one_add_angular] at h
  linarith

/-- **Peetre with one derivative.**  The output weight times the amplitude of the
gradient symbol at *either* summand frequency is controlled by the gradient
weight at the larger of the two frequencies. -/
theorem torusWeightPeetre_grad {a : ℝ} (ha : 0 ≤ a) (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ^ a * torusFreqAmp (k - l) ≤
      (4 : ℝ) ^ a * (periodicFrequencyWeight l ^ a * torusFreqAmp l +
        periodicFrequencyWeight (k - l) ^ a * torusFreqAmp (k - l)) := by
  have hmax : periodicFrequencyWeight k ≤
      4 * max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) := by
    have h := NSFormalization.Paper1.PeriodicWeightShift.weight_add_le l (k - l)
    rw [add_sub_cancel] at h
    rw [← torus_weight_eq, ← torus_weight_eq, ← torus_weight_eq] at h
    have h1 := le_max_left (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
    have h2 := le_max_right (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))
    linarith
  have hMpos : 0 < max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) :=
    lt_of_lt_of_le (wpos l) (le_max_left _ _)
  have h1 : periodicFrequencyWeight k ^ a ≤
      (4 : ℝ) ^ a * (max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a := by
    rw [← Real.mul_rpow (by norm_num) hMpos.le]
    exact Real.rpow_le_rpow (wpos k).le hmax ha
  have hpow4 : (0 : ℝ) ≤ (4 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
  have hstep : periodicFrequencyWeight k ^ a * torusFreqAmp (k - l) ≤
      (4 : ℝ) ^ a * ((max (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l))) ^ a *
        torusFreqAmp (k - l)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (torusFreqAmp_nonneg _)
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ hpow4)
  rcases max_cases (periodicFrequencyWeight l) (periodicFrequencyWeight (k - l)) with
    ⟨he, hge⟩ | ⟨he, hlt⟩
  · rw [he]
    have hamp : torusFreqAmp (k - l) ≤ torusFreqAmp l := amp_mono hge
    have hnn : (0 : ℝ) ≤ periodicFrequencyWeight l ^ a := Real.rpow_nonneg (wpos l).le a
    have h2 : (0 : ℝ) ≤ periodicFrequencyWeight (k - l) ^ a * torusFreqAmp (k - l) :=
      mul_nonneg (Real.rpow_nonneg (wpos _).le a) (torusFreqAmp_nonneg _)
    nlinarith
  · rw [he]
    have h2 : (0 : ℝ) ≤ periodicFrequencyWeight l ^ a * torusFreqAmp l :=
      mul_nonneg (Real.rpow_nonneg (wpos l).le a) (torusFreqAmp_nonneg _)
    linarith


/-! ## 5. The pairing bound -/

/-- `|⟪P, G⟫_{H^s}|` is bounded by the componentwise absolute lattice sum. -/
private lemma pairing_le_components {s : ℝ} (P G : PeriodicSobolev s) :
    |torusRealPairing P G| ≤ ∑ i : Fin 3, ∑' k, ‖P.1 i k‖ * ‖G.1 i k‖ := by
  have hcomp : ∀ i : Fin 3,
      ‖(inner ℂ (P.1 i) (G.1 i) : ℂ)‖ ≤ ∑' k, ‖P.1 i k‖ * ‖G.1 i k‖ := by
    intro i
    have hsum : Summable (fun k ↦ ‖P.1 i k‖ * ‖G.1 i k‖) :=
      (lp.tsum_mul_le_mul_norm
        (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
          simpa using Real.HolderConjugate.two_two) (P.1 i) (G.1 i)).1
    have hinner : (inner ℂ (P.1 i) (G.1 i) : ℂ) = ∑' k, conj (P.1 i k) * G.1 i k := by
      rw [lp.inner_eq_tsum]
      exact tsum_congr fun k ↦ RCLike.inner_apply' _ _
    have hterm : ∀ k, ‖conj (P.1 i k) * G.1 i k‖ = ‖P.1 i k‖ * ‖G.1 i k‖ := by
      intro k
      rw [norm_mul, RCLike.norm_conj]
    rw [hinner]
    refine (norm_tsum_le_tsum_norm (hsum.congr fun k ↦ (hterm k).symm)).trans (le_of_eq ?_)
    exact tsum_congr hterm
  have hre : |torusRealPairing P G| ≤ ‖(inner ℂ P.1 G.1 : ℂ)‖ := Complex.abs_re_le_norm _
  refine hre.trans ?_
  rw [PiLp.inner_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hcomp i)

private lemma summable_sub_left {f : PeriodicFrequency → ℝ} (hf : Summable f)
    (k : PeriodicFrequency) : Summable (fun l ↦ f (k - l)) :=
  hf.comp_injective (i := fun l : PeriodicFrequency ↦ k - l)
    (fun a b h ↦ by simpa using sub_right_injective h)

/-- The componentwise tame bound: the whole analytic content of the lane. -/
private lemma component_bound {r : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r) (h1 : r - 1 ≤ r)
    (A : PeriodicSobolev r) (i : Fin 3) :
    (∑' k, ‖(torusConvectionDatumReal hr A A).1 i k‖ *
        ‖(torusOrderDown r (r - 1) h1 A).1 i k‖) ≤
      5 * (4 : ℝ) ^ ((r - 1) / 2) * Real.sqrt torusInverseWeightSum *
        ‖torusOrderDown r 2 h2 A‖ * ‖torusOrderDown r (r - 1) h1 A‖ * ‖A‖ := by
  have ha : (0 : ℝ) ≤ (r - 1) / 2 := by linarith
  obtain ⟨hXs, hXb⟩ := wAbs_top_energy r A i
  obtain ⟨hYs, hYb⟩ := wTot_energy h1 A
  have hZs := (wAbs_energy h1 A i).1
  have hZb := wAbs_energy_le h1 A i
  obtain ⟨hβs, hβb⟩ := wAbs_zero_l1 h2 A i
  obtain ⟨hγs, hγb⟩ := wTot_l1 h2 A
  obtain ⟨hp1, hb1⟩ := torusTrilinearConvolution (X := fun k ↦ wAbs r r A i k)
    (Y := fun k ↦ wTot r (r - 1) A k) (β := fun k ↦ wAbs r 0 A i k)
    (wAbs_nonneg r r A i) (wTot_nonneg r (r - 1) A) (wAbs_nonneg r 0 A i) hXs hYs hβs
  obtain ⟨hp2, hb2⟩ := torusTrilinearConvolution (X := fun k ↦ wAbs r r A i k)
    (Y := fun k ↦ wAbs r (r - 1) A i k) (β := fun k ↦ wTot r 0 A k)
    (wAbs_nonneg r r A i) (wAbs_nonneg r (r - 1) A i) (wTot_nonneg r 0 A) hXs hZs hγs
  -- the pointwise majorant
  have hmaj : ∀ k : PeriodicFrequency,
      ‖(torusConvectionDatumReal hr A A).1 i k‖ * ‖(torusOrderDown r (r - 1) h1 A).1 i k‖ ≤
        (4 : ℝ) ^ ((r - 1) / 2) *
          ((∑' l, wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l)) +
            (∑' l, wAbs r r A i k * wAbs r (r - 1) A i l * wTot r 0 A (k - l))) := by
    intro k
    have hsym : ‖(torusConvectionDatumReal hr A A).1 i k‖ ≤
        periodicFrequencyWeight k ^ (r / 2) * ∑' l, wTot r 0 A l * wAbs r 0 A i (k - l) := by
      rw [torusConvectionDatumReal_coeff]
      exact symbol_norm_le h2 A i k
    have hdown : ‖(torusOrderDown r (r - 1) h1 A).1 i k‖ =
        periodicFrequencyWeight k ^ (-(1 : ℝ) / 2) * wAbs r r A i k := by
      rw [← wAbs_eq_down h1 A i k, wAbs_self r A i k]
      unfold wAbs
      rw [show (r - 1 - r) / 2 = -(1 : ℝ) / 2 by ring]
    have hTnn : (0 : ℝ) ≤ ∑' l, wTot r 0 A l * wAbs r 0 A i (k - l) :=
      tsum_nonneg fun l ↦ mul_nonneg (wTot_nonneg r 0 A l) (wAbs_nonneg r 0 A i (k - l))
    have hstep : ‖(torusConvectionDatumReal hr A A).1 i k‖ *
        ‖(torusOrderDown r (r - 1) h1 A).1 i k‖ ≤
        periodicFrequencyWeight k ^ ((r - 1) / 2) * wAbs r r A i k *
          ∑' l, wTot r 0 A l * wAbs r 0 A i (k - l) := by
      rw [hdown]
      refine (mul_le_mul_of_nonneg_right hsym
        (mul_nonneg (wrpow_pos k _).le (wAbs_nonneg r r A i k))).trans (le_of_eq ?_)
      rw [show periodicFrequencyWeight k ^ (r / 2) *
            (∑' l, wTot r 0 A l * wAbs r 0 A i (k - l)) *
            (periodicFrequencyWeight k ^ (-(1 : ℝ) / 2) * wAbs r r A i k) =
          periodicFrequencyWeight k ^ (r / 2) * periodicFrequencyWeight k ^ (-(1 : ℝ) / 2) *
            wAbs r r A i k * (∑' l, wTot r 0 A l * wAbs r 0 A i (k - l)) by ring,
        ← Real.rpow_add (wpos k), show r / 2 + -(1 : ℝ) / 2 = (r - 1) / 2 by ring]
    refine hstep.trans ?_
    -- Peetre inside the convolution sum
    have hshiftTot : ∀ l : PeriodicFrequency,
        periodicFrequencyWeight l ^ ((r - 1) / 2) * wTot r 0 A l = wTot r (r - 1) A l := by
      intro l
      have h := wTot_shift r 0 ((r - 1) / 2) A l
      rwa [show (0 : ℝ) + 2 * ((r - 1) / 2) = r - 1 by ring] at h
    have hshiftAbs : ∀ n : PeriodicFrequency,
        periodicFrequencyWeight n ^ ((r - 1) / 2) * wAbs r 0 A i n = wAbs r (r - 1) A i n := by
      intro n
      have h := wAbs_shift r 0 ((r - 1) / 2) A i n
      rwa [show (0 : ℝ) + 2 * ((r - 1) / 2) = r - 1 by ring] at h
    have hF1 : Summable (fun l ↦ wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l)) :=
      hp1.prod_factor k
    have hF2' : Summable (fun l ↦
        wAbs r r A i k * wTot r 0 A l * wAbs r (r - 1) A i (k - l)) := by
      refine ((summable_sub_left (hp2.prod_factor k) k).congr ?_)
      intro l
      rw [sub_sub_cancel]
      ring
    have hptwise : ∀ l : PeriodicFrequency,
        periodicFrequencyWeight k ^ ((r - 1) / 2) * wAbs r r A i k *
            (wTot r 0 A l * wAbs r 0 A i (k - l)) ≤
          (4 : ℝ) ^ ((r - 1) / 2) *
            (wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l) +
              wAbs r r A i k * wTot r 0 A l * wAbs r (r - 1) A i (k - l)) := by
      intro l
      have hpe := torusWeightPeetre ha k l
      have hcoef : (0 : ℝ) ≤ wAbs r r A i k * (wTot r 0 A l * wAbs r 0 A i (k - l)) :=
        mul_nonneg (wAbs_nonneg r r A i k)
          (mul_nonneg (wTot_nonneg r 0 A l) (wAbs_nonneg r 0 A i (k - l)))
      have hmul := mul_le_mul_of_nonneg_right hpe hcoef
      refine le_of_le_of_eq (le_of_eq_of_le (by ring) hmul) ?_
      rw [show (4 : ℝ) ^ ((r - 1) / 2) *
            (periodicFrequencyWeight l ^ ((r - 1) / 2) +
              periodicFrequencyWeight (k - l) ^ ((r - 1) / 2)) *
            (wAbs r r A i k * (wTot r 0 A l * wAbs r 0 A i (k - l))) =
          (4 : ℝ) ^ ((r - 1) / 2) *
            (wAbs r r A i k * (periodicFrequencyWeight l ^ ((r - 1) / 2) * wTot r 0 A l) *
                wAbs r 0 A i (k - l) +
              wAbs r r A i k * wTot r 0 A l *
                (periodicFrequencyWeight (k - l) ^ ((r - 1) / 2) * wAbs r 0 A i (k - l))) by ring,
        hshiftTot l, hshiftAbs (k - l)]
    calc periodicFrequencyWeight k ^ ((r - 1) / 2) * wAbs r r A i k *
          ∑' l, wTot r 0 A l * wAbs r 0 A i (k - l)
        = ∑' l, periodicFrequencyWeight k ^ ((r - 1) / 2) * wAbs r r A i k *
            (wTot r 0 A l * wAbs r 0 A i (k - l)) := (tsum_mul_left).symm
      _ ≤ ∑' l, (4 : ℝ) ^ ((r - 1) / 2) *
            (wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l) +
              wAbs r r A i k * wTot r 0 A l * wAbs r (r - 1) A i (k - l)) := by
          refine Summable.tsum_le_tsum hptwise ?_ ((hF1.add hF2').mul_left _)
          exact ((conv_summable h2 A i k).mul_left
            (periodicFrequencyWeight k ^ ((r - 1) / 2) * wAbs r r A i k)).congr fun l ↦ by ring
      _ = (4 : ℝ) ^ ((r - 1) / 2) *
            ((∑' l, wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l)) +
              (∑' l, wAbs r r A i k * wTot r 0 A l * wAbs r (r - 1) A i (k - l))) := by
          rw [tsum_mul_left, hF1.tsum_add hF2']
      _ = (4 : ℝ) ^ ((r - 1) / 2) *
            ((∑' l, wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l)) +
              (∑' l, wAbs r r A i k * wAbs r (r - 1) A i l * wTot r 0 A (k - l))) := by
          congr 2
          have hg := (Equiv.subLeft k).tsum_eq
            (fun l ↦ wAbs r r A i k * wAbs r (r - 1) A i l * wTot r 0 A (k - l))
          refine Eq.trans (tsum_congr fun l ↦ ?_) hg
          show wAbs r r A i k * wTot r 0 A l * wAbs r (r - 1) A i (k - l) =
            wAbs r r A i k * wAbs r (r - 1) A i (k - l) * wTot r 0 A (k - (k - l))
          rw [sub_sub_cancel]
          ring
  -- assemble over the lattice
  have hlhs : Summable (fun k ↦ ‖(torusConvectionDatumReal hr A A).1 i k‖ *
      ‖(torusOrderDown r (r - 1) h1 A).1 i k‖) :=
    (lp.tsum_mul_le_mul_norm
      (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
        simpa using Real.HolderConjugate.two_two)
      ((torusConvectionDatumReal hr A A).1 i) ((torusOrderDown r (r - 1) h1 A).1 i)).1
  have hmajsum : Summable (fun k ↦ (4 : ℝ) ^ ((r - 1) / 2) *
      ((∑' l, wAbs r r A i k * wTot r (r - 1) A l * wAbs r 0 A i (k - l)) +
        (∑' l, wAbs r r A i k * wAbs r (r - 1) A i l * wTot r 0 A (k - l)))) :=
    (hp1.prod.add hp2.prod).mul_left _
  refine (Summable.tsum_le_tsum hmaj hlhs hmajsum).trans ?_
  rw [tsum_mul_left, hp1.prod.tsum_add hp2.prod, ← hp1.tsum_prod, ← hp2.tsum_prod]
  have hS : (0 : ℝ) ≤ Real.sqrt torusInverseWeightSum := Real.sqrt_nonneg _
  have hb1' : (∑' p : PeriodicFrequency × PeriodicFrequency,
      wAbs r r A i p.1 * wTot r (r - 1) A p.2 * wAbs r 0 A i (p.1 - p.2)) ≤
      ‖A‖ * (2 * ‖torusOrderDown r (r - 1) h1 A‖) *
        (Real.sqrt torusInverseWeightSum * ‖torusOrderDown r 2 h2 A‖) := by
    refine hb1.trans ?_
    exact mul_le_mul (mul_le_mul hXb hYb (Real.sqrt_nonneg _) (norm_nonneg _)) hβb
      (tsum_nonneg fun k ↦ wAbs_nonneg r 0 A i k)
      (mul_nonneg (norm_nonneg _) (by positivity))
  have hb2' : (∑' p : PeriodicFrequency × PeriodicFrequency,
      wAbs r r A i p.1 * wAbs r (r - 1) A i p.2 * wTot r 0 A (p.1 - p.2)) ≤
      ‖A‖ * ‖torusOrderDown r (r - 1) h1 A‖ *
        (3 * Real.sqrt torusInverseWeightSum * ‖torusOrderDown r 2 h2 A‖) := by
    refine hb2.trans ?_
    exact mul_le_mul (mul_le_mul hXb hZb (Real.sqrt_nonneg _) (norm_nonneg _)) hγb
      (tsum_nonneg fun k ↦ wTot_nonneg r 0 A k)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hfinal := add_le_add hb1' hb2'
  have hpow : (0 : ℝ) ≤ (4 : ℝ) ^ ((r - 1) / 2) := Real.rpow_nonneg (by norm_num) _
  refine (mul_le_mul_of_nonneg_left hfinal hpow).trans (le_of_eq ?_)
  ring

/-- **The explicit tame constant** at pairing order `s`:
`C(s) = 15 · 4^(s/2) · sqrt (∑ₖ (1+4π²|k|²)^{-2})`.  No optimality is claimed;
the three numerical factors are `3` components, `5 = 2 + 3` from the two halves
of the Peetre split, and `4^(s/2)` from Peetre itself. -/
def torusPairingConstant (s : ℝ) : ℝ :=
  15 * (4 : ℝ) ^ (s / 2) * Real.sqrt torusInverseWeightSum

theorem torusPairingConstant_pos (s : ℝ) : 0 < torusPairingConstant s := by
  have h1 : (0 : ℝ) < (4 : ℝ) ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) < Real.sqrt torusInverseWeightSum :=
    Real.sqrt_pos.mpr torusInverseWeightSum_pos
  have : (0 : ℝ) < 15 * (4 : ℝ) ^ (s / 2) := by positivity
  exact mul_pos this h2

/-- **The tame pairing bound.**  For every real datum `A` at order `r ≥ 3`, the
`H^{r-1}` pairing of the convection datum `Q(A,A)` against the order-`(r-1)`
datum of the same field obeys
`|⟪Q(A,A), A⟫_{H^s}| ≤ C(s) ‖A‖_{H²} ‖A‖_{H^s} ‖A‖_{H^{s+1}}`, `s = r - 1`.

This is `appendix-a-local-theory.tex:131-138`'s nonlinear term with the
manuscript's `C_m`, realized on the coefficient carrier.  No solenoidality and
no smoothness is used. -/
theorem torusPairingBound {r s : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r) (hs : s ≤ r)
    (hrs : s = r - 1) (A : PeriodicSobolev r) :
    |torusRealPairing (torusConvectionDatumReal hr A A) (torusOrderDown r s hs A)| ≤
      torusPairingConstant s * ‖torusOrderDown r 2 h2 A‖ *
        ‖torusOrderDown r s hs A‖ * ‖A‖ := by
  subst hrs
  refine (pairing_le_components _ _).trans ?_
  calc (∑ i : Fin 3, ∑' k, ‖(torusConvectionDatumReal hr A A).1 i k‖ *
        ‖(torusOrderDown r (r - 1) hs A).1 i k‖)
      ≤ ∑ _i : Fin 3, 5 * (4 : ℝ) ^ ((r - 1) / 2) * Real.sqrt torusInverseWeightSum *
          ‖torusOrderDown r 2 h2 A‖ * ‖torusOrderDown r (r - 1) hs A‖ * ‖A‖ :=
        Finset.sum_le_sum fun i _ ↦ component_bound hr h2 hs A i
    _ = torusPairingConstant (r - 1) * ‖torusOrderDown r 2 h2 A‖ *
          ‖torusOrderDown r (r - 1) hs A‖ * ‖A‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, torusPairingConstant]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

/-- The integer-order form: `m ≥ 3`, top datum at order `m+1`. -/
theorem torusPairingBound_nat (m : ℕ) (hm : 3 ≤ m) (A : PeriodicSobolev ((m : ℝ) + 1))
    (hr : (3 : ℝ) ≤ (m : ℝ) + 1) (h2 : (2 : ℝ) ≤ (m : ℝ) + 1) (hs : (m : ℝ) ≤ (m : ℝ) + 1) :
    |torusRealPairing (torusConvectionDatumReal hr A A)
        (torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs A)| ≤
      torusPairingConstant (m : ℝ) * ‖torusOrderDown ((m : ℝ) + 1) 2 h2 A‖ *
        ‖torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs A‖ * ‖A‖ := by
  have _ := hm
  exact torusPairingBound hr h2 hs (by ring) A

/-! ## 6. Bridges: consumer-supplied data and the physical norms -/

private lemma datum_ext {s : ℝ} {A B : PeriodicSobolev s}
    (h : ∀ i k, A.1 i k = B.1 i k) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  exact lp.ext (funext (h i))

/-- A reweight of `A` is the order-descended datum. -/
private lemma reweight_eq_down {r s : ℝ} (hs : s ≤ r) {A : PeriodicSobolev r}
    {B : PeriodicSobolev s} (hB : IsPeriodicReweight r s A B) :
    B = torusOrderDown r s hs A :=
  datum_ext fun i k ↦ by rw [hB i k, torusOrderDown_reweight r s hs A i k]

/-- **The pairing bound with consumer-supplied data.**  The `H^s` and `H²` data
are given by any reweights of `A`, which is how a consumer carrying the three
Sobolev realizations of one velocity slice meets the estimate. -/
theorem torusPairingBound_of_reweights {r s : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r)
    (hs : s ≤ r) (hrs : s = r - 1) (A : PeriodicSobolev r) (G : PeriodicSobolev s)
    (E : PeriodicSobolev 2) (hG : IsPeriodicReweight r s A G)
    (hE : IsPeriodicReweight r 2 A E) :
    |torusRealPairing (torusConvectionDatumReal hr A A) G| ≤
      torusPairingConstant s * ‖E‖ * ‖G‖ * ‖A‖ := by
  rw [reweight_eq_down hs hG, reweight_eq_down h2 hE]
  exact torusPairingBound hr h2 hs hrs A

/-- **The bound in the physical extended norms.**  If `A` is the order-`r` datum
of a periodic field `z`, the three factors are `‖z‖_{H²}`, `‖z‖_{H^s}`,
`‖z‖_{H^r}` as `periodicSobolevENorm` real values. -/
theorem torusPairingBound_enorm {r s : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r)
    (hs : s ≤ r) (hrs : s = r - 1) {z : NSFormalization.Section4.A02.SpatialField}
    {A : PeriodicSobolev r} (hA : IsPeriodicDatum r z A) :
    |torusRealPairing (torusConvectionDatumReal hr A A) (torusOrderDown r s hs A)| ≤
      torusPairingConstant s * (periodicSobolevENorm 2 z).toReal *
        (periodicSobolevENorm s z).toReal * (periodicSobolevENorm r z).toReal := by
  have hE : IsPeriodicDatum 2 z (torusOrderDown r 2 h2 A) :=
    persistence_datum_of_reweight hA (torusOrderDown_reweight r 2 h2 A)
  have hG : IsPeriodicDatum s z (torusOrderDown r s hs A) :=
    persistence_datum_of_reweight hA (torusOrderDown_reweight r s hs A)
  rw [periodicSobolevENorm_eq_datum hA, periodicSobolevENorm_eq_datum hE,
    periodicSobolevENorm_eq_datum hG, toReal_enorm, toReal_enorm, toReal_enorm]
  exact torusPairingBound hr h2 hs hrs A

/-- **The bound in lane 322's real profile.**  This is the spelling in which
`eq:Rhigh` states the nonlinear term: `torusSobolevNormAt` at the time `t`. -/
theorem torusPairingBound_profile {r s : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r)
    (hs : s ≤ r) (hrs : s = r - 1) {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev r} (hA : IsPeriodicDatum r (fun x ↦ u (t, x)) A) :
    |torusRealPairing (torusConvectionDatumReal hr A A) (torusOrderDown r s hs A)| ≤
      torusPairingConstant s * torusSobolevNormAt 2 u t *
        torusSobolevNormAt s u t * torusSobolevNormAt r u t :=
  torusPairingBound_enorm hr h2 hs hrs hA

/-! ## 7. The Leray-projected convection

The projector differs from the identity by a gradient, which drops against any
solenoidal partner datum, so the tame bound transfers verbatim to the projected
convection datum used by the mild formulation. -/

theorem torusRealPairing_comm {s : ℝ} (X Y : PeriodicSobolev s) :
    torusRealPairing X Y = torusRealPairing Y X := by
  unfold torusRealPairing
  have h := inner_re_symm (𝕜 := ℂ) X.1 Y.1
  have hr : ∀ z : ℂ, RCLike.re z = z.re := fun _ ↦ rfl
  rw [hr, hr] at h
  exact h

theorem torusRealPairing_sub {s : ℝ} (X Y Z : PeriodicSobolev s) :
    torusRealPairing (X - Y) Z = torusRealPairing X Z - torusRealPairing Y Z := by
  unfold torusRealPairing
  have h : ((X - Y).1 : PeriodicVectorData) = X.1 - Y.1 := rfl
  rw [h, inner_sub_left, Complex.sub_re]

/-- Coefficient-side solenoidality without the `2πi` factor. -/
private lemma solenoidal_freq {s : ℝ} {A : PeriodicSobolev s}
    (hA : IsSolenoidalPeriodicDatum A) (k : PeriodicFrequency) :
    ∑ j : Fin 3, (k j : ℂ) * A.1 j k = 0 := by
  have h := hA k
  have hfac : ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k
      = (2 * (Real.pi : ℂ) * Complex.I) * ∑ j : Fin 3, (k j : ℂ) * A.1 j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by unfold periodicDerivativeSymbol; ring
  rw [hfac] at h
  have hw : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact (mul_eq_zero.mp h).resolve_left hw

/-- A datum whose symbol is `kᵢ · q(k)` — a discrete gradient — pairs to zero
against a solenoidal datum.  Same computation as lane 322's `torusPressureDrop`,
without the `2πi` normalization of the derivative symbol. -/
private lemma projection_drop {s : ℝ} {A P : PeriodicSobolev s}
    (hA : IsSolenoidalPeriodicDatum A) (q : PeriodicFrequency → ℂ)
    (hP : ∀ (i : Fin 3) (k : PeriodicFrequency), P.1 i k = (k i : ℂ) * q k) :
    torusRealPairing A P = 0 := by
  have hfreq : ∀ k : PeriodicFrequency, ∑ j : Fin 3, (k j : ℂ) * conj (A.1 j k) = 0 := by
    intro k
    have h0 : conj (∑ j : Fin 3, (k j : ℂ) * A.1 j k) = 0 := by
      rw [solenoidal_freq hA k, map_zero]
    rw [map_sum] at h0
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) h0
    rw [map_mul, map_intCast]
  have hcomp : ∀ i : Fin 3,
      (inner ℂ (A.1 i) (P.1 i) : ℂ) = ∑' k, conj (A.1 i k) * P.1 i k := by
    intro i
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun k ↦ RCLike.inner_apply' _ _
  have hsum : ∀ i : Fin 3, Summable fun k ↦ conj (A.1 i k) * P.1 i k := by
    intro i
    exact (lp.summable_inner (𝕜 := ℂ) (A.1 i) (P.1 i)).congr fun k ↦ RCLike.inner_apply' _ _
  have hzero : (inner ℂ A.1 P.1 : ℂ) = 0 := by
    rw [PiLp.inner_apply]
    have hswap : ∑ i : Fin 3, (inner ℂ (A.1 i) (P.1 i) : ℂ) =
        ∑' k : PeriodicFrequency, ∑ i : Fin 3, conj (A.1 i k) * P.1 i k := by
      rw [Summable.tsum_finsetSum fun i _ ↦ hsum i]
      exact Finset.sum_congr rfl fun i _ ↦ hcomp i
    rw [hswap]
    have hk : ∀ k : PeriodicFrequency, ∑ i : Fin 3, conj (A.1 i k) * P.1 i k = 0 := by
      intro k
      have hq : ∑ i : Fin 3, conj (A.1 i k) * P.1 i k =
          q k * ∑ i : Fin 3, (k i : ℂ) * conj (A.1 i k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hP i k]; ring
      rw [hq, hfreq k, mul_zero]
    simp [hk]
  rw [torusRealPairing, hzero, Complex.zero_re]

/-- **The Leray projector does not change the pairing against a solenoidal
datum.** -/
theorem torusProjectedPairing_eq {r : ℝ} (hr : (3 : ℝ) ≤ r) (A B : PeriodicSobolev r)
    (G : PeriodicSobolev (r - 1)) (hG : IsSolenoidalPeriodicDatum G) :
    torusRealPairing (torusProjectedConvectionDatumReal hr A B) G =
      torusRealPairing (torusConvectionDatumReal hr A B) G := by
  set q : PeriodicFrequency → ℂ := fun k ↦
    -(∑ j : Fin 3, (k j : ℂ) * torusConvectionSymbolReal r A B j k) /
      (((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ)) : ℂ) with hq
  have hdiff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      (torusProjectedConvectionDatumReal hr A B - torusConvectionDatumReal hr A B).1 i k =
        (k i : ℂ) * q k := by
    intro i k
    have hco : (torusProjectedConvectionDatumReal hr A B -
        torusConvectionDatumReal hr A B).1 i k =
        (torusProjectedConvectionDatumReal hr A B).1 i k -
          (torusConvectionDatumReal hr A B).1 i k := rfl
    rw [hco, torusProjectedConvectionDatumReal_coeff, torusConvectionDatumReal_coeff,
      torusProjectedConvectionSymbolReal]
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left (by rfl)]
      simp
    · rw [ite_eq_right (by exact hk), hq]
      ring
  have hdrop : torusRealPairing G
      (torusProjectedConvectionDatumReal hr A B - torusConvectionDatumReal hr A B) = 0 :=
    projection_drop hG q hdiff
  rw [torusRealPairing_comm] at hdrop
  have hsub := torusRealPairing_sub (torusProjectedConvectionDatumReal hr A B)
    (torusConvectionDatumReal hr A B) G
  rw [hdrop] at hsub
  linarith

/-- **The tame pairing bound for the projected convection datum.** -/
theorem torusProjectedPairingBound {r s : ℝ} (hr : (3 : ℝ) ≤ r) (h2 : (2 : ℝ) ≤ r)
    (hs : s ≤ r) (hrs : s = r - 1) (A : PeriodicSobolev r)
    (hsol : IsSolenoidalPeriodicDatum (torusOrderDown r s hs A)) :
    |torusRealPairing (torusProjectedConvectionDatumReal hr A A)
        (torusOrderDown r s hs A)| ≤
      torusPairingConstant s * ‖torusOrderDown r 2 h2 A‖ *
        ‖torusOrderDown r s hs A‖ * ‖A‖ := by
  subst hrs
  rw [torusProjectedPairing_eq hr A A (torusOrderDown r (r - 1) hs A) hsol]
  exact torusPairingBound hr h2 hs rfl A

/-! ## 9. The advection form, in the spelling `eq:Rhigh` pairs against

Lane 335 (`Section3/T11/EnergyIdentity.lean`) reduces the `higherOrderBound`
field to exactly one hypothesis, `hpair`:

`|⟪Gm, Nm⟫_{H^m}| ≤ C_m ‖u(t)‖_{H²} ‖u(t)‖_{H^m} ‖∇u(t)‖_{H^m}`

with `Gm` the order-`m` datum of the velocity slice and `Nm` the order-`m` datum
of `convectionFieldT u = (u·∇)u`.  This section proves it.  Everything is read
off the raw coefficients `velocityCoeffT`, so §3's `wAbs`/`wTot` are reused at
`r := m` (where `wAbs m m Gm i k = ‖Gm.1 i k‖` and `wAbs m 0 Gm i k = |û ᵢ(k)|`),
and the gradient factor is the new `gAbs`. -/

/-- The gradient-weighted absolute coefficient: `|2πk| · |Â ᵢ(k)|`. -/
private def gAbs {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) : ℝ :=
  torusFreqAmp k * ‖A.1 i k‖

private def gTot {s : ℝ} (A : PeriodicSobolev s) (k : PeriodicFrequency) : ℝ :=
  ∑ j : Fin 3, gAbs A j k

private lemma gAbs_nonneg {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    0 ≤ gAbs A i k := mul_nonneg (torusFreqAmp_nonneg k) (norm_nonneg _)

private lemma gTot_nonneg {s : ℝ} (A : PeriodicSobolev s) (k : PeriodicFrequency) :
    0 ≤ gTot A k := Finset.sum_nonneg fun j _ ↦ gAbs_nonneg A j k

private lemma angular_nonneg (k : PeriodicFrequency) : 0 ≤ periodicAngularFrequencySq k := by
  unfold periodicAngularFrequencySq
  positivity

/-- The componentwise gradient energy of the order-`m` datum is `‖∇u(t)‖²_{H^m}`. -/
private lemma gAbs_gradEnergy {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} {Gm : PeriodicSobolev (m : ℝ)} {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1) :
    HasSum (fun k ↦ ∑ i : Fin 3, (gAbs Gm i k) ^ 2) (torusGradientEnergyT (m : ℝ) u t) := by
  have hentry : ∀ k : PeriodicFrequency, (∑ i : Fin 3, (gAbs Gm i k) ^ 2) =
      periodicFrequencyWeight k ^ (m : ℝ) * periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2 := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [gAbs, mul_pow, torusFreqAmp, Real.sq_sqrt (angular_nonneg k),
      datum_norm_sq_entry hGm i k]
    simp only [velocityCoeffT]
    ring
  exact (hasSum_gradEnergy hGm1).congr_fun hentry

private lemma gAbs_energy {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} {Gm : PeriodicSobolev (m : ℝ)} {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1) (i : Fin 3) :
    Summable (fun k ↦ (gAbs Gm i k) ^ 2) ∧
      Real.sqrt (∑' k, (gAbs Gm i k) ^ 2) ≤ torusGradientNormAt (m : ℝ) u t := by
  have htot := gAbs_gradEnergy hGm hGm1
  have hle : ∀ k, (gAbs Gm i k) ^ 2 ≤ ∑ j : Fin 3, (gAbs Gm j k) ^ 2 :=
    fun k ↦ Finset.single_le_sum (fun j _ ↦ sq_nonneg (gAbs Gm j k)) (Finset.mem_univ i)
  have hs : Summable (fun k ↦ (gAbs Gm i k) ^ 2) :=
    htot.summable.of_nonneg_of_le (fun k ↦ sq_nonneg _) hle
  refine ⟨hs, ?_⟩
  have hb : (∑' k, (gAbs Gm i k) ^ 2) ≤ torusGradientEnergyT (m : ℝ) u t := by
    rw [← htot.tsum_eq]
    exact hs.tsum_le_tsum hle htot.summable
  have hdef : torusGradientNormAt (m : ℝ) u t =
      Real.sqrt (torusGradientEnergyT (m : ℝ) u t) := rfl
  rw [hdef]
  exact Real.sqrt_le_sqrt hb

private lemma gTot_energy {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} {Gm : PeriodicSobolev (m : ℝ)} {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1) :
    Summable (fun k ↦ (gTot Gm k) ^ 2) ∧
      Real.sqrt (∑' k, (gTot Gm k) ^ 2) ≤ 2 * torusGradientNormAt (m : ℝ) u t := by
  have htot := gAbs_gradEnergy hGm hGm1
  have hle : ∀ k, (gTot Gm k) ^ 2 ≤ 3 * ∑ i : Fin 3, (gAbs Gm i k) ^ 2 := by
    intro k
    rw [gTot, Fin.sum_univ_three, Fin.sum_univ_three]
    nlinarith [sq_nonneg (gAbs Gm 0 k - gAbs Gm 1 k), sq_nonneg (gAbs Gm 0 k - gAbs Gm 2 k),
      sq_nonneg (gAbs Gm 1 k - gAbs Gm 2 k)]
  have hmaj : Summable (fun k ↦ 3 * ∑ i : Fin 3, (gAbs Gm i k) ^ 2) := htot.summable.mul_left 3
  have hs : Summable (fun k ↦ (gTot Gm k) ^ 2) :=
    hmaj.of_nonneg_of_le (fun k ↦ sq_nonneg _) hle
  refine ⟨hs, ?_⟩
  have hb : (∑' k, (gTot Gm k) ^ 2) ≤ 3 * torusGradientEnergyT (m : ℝ) u t := by
    refine (hs.tsum_le_tsum hle hmaj).trans (le_of_eq ?_)
    rw [tsum_mul_left, htot.tsum_eq]
  have hgn : torusGradientEnergyT (m : ℝ) u t = torusGradientNormAt (m : ℝ) u t ^ 2 :=
    (torusGradientNormAt_sq (m : ℝ) u t).symm
  rw [hgn] at hb
  have hsq : (∑' k, (gTot Gm k) ^ 2) ≤ (2 * torusGradientNormAt (m : ℝ) u t) ^ 2 := by
    nlinarith [torusGradientNormAt_nonneg (m : ℝ) u t]
  calc Real.sqrt (∑' k, (gTot Gm k) ^ 2)
      ≤ Real.sqrt ((2 * torusGradientNormAt (m : ℝ) u t) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * torusGradientNormAt (m : ℝ) u t := by
        refine Real.sqrt_sq ?_
        have := torusGradientNormAt_nonneg (m : ℝ) u t
        linarith

/-! ### 9.1 Relating the raw coefficients to the order-`m` datum -/

private lemma wAbs_zero_eq_coeff {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {s : ℝ} {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A)
    (i : Fin 3) (k : PeriodicFrequency) :
    wAbs s 0 A i k = ‖velocityCoeffT u i k t‖ := by
  have hentry : ‖A.1 i k‖ =
      periodicFrequencyWeight k ^ (s / 2) * ‖velocityCoeffT u i k t‖ := by
    rw [hA.2.2 i k, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (wpos k).le _)]
    rfl
  rw [wAbs_zero_eq, hentry, ← mul_assoc, ← Real.rpow_add (wpos k),
    show -s / 2 + s / 2 = (0 : ℝ) by ring, Real.rpow_zero, one_mul]

private lemma gAbs_of_shift {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3) (n : PeriodicFrequency) :
    periodicFrequencyWeight n ^ (s / 2) * torusFreqAmp n * wAbs s 0 A i n = gAbs A i n := by
  have h := wAbs_shift s 0 (s / 2) A i n
  rw [show (0 : ℝ) + 2 * (s / 2) = s by ring] at h
  calc periodicFrequencyWeight n ^ (s / 2) * torusFreqAmp n * wAbs s 0 A i n
      = torusFreqAmp n * (periodicFrequencyWeight n ^ (s / 2) * wAbs s 0 A i n) := by ring
    _ = torusFreqAmp n * wAbs s s A i n := by rw [h]
    _ = gAbs A i n := by rw [wAbs_self, gAbs]

private lemma gTot_of_shift {s : ℝ} (A : PeriodicSobolev s) (n : PeriodicFrequency) :
    periodicFrequencyWeight n ^ (s / 2) * torusFreqAmp n * wTot s 0 A n = gTot A n := by
  rw [wTot, gTot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ gAbs_of_shift A j n

/-- The unweighted coefficient of the gradient never exceeds the datum norm. -/
private lemma amp_wAbs_le {s : ℝ} (hs : (1 : ℝ) ≤ s) (A : PeriodicSobolev s) (i : Fin 3)
    (n : PeriodicFrequency) : torusFreqAmp n * wAbs s 0 A i n ≤ ‖A‖ := by
  have hamp : torusFreqAmp n ≤ periodicFrequencyWeight n ^ (s / 2) := by
    have h1 : torusFreqAmp n ≤ periodicFrequencyWeight n ^ ((1 : ℝ) / 2) := by
      rw [torusFreqAmp, ← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_sqrt
      rw [weight_eq_one_add_angular]
      linarith [angular_nonneg n]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le (one_le_w n) (by linarith))
  have hentry : periodicFrequencyWeight n ^ (s / 2) * wAbs s 0 A i n = ‖A.1 i n‖ := by
    have h := wAbs_shift s 0 (s / 2) A i n
    rw [show (0 : ℝ) + 2 * (s / 2) = s by ring, wAbs_self] at h
    exact h
  calc torusFreqAmp n * wAbs s 0 A i n
      ≤ periodicFrequencyWeight n ^ (s / 2) * wAbs s 0 A i n :=
        mul_le_mul_of_nonneg_right hamp (wAbs_nonneg s 0 A i n)
    _ = ‖A.1 i n‖ := hentry
    _ ≤ ‖A.1 i‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖A‖ := PiLp.norm_apply_le A.1 i

/-! ### 9.2 The convolution bound on the advection coefficient -/

private lemma advection_conv_summable {s : ℝ} (hs1 : (1 : ℝ) ≤ s) (h2 : (2 : ℝ) ≤ s)
    {A : PeriodicSobolev s}
    (i : Fin 3) (k : PeriodicFrequency) :
    Summable (fun l ↦ wTot s 0 A l * (torusFreqAmp (k - l) * wAbs s 0 A i (k - l))) := by
  obtain ⟨hs, _⟩ := wTot_l1 h2 A
  refine (hs.mul_right ‖A‖).of_nonneg_of_le
    (fun l ↦ mul_nonneg (wTot_nonneg s 0 A l)
      (mul_nonneg (torusFreqAmp_nonneg _) (wAbs_nonneg s 0 A i _))) ?_
  intro l
  exact mul_le_mul_of_nonneg_left (amp_wAbs_le hs1 A i (k - l)) (wTot_nonneg s 0 A l)

private lemma advection_coeff_norm_le {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} (hm : 3 ≤ m) {Gm : PeriodicSobolev (m : ℝ)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hconv : ∀ (i : Fin 3) (k : PeriodicFrequency),
      velocityCoeffT (convectionFieldT u) i k t =
        ∑ j : Fin 3, ∑' l : PeriodicFrequency,
          velocityCoeffT u j l t *
            (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t))
    (i : Fin 3) (k : PeriodicFrequency) :
    ‖velocityCoeffT (convectionFieldT u) i k t‖ ≤
      ∑' l, wTot (m : ℝ) 0 Gm l * (torusFreqAmp (k - l) * wAbs (m : ℝ) 0 Gm i (k - l)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (by norm_num) hm
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (by norm_num) hm
  have hterm : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖velocityCoeffT u j l t *
          (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t)‖ ≤
        wAbs (m : ℝ) 0 Gm j l * (torusFreqAmp (k - l) * wAbs (m : ℝ) 0 Gm i (k - l)) := by
    intro j l
    rw [norm_mul, norm_mul, wAbs_zero_eq_coeff hGm j l, wAbs_zero_eq_coeff hGm i (k - l)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right
      ((norm_periodicDerivativeSymbol j (k - l)) ▸ twoPi_abs_le_amp j (k - l)) (norm_nonneg _)
  have hjsum : ∀ j : Fin 3, Summable (fun l ↦
      wAbs (m : ℝ) 0 Gm j l * (torusFreqAmp (k - l) * wAbs (m : ℝ) 0 Gm i (k - l))) := by
    intro j
    obtain ⟨hs, _⟩ := wAbs_zero_l1 hm2 Gm j
    refine (hs.mul_right ‖Gm‖).of_nonneg_of_le
      (fun l ↦ mul_nonneg (wAbs_nonneg _ _ _ _ _)
        (mul_nonneg (torusFreqAmp_nonneg _) (wAbs_nonneg _ _ _ _ _))) ?_
    intro l
    exact mul_le_mul_of_nonneg_left (amp_wAbs_le hm1 Gm i (k - l)) (wAbs_nonneg _ _ _ _ _)
  have hjnorm : ∀ j : Fin 3, ‖∑' l : PeriodicFrequency, velocityCoeffT u j l t *
      (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t)‖ ≤
      ∑' l, wAbs (m : ℝ) 0 Gm j l * (torusFreqAmp (k - l) * wAbs (m : ℝ) 0 Gm i (k - l)) := by
    intro j
    have hns : Summable (fun l : PeriodicFrequency ↦ ‖velocityCoeffT u j l t *
        (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t)‖) :=
      (hjsum j).of_nonneg_of_le (fun l ↦ norm_nonneg _) (hterm j)
    exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum (hterm j) (hjsum j))
  rw [hconv i k]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ ↦ hjnorm j).trans (le_of_eq ?_)
  rw [← Summable.tsum_finsetSum fun j (_ : j ∈ Finset.univ) ↦ hjsum j]
  exact tsum_congr fun l ↦ by rw [wTot, Finset.sum_mul]

/-! ### 9.3 The componentwise estimate and the tame bound -/

private lemma advection_component_bound {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} (hm : 3 ≤ m) {Gm Nm : PeriodicSobolev (m : ℝ)}
    {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT u (t, x)) Nm)
    (hconv : ∀ (i : Fin 3) (k : PeriodicFrequency),
      velocityCoeffT (convectionFieldT u) i k t =
        ∑ j : Fin 3, ∑' l : PeriodicFrequency,
          velocityCoeffT u j l t *
            (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t))
    (i : Fin 3) :
    (∑' k, ‖Gm.1 i k‖ * ‖Nm.1 i k‖) ≤
      5 * (4 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt torusInverseWeightSum *
        torusSobolevNormAt 2 u t * torusSobolevNormAt (m : ℝ) u t *
        torusGradientNormAt (m : ℝ) u t := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (by norm_num) hm
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (by norm_num) hm
  have ha : (0 : ℝ) ≤ (m : ℝ) / 2 := by linarith
  -- the three factors in the vocabulary of `u`
  have hEdat : IsPeriodicDatum 2 (fun x ↦ u (t, x)) (torusOrderDown (m : ℝ) 2 hm2 Gm) :=
    persistence_datum_of_reweight hGm (torusOrderDown_reweight (m : ℝ) 2 hm2 Gm)
  have hEnorm : torusSobolevNormAt 2 u t = ‖torusOrderDown (m : ℝ) 2 hm2 Gm‖ :=
    torusSobolevNormAt_eq hEdat
  have hGnorm : torusSobolevNormAt (m : ℝ) u t = ‖Gm‖ := torusSobolevNormAt_eq hGm
  obtain ⟨hXs, hXb⟩ := wAbs_top_energy (m : ℝ) Gm i
  obtain ⟨hYs, hYb⟩ := gTot_energy hGm hGm1
  obtain ⟨hZs, hZb⟩ := gAbs_energy hGm hGm1 i
  obtain ⟨hβs, hβb⟩ := wAbs_zero_l1 hm2 Gm i
  obtain ⟨hγs, hγb⟩ := wTot_l1 hm2 Gm
  obtain ⟨hp1, hb1⟩ := torusTrilinearConvolution (X := fun k ↦ wAbs (m : ℝ) (m : ℝ) Gm i k)
    (Y := fun k ↦ gTot Gm k) (β := fun k ↦ wAbs (m : ℝ) 0 Gm i k)
    (wAbs_nonneg _ _ _ _) (gTot_nonneg Gm) (wAbs_nonneg _ _ _ _) hXs hYs hβs
  obtain ⟨hp2, hb2⟩ := torusTrilinearConvolution (X := fun k ↦ wAbs (m : ℝ) (m : ℝ) Gm i k)
    (Y := fun k ↦ gAbs Gm i k) (β := fun k ↦ wTot (m : ℝ) 0 Gm k)
    (wAbs_nonneg _ _ _ _) (gAbs_nonneg Gm i) (wTot_nonneg _ _ _) hXs hZs hγs
  have hmaj : ∀ k : PeriodicFrequency, ‖Gm.1 i k‖ * ‖Nm.1 i k‖ ≤
      (4 : ℝ) ^ ((m : ℝ) / 2) *
        ((∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) +
          (∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gAbs Gm i l * wTot (m : ℝ) 0 Gm (k - l))) := by
    intro k
    have hNentry : ‖Nm.1 i k‖ = periodicFrequencyWeight k ^ ((m : ℝ) / 2) *
        ‖velocityCoeffT (convectionFieldT u) i k t‖ := by
      rw [hNm.2.2 i k, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (wpos k).le _)]
      rfl
    have hGentry : ‖Gm.1 i k‖ = wAbs (m : ℝ) (m : ℝ) Gm i k := (wAbs_self (m : ℝ) Gm i k).symm
    have hconvsum := advection_conv_summable (A := Gm) hm1 hm2 i k
    have hstep : ‖Gm.1 i k‖ * ‖Nm.1 i k‖ ≤
        ∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k *
          (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * torusFreqAmp (k - l)) *
          (wTot (m : ℝ) 0 Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) := by
      rw [hGentry, hNentry]
      have hb := advection_coeff_norm_le hm hGm hconv i k
      have := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (wpos k).le ((m : ℝ) / 2)))
        (wAbs_nonneg (m : ℝ) (m : ℝ) Gm i k)
      refine this.trans (le_of_eq ?_)
      rw [← tsum_mul_left, ← tsum_mul_left]
      exact tsum_congr fun l ↦ by ring
    refine hstep.trans ?_
    have hF1 : Summable (fun l ↦
        wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) :=
      hp1.prod_factor k
    have hF2' : Summable (fun l ↦
        wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l * gAbs Gm i (k - l)) := by
      refine ((summable_sub_left (hp2.prod_factor k) k).congr ?_)
      intro l
      rw [sub_sub_cancel]
      ring
    have hptwise : ∀ l : PeriodicFrequency,
        wAbs (m : ℝ) (m : ℝ) Gm i k *
            (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * torusFreqAmp (k - l)) *
            (wTot (m : ℝ) 0 Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) ≤
          (4 : ℝ) ^ ((m : ℝ) / 2) *
            (wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l) +
              wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l * gAbs Gm i (k - l)) := by
      intro l
      have hpe := torusWeightPeetre_grad ha k l
      have hcoef : (0 : ℝ) ≤ wAbs (m : ℝ) (m : ℝ) Gm i k *
          (wTot (m : ℝ) 0 Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) :=
        mul_nonneg (wAbs_nonneg _ _ _ _ _)
          (mul_nonneg (wTot_nonneg _ _ _ _) (wAbs_nonneg _ _ _ _ _))
      have hmul := mul_le_mul_of_nonneg_right hpe hcoef
      refine le_of_le_of_eq (le_of_eq_of_le (by ring) hmul) ?_
      rw [show (4 : ℝ) ^ ((m : ℝ) / 2) *
            (periodicFrequencyWeight l ^ ((m : ℝ) / 2) * torusFreqAmp l +
              periodicFrequencyWeight (k - l) ^ ((m : ℝ) / 2) * torusFreqAmp (k - l)) *
            (wAbs (m : ℝ) (m : ℝ) Gm i k *
              (wTot (m : ℝ) 0 Gm l * wAbs (m : ℝ) 0 Gm i (k - l))) =
          (4 : ℝ) ^ ((m : ℝ) / 2) *
            (wAbs (m : ℝ) (m : ℝ) Gm i k *
                (periodicFrequencyWeight l ^ ((m : ℝ) / 2) * torusFreqAmp l *
                  wTot (m : ℝ) 0 Gm l) * wAbs (m : ℝ) 0 Gm i (k - l) +
              wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l *
                (periodicFrequencyWeight (k - l) ^ ((m : ℝ) / 2) * torusFreqAmp (k - l) *
                  wAbs (m : ℝ) 0 Gm i (k - l))) by ring,
        gTot_of_shift Gm l, gAbs_of_shift Gm i (k - l)]
    calc (∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k *
            (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * torusFreqAmp (k - l)) *
            (wTot (m : ℝ) 0 Gm l * wAbs (m : ℝ) 0 Gm i (k - l)))
        ≤ ∑' l, (4 : ℝ) ^ ((m : ℝ) / 2) *
            (wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l) +
              wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l * gAbs Gm i (k - l)) := by
          refine Summable.tsum_le_tsum hptwise ?_ ((hF1.add hF2').mul_left _)
          exact ((hconvsum.mul_left (wAbs (m : ℝ) (m : ℝ) Gm i k *
            (periodicFrequencyWeight k ^ ((m : ℝ) / 2)))).congr fun l ↦ by ring)
      _ = (4 : ℝ) ^ ((m : ℝ) / 2) *
            ((∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) +
              (∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l *
                gAbs Gm i (k - l))) := by
          rw [tsum_mul_left, hF1.tsum_add hF2']
      _ = (4 : ℝ) ^ ((m : ℝ) / 2) *
            ((∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) +
              (∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gAbs Gm i l *
                wTot (m : ℝ) 0 Gm (k - l))) := by
          congr 2
          have hg := (Equiv.subLeft k).tsum_eq
            (fun l ↦ wAbs (m : ℝ) (m : ℝ) Gm i k * gAbs Gm i l * wTot (m : ℝ) 0 Gm (k - l))
          refine Eq.trans (tsum_congr fun l ↦ ?_) hg
          show wAbs (m : ℝ) (m : ℝ) Gm i k * wTot (m : ℝ) 0 Gm l * gAbs Gm i (k - l) =
            wAbs (m : ℝ) (m : ℝ) Gm i k * gAbs Gm i (k - l) * wTot (m : ℝ) 0 Gm (k - (k - l))
          rw [sub_sub_cancel]
          ring
  have hlhs : Summable (fun k ↦ ‖Gm.1 i k‖ * ‖Nm.1 i k‖) :=
    (lp.tsum_mul_le_mul_norm
      (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
        simpa using Real.HolderConjugate.two_two) (Gm.1 i) (Nm.1 i)).1
  have hmajsum : Summable (fun k ↦ (4 : ℝ) ^ ((m : ℝ) / 2) *
      ((∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gTot Gm l * wAbs (m : ℝ) 0 Gm i (k - l)) +
        (∑' l, wAbs (m : ℝ) (m : ℝ) Gm i k * gAbs Gm i l * wTot (m : ℝ) 0 Gm (k - l)))) :=
    (hp1.prod.add hp2.prod).mul_left _
  refine (Summable.tsum_le_tsum hmaj hlhs hmajsum).trans ?_
  rw [tsum_mul_left, hp1.prod.tsum_add hp2.prod, ← hp1.tsum_prod, ← hp2.tsum_prod]
  have hb1' : (∑' p : PeriodicFrequency × PeriodicFrequency,
      wAbs (m : ℝ) (m : ℝ) Gm i p.1 * gTot Gm p.2 * wAbs (m : ℝ) 0 Gm i (p.1 - p.2)) ≤
      ‖Gm‖ * (2 * torusGradientNormAt (m : ℝ) u t) *
        (Real.sqrt torusInverseWeightSum * ‖torusOrderDown (m : ℝ) 2 hm2 Gm‖) := by
    refine hb1.trans ?_
    exact mul_le_mul (mul_le_mul hXb hYb (Real.sqrt_nonneg _) (norm_nonneg _)) hβb
      (tsum_nonneg fun k ↦ wAbs_nonneg _ _ _ _ _)
      (mul_nonneg (norm_nonneg _)
        (by linarith [torusGradientNormAt_nonneg (m : ℝ) u t]))
  have hb2' : (∑' p : PeriodicFrequency × PeriodicFrequency,
      wAbs (m : ℝ) (m : ℝ) Gm i p.1 * gAbs Gm i p.2 * wTot (m : ℝ) 0 Gm (p.1 - p.2)) ≤
      ‖Gm‖ * torusGradientNormAt (m : ℝ) u t *
        (3 * Real.sqrt torusInverseWeightSum * ‖torusOrderDown (m : ℝ) 2 hm2 Gm‖) := by
    refine hb2.trans ?_
    exact mul_le_mul (mul_le_mul hXb hZb (Real.sqrt_nonneg _) (norm_nonneg _)) hγb
      (tsum_nonneg fun k ↦ wTot_nonneg _ _ _ _)
      (mul_nonneg (norm_nonneg _) (torusGradientNormAt_nonneg _ _ _))
  have hpow : (0 : ℝ) ≤ (4 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  refine (mul_le_mul_of_nonneg_left (add_le_add hb1' hb2') hpow).trans (le_of_eq ?_)
  rw [hEnorm, hGnorm]
  ring

/-- **The tame pairing bound in the spelling `eq:Rhigh` uses** (lane 335's
`hpair`).  `Gm` is the order-`m` datum of the velocity slice, `Nm` the order-`m`
datum of the physical advection `(u·∇)u`, and the three factors are `‖u‖_{H²}`,
`‖u‖_{H^m}` and the dissipation norm `‖∇u‖_{H^m}`.  `Gm1` is the order-`(m+1)`
datum of the same slice, which is what makes `‖∇u(t)‖_{H^m}` finite; a classical
periodic solution carries one at every integer order. -/
theorem torusPairingBound_advection {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} (hm : 3 ≤ m) {Gm Nm : PeriodicSobolev (m : ℝ)}
    {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT u (t, x)) Nm)
    (hconv : ∀ (i : Fin 3) (k : PeriodicFrequency),
      velocityCoeffT (convectionFieldT u) i k t =
        ∑ j : Fin 3, ∑' l : PeriodicFrequency,
          velocityCoeffT u j l t *
            (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t)) :
    |torusRealPairing Gm Nm| ≤
      torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 u t *
        torusSobolevNormAt (m : ℝ) u t * torusGradientNormAt (m : ℝ) u t := by
  refine (pairing_le_components Gm Nm).trans ?_
  calc (∑ i : Fin 3, ∑' k, ‖Gm.1 i k‖ * ‖Nm.1 i k‖)
      ≤ ∑ _i : Fin 3, 5 * (4 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt torusInverseWeightSum *
          torusSobolevNormAt 2 u t * torusSobolevNormAt (m : ℝ) u t *
          torusGradientNormAt (m : ℝ) u t :=
        Finset.sum_le_sum fun i _ ↦ advection_component_bound hm hGm hGm1 hNm hconv i
    _ = torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 u t *
          torusSobolevNormAt (m : ℝ) u t * torusGradientNormAt (m : ℝ) u t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, torusPairingConstant]
        simp only [nsmul_eq_mul, Nat.cast_ofNat]
        ring

/-! ### 9.4 The advection coefficient is the convolution with the derivative symbol

`(u·∇)uᵢ = ∑ⱼ uⱼ ∂ⱼuᵢ`, so its Fourier coefficient is the convolution of `û ⱼ`
with `2πi nⱼ û ᵢ(n)` — the periodic convolution theorem of `MildPressure.lean`
together with the derivative rule of `Section3/T10/FourierCalculus.lean`.  This
is what removes the last hypothesis from §9.3. -/

/-- The `i`-th component of the advection `(u·∇)u` as a sum of scalar products. -/
theorem advection_component (hs : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)))
    (x : Space) (i : Fin 3) :
    convectionFieldT u (t, x) i =
      ∑ j : Fin 3, u (t, x) j * spatialPartial j (fun y : Space ↦ u (t, y) i) x := by
  have hexp : u (t, x) = ∑ j : Fin 3, (u (t, x) j) • coordinateVector j := by
    ext n
    rw [euclidean_sum_apply]
    simp [coordinateVector, PiLp.single_apply]
  have hval : (fderiv ℝ (fun y : Space ↦ u (t, y)) x (u (t, x))) i =
      ∑ j : Fin 3, (u (t, x) j) *
        ((fderiv ℝ (fun y : Space ↦ u (t, y)) x (coordinateVector j)) i) := by
    conv_lhs => rw [hexp]
    rw [map_sum, euclidean_sum_apply]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]; rfl
  have hpart : ∀ j : Fin 3, spatialPartial j (fun y : Space ↦ u (t, y) i) x =
      (fderiv ℝ (fun y : Space ↦ u (t, y)) x (coordinateVector j)) i := by
    intro j
    have h : HasFDerivAt (fun y : Space ↦ u (t, y) i)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (fun y : Space ↦ u (t, y)) x)) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
        ((hs.differentiable (by simp) x).hasFDerivAt)
    unfold spatialPartial
    rw [h.fderiv]
    rfl
  show (fderiv ℝ (fun y : Space ↦ u (t, y)) x (u (t, x))) i = _
  rw [hval]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hpart j]


/-- **The advection coefficient is the convolution with the derivative symbol.** -/
theorem velocityCoeffT_advection (hs : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)))
    (hp : IsPeriodicSpatial (fun x : Space ↦ u (t, x))) (i : Fin 3) (k : PeriodicFrequency) :
    velocityCoeffT (convectionFieldT u) i k t =
      ∑ j : Fin 3, ∑' l : PeriodicFrequency,
        velocityCoeffT u j l t *
          (periodicDerivativeSymbol j (k - l) * velocityCoeffT u i (k - l) t) := by
  have hFs : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x : Space ↦ ((u (t, x) j : ℝ) : ℂ)) :=
    fun j ↦ sourceComponent_contDiff hs j
  have hFp : ∀ j : Fin 3, IsPeriodicSpatial (fun x : Space ↦ ((u (t, x) j : ℝ) : ℂ)) :=
    fun j ↦ sourceComponent_periodic hp j
  have hDs : ∀ j : Fin 3,
      ContDiff ℝ ∞ (spatialPartial j (fun x : Space ↦ ((u (t, x) i : ℝ) : ℂ))) := by
    intro j
    have h : ContDiff ℝ ∞ (fun x : Space ↦
        fderiv ℝ (fun y : Space ↦ ((u (t, y) i : ℝ) : ℂ)) x) := (hFs i).fderiv_right (by simp)
    exact h.clm_apply contDiff_const
  have hDp : ∀ j : Fin 3,
      IsPeriodicSpatial (spatialPartial j (fun x : Space ↦ ((u (t, x) i : ℝ) : ℂ))) :=
    fun j ↦ NavierStokes.PeriodicUniqueness.spatial_partial_periodic
      (show NavierStokes.PeriodicIntegration.UnitPeriods
        (fun x : Space ↦ ((u (t, x) i : ℝ) : ℂ)) from hFp i) j
  have hcx : ∀ (j : Fin 3) (x : Space),
      spatialPartial j (fun y : Space ↦ ((u (t, y) i : ℝ) : ℂ)) x =
        ((spatialPartial j (fun y : Space ↦ u (t, y) i) x : ℝ) : ℂ) := by
    intro j x
    have hci : ContDiff ℝ 1 (fun y : Space ↦ u (t, y) i) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs).of_le (by simp)
    exact congrFun (spatialPartial_complexify hci j) x
  have hdecomp : (fun x : Space ↦ ((convectionFieldT u (t, x) i : ℝ) : ℂ)) =
      fun x : Space ↦ ∑ j : Fin 3, ((u (t, x) j : ℝ) : ℂ) *
        spatialPartial j (fun y : Space ↦ ((u (t, y) i : ℝ) : ℂ)) x := by
    funext x
    rw [advection_component hs x i, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Complex.ofReal_mul, hcx j x]
  show periodicFourierCoeff (fun x : Space ↦ ((convectionFieldT u (t, x) i : ℝ) : ℂ)) k = _
  rw [hdecomp, periodicFourierCoeff_finsetSum Finset.univ
    (fun (j : Fin 3) (x : Space) ↦ ((u (t, x) j : ℝ) : ℂ) *
      spatialPartial j (fun y : Space ↦ ((u (t, y) i : ℝ) : ℂ)) x)
    (fun j _ ↦ (hFs j).continuous.mul (hDs j).continuous) k]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [periodicFourierCoeff_mul (hFp j) (hFs j) (hDp j) (hDs j) k]
  refine tsum_congr fun l ↦ ?_
  congr 1
  show periodicFourierCoeff
    (fun x : Space ↦ fderiv ℝ (fun y : Space ↦ ((u (t, y) i : ℝ) : ℂ)) x (coordinateVector j))
      (k - l) = _
  exact periodicFourierCoeff_fderiv (hFp i) ((hFs i).of_le (by simp)) j (k - l)


/-- **The tame pairing bound for a smooth periodic velocity slice**, with no
hypothesis on the convection coefficients: `hconv` is discharged by the
convolution theorem. -/
theorem torusPairingBound_slice {u : NSFormalization.Section4.A02.SpaceTimeField} {t : ℝ}
    {m : ℕ} (hm : 3 ≤ m) {Gm Nm : PeriodicSobolev (m : ℝ)}
    {Gm1 : PeriodicSobolev ((m : ℝ) + 1)}
    (hsm : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)))
    (hpr : IsPeriodicSpatial (fun x : Space ↦ u (t, x)))
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) Gm)
    (hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) Gm1)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT u (t, x)) Nm) :
    |torusRealPairing Gm Nm| ≤
      torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 u t *
        torusSobolevNormAt (m : ℝ) u t * torusGradientNormAt (m : ℝ) u t :=
  torusPairingBound_advection hm hGm hGm1 hNm (velocityCoeffT_advection hsm hpr)

/-! ## 10. `hpair` of lane 335, and `higherOrderBound` unconditionally -/

/-- **The `hpair` hypothesis of `EnergyIdentity.higherOrderBound_of_pairingBound`,
proved.**  The constant family is `C_m = torusPairingConstant m`. -/
theorem torusPairingBound_classical :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : NSFormalization.Section4.A02.SpatialField), a ∈ initialClassT →
      ∀ (f : NSFormalization.Section4.A02.SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
            IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
            IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
            |torusRealPairing Gm Nm| ≤
              torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 w.velocity t *
                torusSobolevNormAt (m : ℝ) w.velocity t *
                torusGradientNormAt (m : ℝ) w.velocity t := by
  intro ν _ a _ f _ T w m hm t ht Gm Nm hGm hNm
  have htI : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  obtain ⟨G1, _, hG1d⟩ := w.sobolev (m + 1)
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
  have hGm1 : IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ w.velocity (t, x)) (G1 t) := by
    have h := hG1d t htI
    rwa [hcast] at h
  exact torusPairingBound_slice hm (classical_velocity_slice_contDiff w htI)
    (w.velocity_periodic t htI) hGm hGm1 hNm

/-- **`higherOrderBound` of `PeriodicContinuationAPI`, unconditionally.**
Lane 322 reduced the field to `eq:Rhigh`, lane 335 reduced `eq:Rhigh` to the tame
pairing bound, and this lane proves the pairing bound; nothing is assumed. -/
theorem torusHigherOrderBound :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : NSFormalization.Section4.A02.SpatialField), a ∈ initialClassT →
        ∀ (f : NSFormalization.Section4.A02.SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : NSFormalization.Section4.A02.SpaceTimeField)
              (p : NSFormalization.Section4.A02.SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Set.Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M :=
  higherOrderBound_of_pairingBound (fun m ↦ torusPairingConstant (m : ℝ))
    torusPairingBound_classical

end NSFormalization.Section3.T11
