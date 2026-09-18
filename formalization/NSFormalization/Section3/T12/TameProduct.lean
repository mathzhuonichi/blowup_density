import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T10.Parseval
import NSFormalization.Section3.T11.PairingBound
import NSFormalization.Section3.T11.MildPressure

/-!
# T12 — the scalar tame product on the unit three-torus (`eq:Rproduct`)

`paper/sections/appendix-a-local-theory.tex:8-11`, torus half of `lem:calculus`:
for every integer `m ≥ 2` and scalars `a, b ∈ H^m(T³)`,

`‖ab‖_{H^m} ≤ C(m) (‖a‖_{H²}‖b‖_{H^m} + ‖b‖_{H²}‖a‖_{H^m})`.

This module proves the `tameProduct` field of
`research/T12/probes/api_on_canonical.lean` verbatim, with the explicit
constant family `tameProductConst m = 4^{m/2} (∑ₖ W(k)^{-2})^{1/2}`.

## Route

All work is on the Fourier side of the T10/T12 data layer.  Write
`W(k) = periodicFrequencyWeight k = 1 + 4π²|k|²` and `â(k)` for the scalar
coefficient of a real periodic `a`.

1. **Order descent and the `ℓ¹` bound** (§3).  A scalar datum is unique, so
   `periodicScalarSobolevENorm s z` is *the* norm of the unique order-`s`
   datum whenever one exists, and `MemPeriodicHmScalar m a` produces it.
   Descending from order `m ≥ 2` to order `2` is a contraction, and
   `∑ₖ â(k) ≤ (∑ₖ W(k)^{-2})^{1/2} ‖a‖_{H²}` by Cauchy--Schwarz against
   lane 336's `torusInverseWeight_summable`.  This is the step that makes the
   estimate *tame*: the low factor is `H²`, not `H³`.
2. **The convolution theorem beyond smooth data** (§4-§5).  `MildPressure`'s
   `periodicFourierCoeff_mul` assumes both factors are `C^∞`.  For `m ≥ 2` the
   coefficients are absolutely summable by step 1, so the `L²` Fourier series
   of `a` converges in `L²` *and* uniformly; comparing the two limits in `L²`
   identifies `torusLift a` almost everywhere with its (continuous) Fourier
   series (`torusLift_ae_eq_series`).  That a.e. identity is exactly what the
   dominated-convergence argument of `periodicFourierCoeff_mul` needs, so the
   convolution identity survives with the smoothness of the *first* factor
   replaced by absolute summability and the smoothness of the *second* by
   integrability (`periodicFourierCoeff_mul_of_series`).  This answers the
   brief's question: the extension is proved through the `L²` representation,
   not by density.
3. **Peetre and Young** (§2, §6).  `W(k)^{m/2} ≤ 4^{m/2}(W(l)^{m/2} +
   W(k-l)^{m/2})` (`torusWeightPeetre`) splits the weight so that in each half
   exactly one factor carries the full `H^m` weight and the other is
   unweighted; the unweighted one is summed in `ℓ¹` by step 1, and
   `torusYoungConvolution` (`ℓ² ∗ ℓ¹ ⊆ ℓ²`, proved here by Cauchy--Schwarz
   against the convolution measure) closes the `ℓ²` sum.  Minkowski in `ℓ²`
   adds the two halves.
4. **The product's datum exists** (§6): the `ℓ²` bound of step 3 *is* the
   membership proof for the order-`m` coefficient sequence of `ab`, and the
   two remaining conjuncts (periodicity, Haar integrability of the lift) come
   from periodicity of the factors and Cauchy--Schwarz in `L²`.

§7 records a non-vacuity constructor: every conjugate-symmetric, absolutely
summable, `H^m`-weighted-square-summable coefficient family is realized by an
honest real periodic scalar with exactly those coefficients.

No `sorry`, no axiom, no named `Prop` input: every statement below is
unconditional.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-! ## 1. Weight arithmetic and real `ℓ²` helpers

`PairingBound.lean` proves the same elementary facts as `private` lemmas, so
they are reproved here rather than exported from there. -/

private lemma wpos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight; positivity

private lemma one_le_w (k : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have h : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

private lemma wrpow_pos (k : PeriodicFrequency) (a : ℝ) :
    0 < periodicFrequencyWeight k ^ a :=
  Real.rpow_pos_of_pos (wpos k) a

private lemma wrpow_mono (k : PeriodicFrequency) {a b : ℝ} (h : a ≤ b) :
    periodicFrequencyWeight k ^ a ≤ periodicFrequencyWeight k ^ b :=
  Real.rpow_le_rpow_of_exponent_le (one_le_w k) h

private lemma one_le_wrpow (k : PeriodicFrequency) {a : ℝ} (ha : 0 ≤ a) :
    1 ≤ periodicFrequencyWeight k ^ a := by
  have h := wrpow_mono k ha
  rwa [Real.rpow_zero] at h

private lemma wrpow_le_one (k : PeriodicFrequency) {a : ℝ} (ha : a ≤ 0) :
    periodicFrequencyWeight k ^ a ≤ 1 := by
  have h := wrpow_mono k ha
  rwa [Real.rpow_zero] at h

private lemma rpow_two_norm (x : ℝ) : ‖x‖ ^ (2 : ℝ≥0∞).toReal = x ^ 2 := by
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

private lemma cnorm_rpow_two (z : ℂ) : ‖z‖ ^ (2 : ℝ≥0∞).toReal = ‖z‖ ^ 2 := by
  simp only [ENNReal.toReal_ofNat]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

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

private lemma cplxLp_mem (f : PeriodicFrequency → ℂ) (hf : Summable (fun k ↦ ‖f k‖ ^ 2)) :
    Memℓp f 2 :=
  memℓp_gen (hf.congr fun k ↦ (cnorm_rpow_two (f k)).symm)

/-- Cauchy--Schwarz on the lattice, in the `√`-of-square-sum spelling. -/
private lemma lattice_cauchy_schwarz {f g : PeriodicFrequency → ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Summable (fun k ↦ f k ^ 2)) (hg : Summable (fun k ↦ g k ^ 2)) :
    Summable (fun k ↦ f k * g k) ∧
      (∑' k, f k * g k) ≤ Real.sqrt (∑' k, f k ^ 2) * Real.sqrt (∑' k, g k ^ 2) := by
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two) (realLp f hf) (realLp g hg)
  have hval : ∀ k, ‖(realLp f hf) k‖ * ‖(realLp g hg) k‖ = f k * g k := by
    intro k
    rw [realLp_apply, realLp_apply, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hf0 k), abs_of_nonneg (hg0 k)]
  refine ⟨hh.1.congr hval, ?_⟩
  have hb := hh.2
  rw [tsum_congr hval, lp_norm_eq_sqrt, lp_norm_eq_sqrt] at hb
  exact hb

/-- Minkowski for two nonnegative lattice sequences in `ℓ²`. -/
private lemma l2_add_bound {u v : PeriodicFrequency → ℝ}
    (hu : Summable fun k ↦ u k ^ 2) (hv : Summable fun k ↦ v k ^ 2) :
    Summable (fun k ↦ (u k + v k) ^ 2) ∧
      Real.sqrt (∑' k, (u k + v k) ^ 2) ≤
        Real.sqrt (∑' k, u k ^ 2) + Real.sqrt (∑' k, v k ^ 2) := by
  have hUV : ∀ k, (realLp u hu + realLp v hv) k = u k + v k := by
    intro k
    rw [lp.coeFn_add]
    rfl
  have hs : Summable (fun k ↦ (u k + v k) ^ 2) := by
    have h : Summable (fun k ↦ ‖(realLp u hu + realLp v hv) k‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp (realLp u hu + realLp v hv)).summable (by norm_num)
    refine h.congr fun k ↦ ?_
    rw [rpow_two_norm, hUV k]
  refine ⟨hs, ?_⟩
  have hnorm : ‖realLp u hu + realLp v hv‖ = Real.sqrt (∑' k, (u k + v k) ^ 2) := by
    rw [lp_norm_eq_sqrt]
    exact congrArg Real.sqrt (tsum_congr fun k ↦ by rw [hUV k])
  have htri := norm_add_le (realLp u hu) (realLp v hv)
  rw [hnorm, lp_norm_eq_sqrt, lp_norm_eq_sqrt] at htri
  exact htri

/-! ## 2. Young's inequality `ℓ² ∗ ℓ¹ ⊆ ℓ²` on the lattice -/

private lemma tsum_prod_mul {f g : PeriodicFrequency → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k) :
    (∑' q : PeriodicFrequency × PeriodicFrequency, f q.1 * g q.2) =
      (∑' k, f k) * (∑' k, g k) := by
  rw [(hf.mul_of_nonneg hg hf0 hg0).tsum_prod]
  simp only [tsum_mul_left, tsum_mul_right]

private lemma shiftSnd_inj : Function.Injective
    (fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.2, p.1 - p.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  have h3 : a.1 = b.1 := by
    have hz : a.1 - a.2 + a.2 = b.1 - b.2 + b.2 := by rw [h.2, h.1]
    simpa using hz
  exact Prod.ext h3 h.1

private def shiftEquivSnd : PeriodicFrequency × PeriodicFrequency ≃
    PeriodicFrequency × PeriodicFrequency where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

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
  exact ⟨hs, he1.trans (tsum_prod_mul hY hβ (fun k ↦ sq_nonneg (Y k)) hβ0)⟩

/-- Reindexing by `l ↦ k - l` is a bijection of the lattice. -/
theorem torusShift_summable_iff (γ : PeriodicFrequency → ℝ) (k : PeriodicFrequency) :
    Summable (fun l ↦ γ (k - l)) ↔ Summable γ :=
  (Equiv.subLeft k).summable_iff

theorem torusShift_tsum (γ : PeriodicFrequency → ℝ) (k : PeriodicFrequency) :
    (∑' l, γ (k - l)) = ∑' n, γ n :=
  (Equiv.subLeft k).tsum_eq γ

/-- Convolution on the lattice is commutative. -/
theorem torusConv_comm (γ B : PeriodicFrequency → ℝ) (k : PeriodicFrequency) :
    (∑' l, γ l * B (k - l)) = ∑' l, B l * γ (k - l) := by
  rw [← (Equiv.subLeft k).tsum_eq (fun l ↦ γ l * B (k - l))]
  exact tsum_congr fun l ↦ by
    show γ (k - l) * B (k - (k - l)) = B l * γ (k - l)
    rw [sub_sub_cancel]; ring

/-- Summability transports across the commutation of a lattice convolution. -/
theorem conv_comm_summable {gam B : PeriodicFrequency → ℝ} (k : PeriodicFrequency)
    (h : Summable fun l ↦ B l * gam (k - l)) : Summable fun l ↦ gam l * B (k - l) := by
  have h2 : Summable (fun l ↦ (fun n ↦ B n * gam (k - n)) (k - l)) :=
    (torusShift_summable_iff (fun n ↦ B n * gam (k - n)) k).mpr h
  refine h2.congr fun l ↦ ?_
  show B (k - l) * gam (k - (k - l)) = gam l * B (k - l)
  rw [sub_sub_cancel]
  ring

/-- **Young's inequality `ℓ² ∗ ℓ¹ ⊆ ℓ²` on `Z³`.**  For nonnegative `Y ∈ ℓ²`
and `γ ∈ ℓ¹`, the convolution `k ↦ ∑ₗ Y(l) γ(k-l)` is in `ℓ²` with
`‖Y ∗ γ‖_{ℓ²} ≤ ‖Y‖_{ℓ²} ‖γ‖_{ℓ¹}`. -/
theorem torusYoungConvolution {Y γ : PeriodicFrequency → ℝ}
    (hY0 : ∀ k, 0 ≤ Y k) (hγ0 : ∀ k, 0 ≤ γ k)
    (hY : Summable fun k ↦ Y k ^ 2) (hγ : Summable γ) :
    (∀ k, Summable fun l ↦ Y l * γ (k - l)) ∧
      Summable (fun k ↦ (∑' l, Y l * γ (k - l)) ^ 2) ∧
        Real.sqrt (∑' k, (∑' l, Y l * γ (k - l)) ^ 2) ≤
          Real.sqrt (∑' k, Y k ^ 2) * (∑' k, γ k) := by
  have hSnn : 0 ≤ ∑' k, γ k := tsum_nonneg hγ0
  have hγshift : ∀ k, Summable (fun l ↦ γ (k - l)) := fun k ↦
    (torusShift_summable_iff γ k).mpr hγ
  have hγle : ∀ n, γ n ≤ ∑' k, γ k := fun n ↦ hγ.le_tsum n fun b _ ↦ hγ0 b
  -- the weighted fibre sums
  have hYsq_shift : ∀ k, Summable (fun l ↦ Y l ^ 2 * γ (k - l)) := by
    intro k
    refine (hY.mul_right (∑' n, γ n)).of_nonneg_of_le
      (fun l ↦ mul_nonneg (sq_nonneg _) (hγ0 _)) fun l ↦ ?_
    exact mul_le_mul_of_nonneg_left (hγle _) (sq_nonneg _)
  -- the convolution itself is summable fibrewise
  have hYb : ∀ l, Y l ≤ Real.sqrt (∑' k, Y k ^ 2) := by
    intro l
    have h : Y l ^ 2 ≤ ∑' k, Y k ^ 2 := hY.le_tsum l fun b _ ↦ sq_nonneg _
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (hY0 l)] at this
  have hconv : ∀ k, Summable (fun l ↦ Y l * γ (k - l)) := by
    intro k
    refine ((hγshift k).mul_left (Real.sqrt (∑' n, Y n ^ 2))).of_nonneg_of_le
      (fun l ↦ mul_nonneg (hY0 l) (hγ0 _)) fun l ↦ ?_
    exact mul_le_mul_of_nonneg_right (hYb l) (hγ0 _)
  -- fibrewise Cauchy--Schwarz
  have hcs : ∀ k, (∑' l, Y l * γ (k - l)) ^ 2 ≤
      (∑' l, Y l ^ 2 * γ (k - l)) * (∑' n, γ n) := by
    intro k
    have hsq : ∀ l : PeriodicFrequency,
        Real.sqrt (γ (k - l)) * Real.sqrt (γ (k - l)) = γ (k - l) :=
      fun l ↦ Real.mul_self_sqrt (hγ0 _)
    have hf : Summable (fun l ↦ (Y l * Real.sqrt (γ (k - l))) ^ 2) := by
      refine (hYsq_shift k).congr fun l ↦ ?_
      rw [mul_pow, sq (Real.sqrt (γ (k - l))), hsq l]
    have hg : Summable (fun l ↦ (Real.sqrt (γ (k - l))) ^ 2) := by
      refine (hγshift k).congr fun l ↦ ?_
      rw [sq, hsq l]
    obtain ⟨-, hb⟩ := lattice_cauchy_schwarz
      (f := fun l ↦ Y l * Real.sqrt (γ (k - l))) (g := fun l ↦ Real.sqrt (γ (k - l)))
      (fun l ↦ mul_nonneg (hY0 l) (Real.sqrt_nonneg _)) (fun l ↦ Real.sqrt_nonneg _) hf hg
    have hval : (∑' l, Y l * Real.sqrt (γ (k - l)) * Real.sqrt (γ (k - l))) =
        ∑' l, Y l * γ (k - l) :=
      tsum_congr fun l ↦ by rw [mul_assoc, hsq l]
    have h1 : (∑' l, (Y l * Real.sqrt (γ (k - l))) ^ 2) = ∑' l, Y l ^ 2 * γ (k - l) :=
      tsum_congr fun l ↦ by rw [mul_pow, sq (Real.sqrt (γ (k - l))), hsq l]
    have h2 : (∑' l, (Real.sqrt (γ (k - l))) ^ 2) = ∑' n, γ n := by
      rw [tsum_congr (fun l ↦ by rw [sq, hsq l] : ∀ l, (Real.sqrt (γ (k - l))) ^ 2 = γ (k - l))]
      exact torusShift_tsum γ k
    rw [hval, h1, h2] at hb
    have hnn : 0 ≤ ∑' l, Y l * γ (k - l) :=
      tsum_nonneg fun l ↦ mul_nonneg (hY0 l) (hγ0 _)
    have hsq2 : (∑' l, Y l * γ (k - l)) ^ 2 ≤
        (Real.sqrt (∑' l, Y l ^ 2 * γ (k - l)) * Real.sqrt (∑' n, γ n)) ^ 2 := by
      have hr : 0 ≤ Real.sqrt (∑' l, Y l ^ 2 * γ (k - l)) * Real.sqrt (∑' n, γ n) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      nlinarith
    refine hsq2.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun l ↦ mul_nonneg (sq_nonneg _) (hγ0 _)),
      Real.sq_sqrt hSnn]
  -- fibrewise sum of the majorant
  obtain ⟨hprod, hprodval⟩ := sq_shift_sum' (Y := Y) hγ0 hY hγ
  have hfib : HasSum (fun k ↦ ∑' l, Y l ^ 2 * γ (k - l))
      ((∑' k, Y k ^ 2) * (∑' k, γ k)) := by
    have h := hprod.hasSum.prod_fiberwise (g := fun k ↦ ∑' l, Y l ^ 2 * γ (k - l))
      (fun b ↦ (hYsq_shift b).hasSum)
    rwa [hprodval] at h
  have hmaj : Summable (fun k ↦ (∑' l, Y l ^ 2 * γ (k - l)) * (∑' n, γ n)) :=
    hfib.summable.mul_right _
  have hfinal : Summable (fun k ↦ (∑' l, Y l * γ (k - l)) ^ 2) :=
    hmaj.of_nonneg_of_le (fun k ↦ sq_nonneg _) hcs
  refine ⟨hconv, hfinal, ?_⟩
  have hbound : (∑' k, (∑' l, Y l * γ (k - l)) ^ 2) ≤
      (∑' k, Y k ^ 2) * (∑' k, γ k) ^ 2 := by
    refine (hfinal.tsum_le_tsum hcs hmaj).trans (le_of_eq ?_)
    rw [tsum_mul_right, hfib.tsum_eq]
    ring
  calc Real.sqrt (∑' k, (∑' l, Y l * γ (k - l)) ^ 2)
      ≤ Real.sqrt ((∑' k, Y k ^ 2) * (∑' k, γ k) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (∑' k, Y k ^ 2) * (∑' k, γ k) := by
        rw [Real.sqrt_mul (tsum_nonneg fun k ↦ sq_nonneg _), Real.sqrt_sq hSnn]

/-! ## 3. The scalar data layer: uniqueness, order descent, and the `ℓ¹` bound -/

/-- The absolute raw Fourier coefficient of a real periodic scalar. -/
def scalarAbsCoeff (a : Space → ℝ) (k : PeriodicFrequency) : ℝ :=
  ‖periodicFourierCoeff (fun x ↦ ((a x : ℝ) : ℂ)) k‖

theorem scalarAbsCoeff_nonneg (a : Space → ℝ) (k : PeriodicFrequency) :
    0 ≤ scalarAbsCoeff a k := norm_nonneg _

/-- Two order-`s` scalar data of the same field coincide. -/
theorem scalarDatum_unique {s : ℝ} {z : Space → ℝ} {A B : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum s z A) (hB : IsPeriodicScalarDatum s z B) : A = B := by
  ext k
  rw [hA.2.2 k, hB.2.2 k]

/-- The totalized scalar norm is the norm of the (unique) representing datum. -/
theorem periodicScalarSobolevENorm_eq {s : ℝ} {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum s z A) : periodicScalarSobolevENorm s z = ‖A‖ₑ := by
  refine le_antisymm (iInf_le_of_le ⟨A, hA⟩ le_rfl) (le_iInf ?_)
  rintro ⟨B, hB⟩
  exact le_of_eq (congrArg (fun C : PeriodicScalarData ↦ ‖C‖ₑ) (scalarDatum_unique hA hB))

/-- A finite totalized scalar norm produces a representing datum. -/
theorem exists_scalarDatum {s : ℝ} {z : Space → ℝ}
    (h : periodicScalarSobolevENorm s z ≠ ⊤) :
    ∃ A : PeriodicScalarData, IsPeriodicScalarDatum s z A := by
  by_contra hc
  push Not at hc
  refine h ?_
  have hempty : IsEmpty {A : PeriodicScalarData // IsPeriodicScalarDatum s z A} :=
    ⟨fun A ↦ hc A.1 A.2⟩
  rw [periodicScalarSobolevENorm, iInf_of_isEmpty, sInf_empty]

/-- The absolute coefficients read off an order-`s` datum. -/
theorem scalarDatum_norm_apply {s : ℝ} {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum s z A) (k : PeriodicFrequency) :
    ‖A k‖ = periodicFrequencyWeight k ^ (s / 2) * scalarAbsCoeff z k := by
  rw [hA.2.2 k, norm_smul, Real.norm_eq_abs, abs_of_pos (wrpow_pos k _)]
  rfl

/-- The order-`s` energy of a scalar datum, on the coefficient side. -/
theorem scalarDatum_energy {s : ℝ} {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum s z A) :
    Summable (fun k ↦ (periodicFrequencyWeight k ^ (s / 2) * scalarAbsCoeff z k) ^ 2) ∧
      (∑' k, (periodicFrequencyWeight k ^ (s / 2) * scalarAbsCoeff z k) ^ 2) = ‖A‖ ^ 2 := by
  have hfun : ∀ k, (periodicFrequencyWeight k ^ (s / 2) * scalarAbsCoeff z k) ^ 2 =
      ‖A k‖ ^ (2 : ℝ≥0∞).toReal := by
    intro k
    rw [cnorm_rpow_two, scalarDatum_norm_apply hA k]
  have hs : Summable (fun k ↦ ‖A k‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp A).summable (by norm_num)
  refine ⟨hs.congr fun k ↦ (hfun k).symm, ?_⟩
  rw [tsum_congr hfun, ← lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) A]
  simp only [ENNReal.toReal_ofNat]
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **Order descent.**  A datum at order `r` gives the datum at every `s ≤ r`. -/
def scalarOrderDown (r s : ℝ) (h : s ≤ r) (A : PeriodicScalarData) : PeriodicScalarData :=
  ⟨fun k ↦ (periodicFrequencyWeight k ^ ((s - r) / 2) : ℝ) • A k, by
    refine cplxLp_mem _ (((lp.memℓp A).summable (by norm_num)).of_nonneg_of_le
      (fun k ↦ by positivity) fun k ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (wrpow_pos k _), mul_pow, cnorm_rpow_two]
    have h1 : periodicFrequencyWeight k ^ ((s - r) / 2) ≤ 1 :=
      wrpow_le_one k (by linarith)
    have h2 : (0 : ℝ) ≤ periodicFrequencyWeight k ^ ((s - r) / 2) := (wrpow_pos k _).le
    have ht2 : (periodicFrequencyWeight k ^ ((s - r) / 2)) ^ 2 ≤ 1 := by nlinarith
    calc (periodicFrequencyWeight k ^ ((s - r) / 2)) ^ 2 * ‖A k‖ ^ 2
        ≤ 1 * ‖A k‖ ^ 2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      _ = ‖A k‖ ^ 2 := one_mul _⟩

theorem scalarOrderDown_apply (r s : ℝ) (h : s ≤ r) (A : PeriodicScalarData)
    (k : PeriodicFrequency) :
    (scalarOrderDown r s h A) k = (periodicFrequencyWeight k ^ ((s - r) / 2) : ℝ) • A k := rfl

theorem scalarOrderDown_isDatum {r s : ℝ} (h : s ≤ r) {z : Space → ℝ}
    {A : PeriodicScalarData} (hA : IsPeriodicScalarDatum r z A) :
    IsPeriodicScalarDatum s z (scalarOrderDown r s h A) := by
  refine ⟨hA.1, hA.2.1, fun k ↦ ?_⟩
  rw [scalarOrderDown_apply, hA.2.2 k, smul_smul, ← Real.rpow_add (wpos k)]
  ring_nf

/-- **The tame `ℓ¹` bound.**  The unweighted coefficients are summed against
`∑ₖ W(k)^{-2} < ∞`, so the low factor of the tame estimate is `H²`. -/
theorem scalarAbsCoeff_summable {z : Space → ℝ} {A : PeriodicScalarData}
    (hA : IsPeriodicScalarDatum 2 z A) :
    Summable (scalarAbsCoeff z) ∧
      (∑' k, scalarAbsCoeff z k) ≤ Real.sqrt torusInverseWeightSum * ‖A‖ := by
  have hinv : ∀ k : PeriodicFrequency,
      (periodicFrequencyWeight k ^ (-1 : ℝ)) ^ 2 = periodicFrequencyWeight k ^ (-2 : ℝ) := by
    intro k
    rw [← Real.rpow_natCast (periodicFrequencyWeight k ^ (-1 : ℝ)) 2,
      ← Real.rpow_mul (wpos k).le]
    norm_num
  have hu : Summable (fun k ↦ (periodicFrequencyWeight k ^ (-1 : ℝ)) ^ 2) :=
    torusInverseWeightSum_summable.congr fun k ↦ (hinv k).symm
  obtain ⟨hv, hvval⟩ := scalarDatum_energy hA
  have hsplit : ∀ k : PeriodicFrequency,
      periodicFrequencyWeight k ^ (-1 : ℝ) *
        (periodicFrequencyWeight k ^ ((2 : ℝ) / 2) * scalarAbsCoeff z k) =
      scalarAbsCoeff z k := by
    intro k
    rw [← mul_assoc, ← Real.rpow_add (wpos k)]
    norm_num
  obtain ⟨hs, hb⟩ := lattice_cauchy_schwarz
    (f := fun k ↦ periodicFrequencyWeight k ^ (-1 : ℝ))
    (g := fun k ↦ periodicFrequencyWeight k ^ ((2 : ℝ) / 2) * scalarAbsCoeff z k)
    (fun k ↦ (wrpow_pos k _).le)
    (fun k ↦ mul_nonneg (wrpow_pos k _).le (scalarAbsCoeff_nonneg z k)) hu hv
  refine ⟨hs.congr hsplit, ?_⟩
  rw [← tsum_congr hsplit]
  refine hb.trans (le_of_eq ?_)
  congr 1
  · exact congrArg Real.sqrt (tsum_congr hinv)
  · rw [hvval, Real.sqrt_sq (norm_nonneg A)]

/-! ## 4. Almost-everywhere Fourier inversion for absolutely summable coefficients -/

/-- The complexification of an `L²` real periodic lift stays `L²`. -/
theorem memLp_lift_ofReal {z : Space → ℝ}
    (hz : MemLp (torusLift z) 2 periodicTorusMeasure) :
    MemLp (torusLift (fun x ↦ ((z x : ℝ) : ℂ))) 2 periodicTorusMeasure := by
  refine hz.of_le ?_ (Filter.Eventually.of_forall fun q ↦ ?_)
  · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hz.aestronglyMeasurable
  · show ‖((torusLift z q : ℝ) : ℂ)‖ ≤ ‖torusLift z q‖
    rw [Complex.norm_real]

/-- **Fourier inversion almost everywhere.**  An `L²` periodic scalar whose
coefficients are absolutely summable agrees a.e. with its (continuous) Fourier
series.  Both the `L²` Fourier series and the uniformly convergent series land
in `L²`; the limits agree because sums in a Hausdorff group are unique. -/
theorem torusLift_ae_eq_series {f : Space → ℂ}
    (hf : MemLp (torusLift f) 2 periodicTorusMeasure)
    (hc : Summable fun k ↦ ‖periodicFourierCoeff f k‖) :
    torusLift f =ᵐ[periodicTorusMeasure]
      fun q ↦ ∑' k : PeriodicFrequency,
        periodicFourierCoeff f k * UnitAddTorus.mFourier k q := by
  set c : PeriodicFrequency → ℂ := fun k ↦ periodicFourierCoeff f k with hcdef
  have hsm : Summable (fun k ↦ c k • UnitAddTorus.mFourier (d := Fin 3) k) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hc
  set g : C(PeriodicTorus, ℂ) := ∑' k, c k • UnitAddTorus.mFourier k with hgdef
  have hgs : HasSum (fun k ↦ c k • UnitAddTorus.mFourier (d := Fin 3) k) g := hsm.hasSum
  have hL : HasSum (fun k ↦ c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)
      (ContinuousMap.toLp (E := ℂ) 2 periodicTorusMeasure ℂ g) := by
    have h := hgs.map (ContinuousMap.toLp (E := ℂ) 2 periodicTorusMeasure ℂ) (map_continuous _)
    simpa only [Function.comp_def, map_smul] using h
  have hcoeff : ∀ k, UnitAddTorus.mFourierCoeff (⇑(hf.toLp (torusLift f))) k = c k := by
    intro k
    rw [← UnitAddTorus.mFourierBasis_repr]
    exact fourier_repr_toLp f hf k
  have hF : HasSum (fun k ↦ c k • UnitAddTorus.mFourierLp (d := Fin 3) 2 k)
      (hf.toLp (torusLift f)) := by
    have h := UnitAddTorus.hasSum_mFourier_series_L2 (hf.toLp (torusLift f))
    simpa only [hcoeff] using h
  have heq : hf.toLp (torusLift f) = ContinuousMap.toLp (E := ℂ) 2 periodicTorusMeasure ℂ g :=
    hF.unique hL
  have hgval : ∀ q : PeriodicTorus, g q = ∑' k, c k * UnitAddTorus.mFourier k q := by
    intro q
    have h := hgs.map (ContinuousMap.evalCLM (M := ℂ) ℂ q) (map_continuous _)
    simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
      smul_eq_mul] using h.tsum_eq.symm
  filter_upwards [hf.coeFn_toLp,
    ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (p := 2) periodicTorusMeasure g] with q h1 h2
  rw [← h1, heq, h2, hgval q]

/-! ## 5. The periodic convolution theorem beyond smooth data -/

/-- **Periodic convolution theorem, `H^m` version.**  Smoothness of the first
factor in `MildPressure.periodicFourierCoeff_mul` is only used through the two
facts recorded as hypotheses here: absolute summability of its coefficients and
the a.e. Fourier representation.  Smoothness of the second factor is only used
through integrability of its lift. -/
theorem periodicFourierCoeff_mul_of_series {f g : Space → ℂ}
    (hcf : Summable fun k ↦ ‖periodicFourierCoeff f k‖)
    (hfae : torusLift f =ᵐ[periodicTorusMeasure]
      fun q ↦ ∑' l : PeriodicFrequency,
        periodicFourierCoeff f l * UnitAddTorus.mFourier l q)
    (hg : Integrable (torusLift g) periodicTorusMeasure) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff g (k - l) := by
  set G : PeriodicFrequency → PeriodicTorus → ℂ := fun l q ↦
    periodicFourierCoeff f l * (UnitAddTorus.mFourier (l - k) q * torusLift g q) with hGdef
  have hbdd : ∀ l : PeriodicFrequency,
      Integrable (fun q ↦ UnitAddTorus.mFourier (l - k) q * torusLift g q)
        periodicTorusMeasure := by
    intro l
    refine hg.bdd_mul (UnitAddTorus.mFourier (l - k)).continuous.aestronglyMeasurable
      (c := 1) ?_
    filter_upwards with q
    exact le_of_eq (torusMFourier_norm (l - k) q)
  have hint : ∀ l, Integrable (G l) periodicTorusMeasure := fun l ↦ (hbdd l).const_mul _
  have hnorm : ∀ (l : PeriodicFrequency) (q : PeriodicTorus),
      ‖G l q‖ = ‖periodicFourierCoeff f l‖ * ‖torusLift g q‖ := by
    intro l q
    simp only [hGdef, norm_mul, torusMFourier_norm, one_mul]
  have hsum : Summable (fun l ↦ ∫ q, ‖G l q‖ ∂periodicTorusMeasure) := by
    have he : (fun l ↦ ∫ q, ‖G l q‖ ∂periodicTorusMeasure) =
        fun l ↦ ‖periodicFourierCoeff f l‖ *
          ∫ q, ‖torusLift g q‖ ∂periodicTorusMeasure := by
      funext l
      simp_rw [hnorm l]
      exact integral_const_mul _ _
    rw [he]
    exact hcf.mul_right _
  have hlift : ∀ᵐ q ∂periodicTorusMeasure,
      UnitAddTorus.mFourier (-k) q • torusLift (fun x ↦ f x * g x) q = ∑' l, G l q := by
    filter_upwards [hfae] with q hq
    have he : torusLift (fun x ↦ f x * g x) q = torusLift f q * torusLift g q := rfl
    rw [he, hq, smul_eq_mul, ← tsum_mul_right, ← tsum_mul_left]
    refine tsum_congr fun l ↦ ?_
    simp only [hGdef, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  change (∫ q, UnitAddTorus.mFourier (-k) q •
    torusLift (fun x ↦ f x * g x) q ∂periodicTorusMeasure) = _
  rw [integral_congr_ae hlift, ← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun l ↦ ?_
  show (∫ q, periodicFourierCoeff f l *
    (UnitAddTorus.mFourier (l - k) q * torusLift g q) ∂periodicTorusMeasure) = _
  rw [integral_const_mul]
  congr 1
  change _ = ∫ q, UnitAddTorus.mFourier (-(k - l)) q • torusLift g q ∂periodicTorusMeasure
  simp only [neg_sub, smul_eq_mul]

/-- The convolution identity for two real periodic `H^m` scalars, `m ≥ 2`. -/
theorem scalarCoeff_mul {a b : Space → ℝ}
    (hca : Summable (scalarAbsCoeff a))
    (hae : MemLp (torusLift a) 2 periodicTorusMeasure)
    (hbe : MemLp (torusLift b) 2 periodicTorusMeasure) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((a x * b x : ℝ) : ℂ)) k =
      ∑' l, periodicFourierCoeff (fun x ↦ ((a x : ℝ) : ℂ)) l *
        periodicFourierCoeff (fun x ↦ ((b x : ℝ) : ℂ)) (k - l) := by
  have hmul : (fun x ↦ ((a x * b x : ℝ) : ℂ)) =
      fun x ↦ ((a x : ℝ) : ℂ) * ((b x : ℝ) : ℂ) := by
    funext x
    exact Complex.ofReal_mul _ _
  rw [hmul]
  refine periodicFourierCoeff_mul_of_series hca ?_
    ((memLp_lift_ofReal hbe).integrable (by norm_num)) k
  exact torusLift_ae_eq_series (memLp_lift_ofReal hae) hca

/-! ## 6. The tame product -/

/-- The explicit tame-product constant `4^{m/2} (∑ₖ W(k)^{-2})^{1/2}`. -/
def tameProductConst (m : ℕ) : ℝ :=
  (4 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt torusInverseWeightSum

/-- The tame-product constant is positive at every order. -/
theorem tameProductConst_pos (m : ℕ) : 0 < tameProductConst m := by
  have h1 : (0 : ℝ) < (4 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : 0 < Real.sqrt torusInverseWeightSum :=
    Real.sqrt_pos.mpr torusInverseWeightSum_pos
  exact mul_pos h1 h2

/-- The order-`m` weighted coefficient sequence of a product. -/
private def productCoeff (m : ℕ) (a b : Space → ℝ) (k : PeriodicFrequency) : ℂ :=
  (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) •
    periodicFourierCoeff (fun x ↦ ((a x * b x : ℝ) : ℂ)) k

/-- **The scalar tame product on the torus.**  The `tameProduct` field of the
reconciled `MeanZeroSobolevCalculusAPI`, with `Cproduct := tameProductConst`. -/
theorem tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (tameProductConst m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a) := by
  intro m hm a b ha hb
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmhalf : (0 : ℝ) ≤ (m : ℝ) / 2 := by linarith
  have hmone : (1 : ℝ) ≤ (m : ℝ) / 2 := by linarith
  obtain ⟨Am, hAm⟩ := exists_scalarDatum ha.2.2
  obtain ⟨Bm, hBm⟩ := exists_scalarDatum hb.2.2
  set A2 : PeriodicScalarData := scalarOrderDown (m : ℝ) 2 hm2 Am with hA2def
  set B2 : PeriodicScalarData := scalarOrderDown (m : ℝ) 2 hm2 Bm with hB2def
  have hA2 : IsPeriodicScalarDatum 2 a A2 := scalarOrderDown_isDatum hm2 hAm
  have hB2 : IsPeriodicScalarDatum 2 b B2 := scalarOrderDown_isDatum hm2 hBm
  set alp : PeriodicFrequency → ℝ := scalarAbsCoeff a with halpdef
  set bet : PeriodicFrequency → ℝ := scalarAbsCoeff b with hbetdef
  set Aw : PeriodicFrequency → ℝ :=
    fun k ↦ periodicFrequencyWeight k ^ ((m : ℝ) / 2) * alp k with hAwdef
  set Bw : PeriodicFrequency → ℝ :=
    fun k ↦ periodicFrequencyWeight k ^ ((m : ℝ) / 2) * bet k with hBwdef
  have halp0 : ∀ k, 0 ≤ alp k := fun k ↦ scalarAbsCoeff_nonneg a k
  have hbet0 : ∀ k, 0 ≤ bet k := fun k ↦ scalarAbsCoeff_nonneg b k
  have hAw0 : ∀ k, 0 ≤ Aw k := fun k ↦ mul_nonneg (wrpow_pos k _).le (halp0 k)
  have hBw0 : ∀ k, 0 ≤ Bw k := fun k ↦ mul_nonneg (wrpow_pos k _).le (hbet0 k)
  obtain ⟨hAwS, hAwV⟩ := scalarDatum_energy hAm
  obtain ⟨hBwS, hBwV⟩ := scalarDatum_energy hBm
  obtain ⟨halp1, halp1b⟩ := scalarAbsCoeff_summable hA2
  obtain ⟨hbet1, hbet1b⟩ := scalarAbsCoeff_summable hB2
  obtain ⟨huc, huS, huB⟩ := torusYoungConvolution hAw0 hbet0 hAwS hbet1
  obtain ⟨hvc, hvS, hvB⟩ := torusYoungConvolution hBw0 halp0 hBwS halp1
  set u : PeriodicFrequency → ℝ := fun k ↦ ∑' l, Aw l * bet (k - l) with hudef
  set v : PeriodicFrequency → ℝ := fun k ↦ ∑' l, Bw l * alp (k - l) with hvdef
  have huBound : Real.sqrt (∑' k, u k ^ 2) ≤
      ‖Am‖ * (Real.sqrt torusInverseWeightSum * ‖B2‖) := by
    refine huB.trans (mul_le_mul ?_ hbet1b (tsum_nonneg hbet0) (norm_nonneg Am))
    rw [hAwV, Real.sqrt_sq (norm_nonneg Am)]
  have hvBound : Real.sqrt (∑' k, v k ^ 2) ≤
      ‖Bm‖ * (Real.sqrt torusInverseWeightSum * ‖A2‖) := by
    refine hvB.trans (mul_le_mul ?_ halp1b (tsum_nonneg halp0) (norm_nonneg Bm))
    rw [hBwV, Real.sqrt_sq (norm_nonneg Bm)]
  -- the mixed convolution, in the orientation Peetre produces
  have hmix : ∀ k, Summable fun l ↦ alp l * Bw (k - l) := fun k ↦
    conv_comm_summable k (hvc k)
  have hmixval : ∀ k, (∑' l, alp l * Bw (k - l)) = v k := fun k ↦ torusConv_comm alp Bw k
  have hconvAbs : ∀ k, Summable fun l ↦ alp l * bet (k - l) := by
    intro k
    refine (huc k).of_nonneg_of_le (fun l ↦ mul_nonneg (halp0 l) (hbet0 _)) fun l ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (hbet0 _)
    have h : (1 : ℝ) * alp l ≤ periodicFrequencyWeight l ^ ((m : ℝ) / 2) * alp l :=
      mul_le_mul_of_nonneg_right (one_le_wrpow l hmhalf) (halp0 l)
    simpa using h
  have hpointwise : ∀ k, ‖productCoeff m a b k‖ ≤
      (4 : ℝ) ^ ((m : ℝ) / 2) * (u k + v k) := by
    intro k
    have hcoeff := scalarCoeff_mul (a := a) (b := b) halp1 ha.2.1 hb.2.1 k
    have hnorm1 : ‖periodicFourierCoeff (fun x ↦ ((a x * b x : ℝ) : ℂ)) k‖ ≤
        ∑' l, alp l * bet (k - l) := by
      rw [hcoeff]
      have hs : Summable fun l ↦
          ‖periodicFourierCoeff (fun x ↦ ((a x : ℝ) : ℂ)) l *
            periodicFourierCoeff (fun x ↦ ((b x : ℝ) : ℂ)) (k - l)‖ :=
        (hconvAbs k).congr fun l ↦ (norm_mul _ _).symm
      refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr fun l ↦ ?_))
      exact norm_mul _ _
    have hterm : ∀ l, periodicFrequencyWeight k ^ ((m : ℝ) / 2) * (alp l * bet (k - l)) ≤
        (4 : ℝ) ^ ((m : ℝ) / 2) * (Aw l * bet (k - l) + alp l * Bw (k - l)) := by
      intro l
      have hpeetre := torusWeightPeetre (a := (m : ℝ) / 2) hmhalf k l
      have hnn : 0 ≤ alp l * bet (k - l) := mul_nonneg (halp0 l) (hbet0 _)
      refine (mul_le_mul_of_nonneg_right hpeetre hnn).trans (le_of_eq ?_)
      simp only [hAwdef, hBwdef]
      ring
    have hmaj : Summable fun l ↦
        (4 : ℝ) ^ ((m : ℝ) / 2) * (Aw l * bet (k - l) + alp l * Bw (k - l)) :=
      ((huc k).add (hmix k)).mul_left _
    have hstep : periodicFrequencyWeight k ^ ((m : ℝ) / 2) * (∑' l, alp l * bet (k - l)) ≤
        (4 : ℝ) ^ ((m : ℝ) / 2) * (u k + v k) := by
      rw [← tsum_mul_left]
      refine (((hconvAbs k).mul_left _).tsum_le_tsum hterm hmaj).trans (le_of_eq ?_)
      rw [tsum_mul_left, Summable.tsum_add (huc k) (hmix k), hmixval k]
    calc ‖productCoeff m a b k‖
        = periodicFrequencyWeight k ^ ((m : ℝ) / 2) *
            ‖periodicFourierCoeff (fun x ↦ ((a x * b x : ℝ) : ℂ)) k‖ := by
          rw [productCoeff, norm_smul, Real.norm_eq_abs, abs_of_pos (wrpow_pos k _)]
      _ ≤ periodicFrequencyWeight k ^ ((m : ℝ) / 2) * (∑' l, alp l * bet (k - l)) :=
          mul_le_mul_of_nonneg_left hnorm1 (wrpow_pos k _).le
      _ ≤ _ := hstep
  obtain ⟨hsumUV, hUV⟩ := l2_add_bound huS hvS
  have hfour : (0 : ℝ) ≤ (4 : ℝ) ^ ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hPsq : Summable fun k ↦ ‖productCoeff m a b k‖ ^ 2 := by
    refine (hsumUV.mul_left (((4 : ℝ) ^ ((m : ℝ) / 2)) ^ 2)).of_nonneg_of_le
      (fun k ↦ sq_nonneg _) fun k ↦ ?_
    have h1 := hpointwise k
    have h2 : (0 : ℝ) ≤ ‖productCoeff m a b k‖ := norm_nonneg _
    nlinarith [h1, h2]
  set P : PeriodicScalarData := ⟨productCoeff m a b, cplxLp_mem _ hPsq⟩ with hPdef
  have hPdatum : IsPeriodicScalarDatum (m : ℝ) (fun x ↦ a x * b x) P := by
    refine ⟨?_, ?_, fun k ↦ rfl⟩
    · intro x i
      show a (x + coordinateVector i) * b (x + coordinateVector i) = a x * b x
      rw [ha.1 x i, hb.1 x i]
    · exact (ha.2.1.integrable_mul hb.2.1).congr (Filter.Eventually.of_forall fun q ↦ rfl)
  have hPnorm : ‖P‖ = Real.sqrt (∑' k, ‖productCoeff m a b k‖ ^ 2) := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) P
    rw [show (∑' k : PeriodicFrequency, ‖P k‖ ^ (2 : ℝ≥0∞).toReal) =
      ∑' k, ‖productCoeff m a b k‖ ^ 2 from
      tsum_congr fun k ↦ cnorm_rpow_two _] at h
    rw [← h]
    simp only [ENNReal.toReal_ofNat]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sqrt_sq (norm_nonneg P)]
  have hreal : ‖P‖ ≤ tameProductConst m * (‖A2‖ * ‖Bm‖ + ‖B2‖ * ‖Am‖) := by
    have hsq : (∑' k, ‖productCoeff m a b k‖ ^ 2) ≤
        ((4 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 * (∑' k, (u k + v k) ^ 2) := by
      rw [← tsum_mul_left]
      refine hPsq.tsum_le_tsum (fun k ↦ ?_) (hsumUV.mul_left _)
      have h1 := hpointwise k
      have h2 : (0 : ℝ) ≤ ‖productCoeff m a b k‖ := norm_nonneg _
      nlinarith [h1, h2]
    have hstep : ‖P‖ ≤ (4 : ℝ) ^ ((m : ℝ) / 2) * Real.sqrt (∑' k, (u k + v k) ^ 2) := by
      rw [hPnorm]
      refine (Real.sqrt_le_sqrt hsq).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hfour]
    have hsum2 : Real.sqrt (∑' k, (u k + v k) ^ 2) ≤
        Real.sqrt torusInverseWeightSum * (‖A2‖ * ‖Bm‖ + ‖B2‖ * ‖Am‖) := by
      refine hUV.trans ?_
      nlinarith [huBound, hvBound]
    refine hstep.trans ?_
    rw [tameProductConst, mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum2 hfour
  rw [periodicScalarSobolevENorm_eq hPdatum, periodicScalarSobolevENorm_eq hA2,
    periodicScalarSobolevENorm_eq hB2, periodicScalarSobolevENorm_eq hAm,
    periodicScalarSobolevENorm_eq hBm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg A2),
    ← ENNReal.ofReal_mul (norm_nonneg B2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (tameProductConst_pos m).le]
  exact ENNReal.ofReal_le_ofReal hreal


/-! ## 7. Non-vacuity: every admissible coefficient family is realized

The `tameProduct` hypotheses are not vacuous.  Every conjugate-symmetric,
absolutely summable, order-`m`-weighted square-summable coefficient family is
the coefficient family of an honest real periodic scalar in `H^m(T³)`, with
exactly the prescribed coefficients.  Finitely supported families give
genuinely multi-mode witnesses. -/

/-- The real physical scalar attached to a conjugate-symmetric coefficient
family: the real part of its (absolutely convergent) Fourier series. -/
def scalarOfCoeff (c : PeriodicFrequency → ℂ) (x : Space) : ℝ :=
  (torusScalarSeries c x).re

theorem scalarOfCoeff_ofReal {c : PeriodicFrequency → ℂ}
    (hneg : ∀ k, c (-k) = star (c k)) (x : Space) :
    ((scalarOfCoeff c x : ℝ) : ℂ) = torusScalarSeries c x :=
  Complex.conj_eq_iff_re.mp (torusScalarSeries_conj hneg x)

theorem scalarOfCoeff_periodic (c : PeriodicFrequency → ℂ) :
    IsPeriodicSpatial (scalarOfCoeff c) := by
  intro x j
  show (torusScalarSeries c (x + coordinateVector j)).re = (torusScalarSeries c x).re
  rw [torusScalarSeries_periodic c x j]

theorem scalarOfCoeff_coeff {c : PeriodicFrequency → ℂ}
    (hneg : ∀ k, c (-k) = star (c k)) (habs : Summable fun k ↦ ‖c k‖)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((scalarOfCoeff c x : ℝ) : ℂ)) k = c k := by
  have he : (fun x ↦ ((scalarOfCoeff c x : ℝ) : ℂ)) = torusScalarSeries c :=
    funext (scalarOfCoeff_ofReal hneg)
  rw [he]
  exact torusScalarSeries_coeff habs k

private lemma memLp_torusLift_real {f : Space → ℝ} (hf : Continuous f) (q : ℝ≥0∞) :
    MemLp (torusLift f) q periodicTorusMeasure := by
  have hc : MemLp (torusLift (fun x ↦ ((f x : ℝ) : ℂ))) q periodicTorusMeasure :=
    NSFormalization.Paper1.memLp_torusLift (Complex.continuous_ofReal.comp hf) q
  refine hc.of_le ?_ (Filter.Eventually.of_forall fun y ↦ ?_)
  · exact Complex.continuous_re.comp_aestronglyMeasurable hc.aestronglyMeasurable
  · show ‖torusLift f y‖ ≤ ‖((torusLift f y : ℝ) : ℂ)‖
    rw [Complex.norm_real]

/-- **Realization.**  An admissible coefficient family is the family of a real
periodic scalar lying in `H^m(T³)`. -/
theorem memPeriodicHmScalar_ofCoeff {m : ℕ} {c : PeriodicFrequency → ℂ}
    (hneg : ∀ k, c (-k) = star (c k)) (habs : Summable fun k ↦ ‖c k‖)
    (hcont : Continuous (torusScalarSeries c))
    (hw : Summable fun k ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) * ‖c k‖) ^ 2) :
    MemPeriodicHmScalar m (scalarOfCoeff c) := by
  have hre : Continuous (scalarOfCoeff c) := Complex.continuous_re.comp hcont
  have hL2 : MemLp (torusLift (scalarOfCoeff c)) 2 periodicTorusMeasure :=
    memLp_torusLift_real hre 2
  have hmem : Memℓp (fun k ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • c k) 2 := by
    refine cplxLp_mem _ (hw.congr fun k ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (wrpow_pos k _)]
  refine ⟨scalarOfCoeff_periodic c, hL2, ?_⟩
  have hdatum : IsPeriodicScalarDatum (m : ℝ) (scalarOfCoeff c)
      ⟨fun k ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • c k, hmem⟩ := by
    refine ⟨scalarOfCoeff_periodic c, hL2.integrable (by norm_num), fun k ↦ ?_⟩
    show (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • c k =
      (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) •
        periodicFourierCoeff (fun x ↦ ((scalarOfCoeff c x : ℝ) : ℂ)) k
    rw [scalarOfCoeff_coeff hneg habs k]
  rw [periodicScalarSobolevENorm_eq hdatum, ← ofReal_norm]
  exact ENNReal.ofReal_ne_top

end NSFormalization.Section3.T12
