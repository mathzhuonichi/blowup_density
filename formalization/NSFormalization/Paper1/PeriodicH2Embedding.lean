import NSFormalization.Paper1.PeriodicSobolevHilbert
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# A spectral (H^2)-to-(L^infty) estimate on the unit three-torus

This module isolates the part of the periodic embedding that is purely
Fourier-algebraic.  For a finite frequency set, Cauchy--Schwarz bounds the
Fourier partial sum by the weighted (H^2) energy times the inverse-square
weight sum.  The infinite-series statement is then obtained from Mathlib's
uniform Fourier-series theorem, under an explicit summability hypothesis for
the inverse weight.  The latter hypothesis is kept visible: this file does
not silently identify a lattice counting theorem with the Paper 1 frequency
convention, and it makes no claim about the critical (H^{1/2}\to L^3)
endpoint.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NSFormalization.Paper1

abbrev PeriodicTorusC := C(UnitAddTorus (Fin 3), ℂ)

def periodicH2Weight (k : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k ^ (2 : ℝ)

def periodicH2InverseWeight (k : PeriodicFrequency) : ℝ :=
  (periodicH2Weight k)⁻¹

theorem periodicH2Weight_pos (k : PeriodicFrequency) : 0 < periodicH2Weight k := by
  unfold periodicH2Weight
  positivity [one_le_periodicFrequencyWeight k]

theorem periodicH2Weight_mul_inverse (k : PeriodicFrequency) :
    periodicH2Weight k * periodicH2InverseWeight k = 1 := by
  exact mul_inv_cancel₀ (ne_of_gt (periodicH2Weight_pos k))

theorem periodicH2InverseWeight_zero :
    periodicH2InverseWeight (0 : PeriodicFrequency) = 1 := by
  unfold periodicH2InverseWeight periodicH2Weight periodicFrequencyWeight
  norm_num

theorem finite_fourier_sum_h2_bound
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency) :
    ‖∑ k ∈ S, c k‖ ≤
      Real.sqrt (∑ k ∈ S, periodicH2Weight k * ‖c k‖ ^ 2) *
        Real.sqrt (∑ k ∈ S, periodicH2InverseWeight k) := by
  have hterm (k : PeriodicFrequency) :
      ‖c k‖ =
        (Real.sqrt (periodicH2Weight k) * ‖c k‖) *
          Real.sqrt (periodicH2InverseWeight k) := by
    have hw := periodicH2Weight_pos k
    have hi : 0 ≤ periodicH2InverseWeight k := inv_nonneg.mpr hw.le
    calc
      ‖c k‖ = Real.sqrt (periodicH2Weight k * periodicH2InverseWeight k) * ‖c k‖ := by
        rw [periodicH2Weight_mul_inverse, Real.sqrt_one, one_mul]
      _ = _ := by rw [Real.sqrt_mul hw.le]; ring
  calc
    ‖∑ k ∈ S, c k‖ ≤ ∑ k ∈ S, ‖c k‖ := norm_sum_le S _
    _ = ∑ k ∈ S,
        (Real.sqrt (periodicH2Weight k) * ‖c k‖) *
          Real.sqrt (periodicH2InverseWeight k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k
    _ ≤ Real.sqrt (∑ k ∈ S,
          (Real.sqrt (periodicH2Weight k) * ‖c k‖) ^ 2) *
        Real.sqrt (∑ k ∈ S, (Real.sqrt (periodicH2InverseWeight k)) ^ 2) := by
      exact Real.sum_mul_le_sqrt_mul_sqrt S
        (fun k => Real.sqrt (periodicH2Weight k) * ‖c k‖)
        (fun k => Real.sqrt (periodicH2InverseWeight k))
    _ = _ := by
      congr 1
      · apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro k hk
        rw [mul_pow, Real.sq_sqrt (periodicH2Weight_pos k).le]
      · apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro k hk
        exact Real.sq_sqrt (inv_nonneg.mpr (periodicH2Weight_pos k).le)

theorem finite_fourier_sum_h2_bound_of_energy
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    {E B : ℝ} (hE : ∑ k ∈ S, periodicH2Weight k * ‖c k‖ ^ 2 ≤ E ^ 2)
    (hB : ∑ k ∈ S, periodicH2InverseWeight k ≤ B ^ 2)
    (hE0 : 0 ≤ E) (hB0 : 0 ≤ B) :
    ‖∑ k ∈ S, c k‖ ≤ E * B := by
  apply (finite_fourier_sum_h2_bound c S).trans
  exact mul_le_mul (Real.sqrt_le_iff.mpr ⟨by positivity, hE⟩)
    (Real.sqrt_le_iff.mpr ⟨by positivity, hB⟩) (Real.sqrt_nonneg _) hE0

/- A reusable interface for the missing lattice-normalization step.  Any
explicit majorant for the inverse Bessel weight can be plugged in here;
the theorem then records the resulting genuine summability, rather than
silently relying on the default-zero value of an unproved `tsum`. -/
theorem summable_periodicH2InverseWeight_of_majorant
    {m : PeriodicFrequency → ℝ} (hm : Summable m)
    (hmajor : ∀ k, periodicH2InverseWeight k ≤ m k) :
    Summable (fun k => periodicH2InverseWeight k) := by
  apply Summable.of_nonneg_of_le
    (fun k => inv_nonneg.mpr (periodicH2Weight_pos k).le) hmajor hm

/- The finite Fourier estimate with the global inverse-weight constant.  This
is the exact bridge needed after an inverse-weight lattice comparison has
been proved (for example by splitting off the zero mode and using the
Euclidean `‖k‖⁻⁴` lattice series below). -/
theorem finite_fourier_sum_h2_bound_of_summable_inverse
    (c : PeriodicFrequency → ℂ) (S : Finset PeriodicFrequency)
    {E : ℝ} (hE : ∑ k ∈ S, periodicH2Weight k * ‖c k‖ ^ 2 ≤ E ^ 2)
    (hE0 : 0 ≤ E)
    (hInv : Summable (fun k => periodicH2InverseWeight k)) :
    ‖∑ k ∈ S, c k‖ ≤ E * Real.sqrt (∑' k, periodicH2InverseWeight k) := by
  have htsum : 0 ≤ ∑' k, periodicH2InverseWeight k :=
    tsum_nonneg (fun k => inv_nonneg.mpr (periodicH2Weight_pos k).le)
  have hB : ∑ k ∈ S, periodicH2InverseWeight k ≤
      (Real.sqrt (∑' k, periodicH2InverseWeight k)) ^ 2 := by
    simpa only [Real.sq_sqrt htsum] using
      (show (∑ k ∈ S, periodicH2InverseWeight k) ≤
          ∑' k, periodicH2InverseWeight k from by
        simpa only [periodicH2InverseWeight] using
          (Summable.sum_le_tsum S
        (fun k _ => inv_nonneg.mpr (periodicH2Weight_pos k).le) hInv)
      )
  exact finite_fourier_sum_h2_bound_of_energy c S hE hB hE0
    (Real.sqrt_nonneg _)

private abbrev FrequencyLattice :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

private noncomputable def frequencyEquiv : PeriodicFrequency ≃ₗ[ℤ] FrequencyLattice :=
  ((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ).equivFun.symm

private theorem frequencyEquiv_coe (k : PeriodicFrequency) :
    (frequencyEquiv k : Fin 3 → ℝ) = fun i => (k i : ℝ) := by
  ext i
  simp [frequencyEquiv, Module.Basis.equivFun_symm_apply, Finset.sum_apply, Pi.single_apply]

private theorem summable_frequency_norm_neg_four :
    Summable (fun k : PeriodicFrequency => ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ)) := by
  letI : DiscreteTopology FrequencyLattice := ZSpan.discreteTopology_pi_basisFun
  have hdim : Module.finrank ℤ FrequencyLattice = 3 := by
    rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ)]
    rfl
  have h := (frequencyEquiv.toEquiv.summable_iff).mpr
    (ZLattice.summable_norm_rpow FrequencyLattice (-4) (by rw [hdim]; norm_num))
  change Summable (fun k => ‖(frequencyEquiv k : Fin 3 → ℝ)‖ ^ (-4 : ℝ)) at h
  simpa only [frequencyEquiv_coe] using h

/- The lattice result is kept as a named export for the final normalization
bridge: comparing the paper's inverse Bessel weight with this Euclidean
`norm ^ (-4)` series is a separate, explicit step. -/
theorem periodic_frequency_inverse_norm_series :
    Summable (fun k : PeriodicFrequency => ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ)) :=
  summable_frequency_norm_neg_four

private theorem summable_inverse_norm_off_zero :
    Summable (fun k : PeriodicFrequency =>
      if k = (0 : PeriodicFrequency) then (0 : ℝ)
      else ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ)) := by
  apply Summable.congr periodic_frequency_inverse_norm_series
  intro k
  by_cases h : k = (0 : PeriodicFrequency)
  · subst k
    norm_num
  · simp [h]

private theorem summable_zero_mode_indicator :
    Summable (fun k : PeriodicFrequency =>
      if k = (0 : PeriodicFrequency) then (1 : ℝ) else 0) := by
  apply summable_of_hasFiniteSupport
  refine Set.Finite.subset (Set.finite_singleton (0 : PeriodicFrequency)) ?_
  intro x hx
  by_contra hne
  simp [Function.mem_support] at hx
  exact hne hx

/-- The Euclidean inverse-fourth-power series remains summable after restoring
the single zero-frequency term. -/
theorem summable_inverse_norm_with_zero :
    Summable (fun k : PeriodicFrequency =>
      if k = (0 : PeriodicFrequency) then (1 : ℝ)
      else ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ)) := by
  have h := summable_zero_mode_indicator.add summable_inverse_norm_off_zero
  apply h.congr
  intro k
  by_cases hk : k = (0 : PeriodicFrequency)
  · subst k
    norm_num
  · simp [hk]

/-- A zero-mode-split form of the missing inverse Bessel comparison.  It only
asks for the nonzero-frequency inequality against the verified Euclidean
lattice majorant. -/
theorem summable_periodicH2InverseWeight_of_nonzero_comparison
    (hmajor : ∀ k ≠ (0 : PeriodicFrequency),
      periodicH2InverseWeight k ≤
        ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ)) :
    Summable (fun k => periodicH2InverseWeight k) := by
  apply summable_periodicH2InverseWeight_of_majorant
    summable_inverse_norm_with_zero
  intro k
  by_cases hk : k = (0 : PeriodicFrequency)
  · subst k
    simp [periodicH2InverseWeight_zero]
  · simp only [hk, ↓reduceIte]
    exact hmajor k hk

theorem periodicH2InverseWeight_le_norm_neg_four_of_ne_zero
    {k : PeriodicFrequency} (hk : k ≠ (0 : PeriodicFrequency)) :
    periodicH2InverseWeight k ≤
      ‖(fun i => (k i : ℝ))‖ ^ (-4 : ℝ) := by
  let x : Fin 3 → ℝ := fun i => (k i : ℝ)
  have hx : x ≠ 0 := by
    intro hz; apply hk; ext i
    have hi := congrFun hz i
    change (k i : ℝ) = 0 at hi
    exact_mod_cast hi
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsumabs : ‖x‖ ≤ ∑ i : Fin 3, |x i| := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [Real.norm_eq_abs, Finset.sum_filter,
      Finset.filter_true_of_mem] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun j : Fin 3 => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hsq := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i : Fin 3 => |x i|)
  norm_num [sq_abs] at hsq
  have hnormsq : ‖x‖ ^ 2 ≤ 3 * ∑ i : Fin 3, x i ^ 2 := by
    have hsumabs0 : 0 ≤ ∑ i : Fin 3, |x i| := by positivity
    nlinarith
  have hpi : 3 ≤ (2 * Real.pi) ^ 2 := by
    have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith [sq_nonneg (Real.pi - 3)]
  have hsum : 0 ≤ ∑ i : Fin 3, x i ^ 2 := by positivity
  have hmul : 3 * (∑ i : Fin 3, x i ^ 2) ≤
      (2 * Real.pi) ^ 2 * ∑ i : Fin 3, x i ^ 2 :=
    mul_le_mul_of_nonneg_right hpi hsum
  have hbase : ‖x‖ ^ 2 ≤ 1 + (2 * Real.pi) ^ 2 * ∑ i : Fin 3, x i ^ 2 := by
    nlinarith
  have hsq' : ‖x‖ ^ 4 ≤
      (1 + (2 * Real.pi) ^ 2 * ∑ i : Fin 3, x i ^ 2) ^ 2 := by
    have hm := mul_self_le_mul_self (sq_nonneg (‖x‖)) hbase
    nlinarith
  have hweight : periodicH2Weight k =
      (1 + (2 * Real.pi) ^ 2 * ∑ i : Fin 3, x i ^ 2) ^ 2 := by
    rw [periodicH2Weight, periodicFrequencyWeight_eq]
    simp only [Real.rpow_two]
    rfl
  have hinv : periodicH2InverseWeight k ≤ (‖x‖ ^ 4)⁻¹ := by
    rw [periodicH2InverseWeight, hweight]
    have hh := one_div_le_one_div_of_le (show 0 < ‖x‖ ^ 4 by positivity) hsq'
    simpa [one_div] using hh
  rw [Real.rpow_neg (le_of_lt hxn)]
  convert hinv using 1 <;> norm_num [Real.rpow_natCast]

theorem summable_periodicH2InverseWeight :
    Summable (fun k : PeriodicFrequency => periodicH2InverseWeight k) :=
  summable_periodicH2InverseWeight_of_nonzero_comparison
    (fun k hk => periodicH2InverseWeight_le_norm_neg_four_of_ne_zero hk)

end NSFormalization.Paper1
