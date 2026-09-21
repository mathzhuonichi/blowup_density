import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

section

/-!
Explicit numerical estimates for the factorial majorants used in the proposed
Euler construction. These lemmas prove combinatorial implications; they do not
assert the analytic estimates needed to apply the implications to Euler.
-/

namespace EulerGevrey

open Finset

/-- Every interior entry of the `n`th binomial row is at least `n`. -/
theorem le_choose_of_interior (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      by_cases hk1 : k = 1
      · simp [hk1]
      by_cases hkn' : k = n
      · subst k
        simp
      have hklt : k < n := by omega
      have hkp : 0 < k - 1 := by omega
      have hp := ih (k - 1) hkp (by omega)
      have hq := ih k hk hklt
      rw [Nat.choose_succ_left n k hk]
      omega

/-- The reciprocal binomial row has uniformly bounded sum, including order zero. -/
theorem sum_inv_choose_le_three (n : ℕ) :
    ∑ k ∈ range (n + 1), (1 : ℝ) / (n.choose k : ℝ) ≤ 3 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hsum : ∑ k ∈ range n, (1 : ℝ) / ((n + 1).choose (k + 1) : ℝ)
          ≤ n * (1 / (n + 1) : ℝ) := by
        calc
          _ ≤ ∑ _k ∈ range n, (1 / (n + 1) : ℝ) := by
            apply sum_le_sum
            intro k hk
            apply one_div_le_one_div_of_le hn
            exact_mod_cast le_choose_of_interior (n + 1) (k + 1)
              (by omega) (by have := mem_range.mp hk; omega)
          _ = _ := by simp
      have hquot : (n : ℝ) * (1 / (n + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hn]
        linarith
      rw [sum_range_succ', sum_range_succ]
      norm_num only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, div_one]
      linarith

/-- Adding nonnegative shifts to both lower factorial indices enlarges the binomial coefficient. -/
theorem choose_le_shifted (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    n.choose k ≤ (n + d₁ + d₂).choose (k + d₁) := by
  calc
    n.choose k = n.choose (n - k) := (Nat.choose_symm hkn).symm
    _ ≤ (n + d₁).choose (n - k) := Nat.choose_le_add n d₁ (n - k)
    _ = (n + d₁).choose (k + d₁) := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ ≤ (n + d₁ + d₂).choose (k + d₁) :=
      Nat.choose_le_add (n + d₁) d₂ (k + d₁)

/-- The exact reciprocal-binomial comparison used in the shifted product estimate. -/
theorem choose_ratio_le_inv (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2
      ≤ 1 / (n.choose k : ℝ) := by
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hle : (n.choose k : ℝ) ≤ (n + d₁ + d₂).choose (k + d₁) := by
    exact_mod_cast choose_le_shifted n k d₁ d₂ hkn
  apply (div_le_div_iff₀ (sq_pos_of_pos (lt_of_lt_of_le hc hle)) hc).2
  nlinarith

/-- A term of the shifted factorial convolution gains the reciprocal binomial coefficient. -/
theorem shifted_factorial_kernel_le (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
        ((n - k + d₂).factorial : ℝ) ^ 2
      ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 / (n.choose k : ℝ) := by
  have hlarge : k + d₁ ≤ n + d₁ + d₂ := by omega
  have hsub : n + d₁ + d₂ - (k + d₁) = n - k + d₂ := by omega
  have hfac : ((n + d₁ + d₂).choose (k + d₁) : ℝ) *
      ((k + d₁).factorial : ℝ) * ((n - k + d₂).factorial : ℝ) =
      ((n + d₁ + d₂).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hlarge
    rw [hsub] at h
    exact_mod_cast h
  have hC : ((n + d₁ + d₂).choose (k + d₁) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hlarge
  calc
    _ = ((n + d₁ + d₂).factorial : ℝ) ^ 2 *
        ((n.choose k : ℝ) / ((n + d₁ + d₂).choose (k + d₁) : ℝ) ^ 2) := by
      rw [← hfac]
      field_simp
    _ ≤ ((n + d₁ + d₂).factorial : ℝ) ^ 2 * (1 / (n.choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left (choose_ratio_le_inv n k d₁ d₂ hkn) (sq_nonneg _)
    _ = _ := by ring

/-- The Gevrey-two factorial majorant with a nonnegative integer shift. -/
def majorant (R : ℝ) (d n : ℕ) : ℝ :=
  R ^ (n + d) * ((n + d).factorial : ℝ) ^ 2

theorem majorant_nonneg (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    0 ≤ majorant R d n := by
  unfold majorant
  positivity

/-- A single Leibniz term obeys the uniform shifted estimate. -/
theorem majorant_product_term (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
  have hexp : k + d₁ + (n - k + d₂) = n + d₁ + d₂ := by omega
  have hpow : R ^ (k + d₁) * R ^ (n - k + d₂) = R ^ (n + d₁ + d₂) := by
    rw [← pow_add, hexp]
  have h := mul_le_mul_of_nonneg_left (shifted_factorial_kernel_le n k d₁ d₂ hkn)
    (pow_nonneg hR (n + d₁ + d₂))
  unfold majorant
  simp only [← Nat.add_assoc]
  calc
    _ = (R ^ (k + d₁) * R ^ (n - k + d₂)) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by ring
    _ = R ^ (n + d₁ + d₂) *
        ((n.choose k : ℝ) * ((k + d₁).factorial : ℝ) ^ 2 *
          ((n - k + d₂).factorial : ℝ) ^ 2) := by rw [hpow]
    _ ≤ _ := by simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using h

/-- The product constant is exactly `3`, independently of order and both shifts. -/
theorem majorant_convolution (R : ℝ) (hR : 0 ≤ R) (n d₁ d₂ : ℕ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ 3 * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        majorant R (d₁ + d₂) n * (1 / (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact majorant_product_term R hR n k d₁ d₂ (by have := mem_range.mp hk; omega)
    _ = majorant R (d₁ + d₂) n *
        ∑ k ∈ range (n + 1), (1 / (n.choose k : ℝ)) := by rw [mul_sum]
    _ ≤ majorant R (d₁ + d₂) n * 3 :=
      mul_le_mul_of_nonneg_left (sum_inv_choose_le_three n) (majorant_nonneg R hR _ _)
    _ = _ := by ring

/-- Discarding the reciprocal binomial gain is valid for each admissible split. -/
theorem majorant_product_term_le (R : ℝ) (hR : 0 ≤ R)
    (n k d₁ d₂ : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)
      ≤ majorant R (d₁ + d₂) n := by
  have hc : (1 : ℝ) ≤ n.choose k := by
    exact_mod_cast Nat.choose_pos hkn
  have hi : (1 : ℝ) / (n.choose k : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc
  exact (majorant_product_term R hR n k d₁ d₂ hkn).trans
    (mul_le_of_le_one_right (majorant_nonneg R hR _ _) hi)

/-- One spare factorial shift supplies a factor of at least `R`. -/
theorem majorant_shift_le (R : ℝ) (hR : 0 ≤ R) (d n : ℕ) :
    R * majorant R d n ≤ majorant R (d + 1) n := by
  have hf : (((n + d).factorial : ℕ) : ℝ) ≤ ((n + (d + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show n + d ≤ n + (d + 1) by omega)
  have hs : ((n + d).factorial : ℝ) ^ 2 ≤ ((n + (d + 1)).factorial : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n + d).factorial by positivity]
  unfold majorant
  calc
    _ = R ^ (n + (d + 1)) * ((n + d).factorial : ℝ) ^ 2 := by
      rw [show n + (d + 1) = (n + d) + 1 by omega, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (pow_nonneg hR _)

/-- The geometric tail is bounded uniformly in the truncation length. -/
theorem geometric_tail_le_two_mul (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (n : ℕ) : ∑ k ∈ range n, q ^ (k + 1) ≤ 2 * q := by
  have hgeom : ∀ m : ℕ, ∑ k ∈ range m, q ^ k ≤ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [sum_range_succ']
        simp_rw [pow_succ]
        rw [← sum_mul]
        simp only [pow_zero]
        have hm := mul_le_mul_of_nonneg_right ih hq
        linarith
  simpa only [pow_succ, ← sum_mul] using mul_le_mul_of_nonneg_right (hgeom n) hq

/-- A coefficient of radius `Rc ≤ q R` has the geometric gain `q^k`. -/
theorem majorant_coefficient_term (R Rc q : ℝ)
    (hR : 0 ≤ R) (hRc : 0 ≤ Rc) (hq : 0 ≤ q) (hscale : Rc ≤ q * R)
    (n k d : ℕ) (hkn : k ≤ n) :
    (n.choose k : ℝ) * Rc ^ k * (k.factorial : ℝ) ^ 2 * majorant R d (n - k)
      ≤ q ^ k * majorant R d n := by
  have hp : Rc ^ k ≤ (q * R) ^ k := pow_le_pow_left₀ hRc hscale k
  have hterm := majorant_product_term_le R hR n k 0 d hkn
  simp only [zero_add] at hterm
  have hscaled := mul_le_mul_of_nonneg_left hterm (pow_nonneg hq k)
  calc
    _ ≤ (n.choose k : ℝ) * (q * R) ^ k * (k.factorial : ℝ) ^ 2 *
        majorant R d (n - k) := by
      gcongr
      exact majorant_nonneg R hR d (n - k)
    _ = q ^ k * ((n.choose k : ℝ) * majorant R 0 k * majorant R d (n - k)) := by
      simp only [majorant, Nat.add_zero, mul_pow]
      ring
    _ ≤ _ := hscaled

/--
The triangular inverse rule with an explicit sufficient radius, uniform in the
derivative order and in the input shift. The recurrence sums the indices `1,…,n`
as `k + 1` for `k ∈ range n`. No sign assumption on `F` or `Z` is needed.
-/
theorem triangular_inverse_majorant (A Rc R : ℝ)
    (hA : 1 ≤ A) (hRc : 0 ≤ Rc) (hlarge : 2 * A * (Rc + 1) ≤ R)
    (d : ℕ) (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant R d n)
    (hZ : ∀ n, Z n ≤ A * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant R (d + 1) n := by
  have hA0 : 0 ≤ A := by linarith
  have hARc : 0 ≤ A * Rc := mul_nonneg hA0 hRc
  have hR : 0 < R := by nlinarith
  have hq0 : 0 ≤ Rc / R := div_nonneg hRc hR.le
  have hqhalf : Rc / R ≤ 1 / 2 := by
    apply (div_le_iff₀ hR).2
    nlinarith [mul_nonneg (show 0 ≤ A - 1 by linarith) hRc]
  have hscale : Rc ≤ (Rc / R) * R := by rw [div_mul_cancel₀ _ hR.ne']
  have hbudget : A / R + 2 * A * (Rc / R) ≤ 1 := by
    calc
      _ = (A + 2 * A * Rc) / R := by ring
      _ ≤ 1 := (div_le_one hR).2 (by nlinarith)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw : 0 ≤ majorant R (d + 1) n := majorant_nonneg R hR.le _ _
      have hshift : majorant R d n ≤ majorant R (d + 1) n / R := by
        apply (le_div_iff₀ hR).2
        simpa only [mul_comm] using majorant_shift_le R hR.le d n
      have hs : (∑ k ∈ range n,
          (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
            Z (n - (k + 1)))
          ≤ (2 * (Rc / R)) * majorant R (d + 1) n := by
        calc
          _ ≤ ∑ k ∈ range n, (Rc / R) ^ (k + 1) * majorant R (d + 1) n := by
            apply sum_le_sum
            intro k hk
            have hklt : k < n := mem_range.mp hk
            have hlow : n - (k + 1) < n := by omega
            have hc : 0 ≤ (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) *
                ((k + 1).factorial : ℝ) ^ 2 := by positivity
            exact (mul_le_mul_of_nonneg_left (ih _ hlow) hc).trans
              (majorant_coefficient_term R Rc (Rc / R) hR.le hRc hq0 hscale
                n (k + 1) (d + 1) (by omega))
          _ = (∑ k ∈ range n, (Rc / R) ^ (k + 1)) * majorant R (d + 1) n :=
            (sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (geometric_tail_le_two_mul (Rc / R) hq0 hqhalf n) hw
      calc
        Z n ≤ A * (F n + ∑ k ∈ range n,
            (n.choose (k + 1) : ℝ) * Rc ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
              Z (n - (k + 1))) := hZ n
        _ ≤ A * (majorant R (d + 1) n / R +
            (2 * (Rc / R)) * majorant R (d + 1) n) :=
          mul_le_mul_of_nonneg_left (add_le_add ((hF n).trans hshift) hs) hA0
        _ = (A / R + 2 * A * (Rc / R)) * majorant R (d + 1) n := by ring
        _ ≤ majorant R (d + 1) n := mul_le_of_le_one_left hw hbudget

/-- For coefficient and inverse size `P^c`, the single polynomial radius `P^(2c+2)` suffices. -/
theorem triangular_inverse_polynomial_radius (P : ℝ) (hP : 2 ≤ P) (c d : ℕ)
    (F Z : ℕ → ℝ)
    (hF : ∀ n, F n ≤ majorant (P ^ (2 * c + 2)) d n)
    (hZ : ∀ n, Z n ≤ P ^ c * (F n + ∑ k ∈ range n,
      (n.choose (k + 1) : ℝ) * (P ^ c) ^ (k + 1) * ((k + 1).factorial : ℝ) ^ 2 *
        Z (n - (k + 1)))) :
    ∀ n, Z n ≤ majorant (P ^ (2 * c + 2)) (d + 1) n := by
  have hPc : 1 ≤ P ^ c := one_le_pow₀ (by linarith)
  have hPc0 : 0 ≤ P ^ c := by linarith
  have hP2 : 4 ≤ P ^ 2 := by nlinarith [sq_nonneg (P - 2)]
  have heq : P ^ (2 * c + 2) = (P ^ c) ^ 2 * P ^ 2 := by
    rw [show 2 * c + 2 = c * 2 + 2 by omega, pow_add, pow_mul]
  have hlarge : 2 * P ^ c * (P ^ c + 1) ≤ P ^ (2 * c + 2) := by
    calc
      _ ≤ (P ^ c) ^ 2 * 4 := by nlinarith
      _ ≤ (P ^ c) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
      _ = _ := heq.symm
  exact triangular_inverse_majorant (P ^ c) (P ^ c) (P ^ (2 * c + 2))
    hPc hPc0 hlarge d F Z hF hZ

/-- The shifted product rule applies directly to arbitrary real sequences bounded in absolute value. -/
theorem sequence_product_majorant (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (d₁ d₂ : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ A * majorant R d₁ n)
    (hg : ∀ n, |g n| ≤ B * majorant R d₂ n) (n : ℕ) :
    |∑ k ∈ range (n + 1), (n.choose k : ℝ) * f k * g (n - k)|
      ≤ 3 * A * B * majorant R (d₁ + d₂) n := by
  calc
    _ ≤ ∑ k ∈ range (n + 1), |(n.choose k : ℝ) * f k * g (n - k)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), A * B *
        ((n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by
      apply sum_le_sum
      intro k _hk
      have hfg : |f k| * |g (n - k)| ≤
          (A * majorant R d₁ k) * (B * majorant R d₂ (n - k)) :=
        mul_le_mul (hf k) (hg (n - k)) (abs_nonneg _)
          (mul_nonneg hA (majorant_nonneg R hR d₁ k))
      have hc : (0 : ℝ) ≤ n.choose k := by positivity
      have h := mul_le_mul_of_nonneg_left hfg hc
      simpa only [abs_mul, abs_of_nonneg hc, mul_assoc, mul_left_comm, mul_comm] using h
    _ = A * B * (∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * majorant R d₁ k * majorant R d₂ (n - k)) := by rw [mul_sum]
    _ ≤ A * B * (3 * majorant R (d₁ + d₂) n) :=
      mul_le_mul_of_nonneg_left (majorant_convolution R hR n d₁ d₂) (mul_nonneg hA hB)
    _ = _ := by ring

end EulerGevrey

end

section

namespace EulerSmoothUniformLimit

open Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]

/-- An infinite compatible derivative tower is smooth at every level. -/
theorem contDiff_of_derivative_tower (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hJ : ∀ n x, HasFDerivAt (J n) (L n (J (n + 1) x)) x) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  have hfinite : ∀ k : ℕ, ∀ n, ContDiff ℝ k (J n) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun x => (hJ n x).continuousAt))
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hJ n x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (J n) = fun x => L n (J (n + 1) x) :=
        funext (fun x => (hJ n x).fderiv)
      rw [he]
      exact (L n).contDiff.comp (ih (n + 1))
  intro n
  exact contDiff_infty.mpr (fun k => hfinite k n)

/-- Uniform limits of a compatible smooth derivative tower are again smooth.
This is the completion step for Sobolev mollifications. -/
theorem contDiff_of_uniform_derivative_limits
    (f : ∀ n, ℕ → E → F n) (J : ∀ n, E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hlim : ∀ n, TendstoUniformly (f n) (J n) atTop) :
    ∀ n, ContDiff ℝ ∞ (J n) := by
  apply contDiff_of_derivative_tower J L
  intro n x
  have hd := (L n).uniformContinuous.comp_tendstoUniformly (hlim (n + 1))
  exact hasFDerivAt_of_tendstoUniformly hd (hf n) (fun y => (hlim n).tendsto_at y) x

/-- Completeness constructs every limit in a uniformly Cauchy derivative tower;
the limit and all of its compatible derivatives are smooth. -/
theorem exists_smooth_limit_of_uniform_cauchy_tower [∀ n, CompleteSpace (F n)]
    (f : ∀ n, ℕ → E → F n)
    (L : ∀ n, F (n + 1) →L[ℝ] (E →L[ℝ] F n))
    (hf : ∀ n k x, HasFDerivAt (f n k) (L n (f (n + 1) k x)) x)
    (hC : ∀ n, UniformCauchySeqOn (f n) atTop Set.univ) :
    ∃ J : ∀ n, E → F n,
      (∀ n, TendstoUniformly (f n) (J n) atTop) ∧ (∀ n, ContDiff ℝ ∞ (J n)) := by
  have hp : ∀ n x, ∃ v : F n, Tendsto (fun k => f n k x) atTop (nhds v) := by
    intro n x
    exact cauchy_map_iff_exists_tendsto.mp ((hC n).cauchy_map (Set.mem_univ x))
  choose J hJ using hp
  have hlim : ∀ n, TendstoUniformly (f n) (J n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (hC n).tendstoUniformlyOn_of_tendsto (fun x _ => hJ n x)
  exact ⟨J, hlim, contDiff_of_uniform_derivative_limits f J L hf hlim⟩

end EulerSmoothUniformLimit

end

section

/-!
Exact weight identities used in the proposed packet's Gevrey estimates (18)--(19).
These lemmas do not assert the nonlinear PDE estimates or an Euler blowup theorem.
-/

namespace EulerPacketWeights

/-- Factorial weight at radius `ρ` for the Gevrey-two energy series. -/
noncomputable def weight (ρ : ℝ) (n : ℕ) : ℝ :=
  ρ ^ n / (n.factorial : ℝ) ^ 2

theorem weight_pos {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : 0 < weight ρ n := by
  unfold weight
  positivity

theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

/-- The binomial gain that compensates a Gevrey-2 derivative in a non-top commutator. -/
theorem choose_add_lower (j l : ℕ) (hl : 1 ≤ l) :
    j + 1 ≤ (j + l).choose l := by
  rw [← Nat.choose_symm_add]
  have h := Nat.choose_le_choose j (Nat.add_le_add_left hl j)
  simpa only [Nat.choose_succ_self_right] using h

/-- Equation (18)'s source weight ratio, written without truncated natural subtraction. -/
theorem shifted_source_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      1 / ((j + l + 1).choose l : ℝ) := by
  have hl₀ : l ≤ j + l := Nat.le_add_left l j
  have hl₁ : l ≤ j + l + 1 := hl₀.trans (Nat.le_add_right _ _)
  have hsub : j + l + 1 - l = j + 1 := by omega
  rw [Nat.cast_choose ℝ hl₀, Nat.cast_choose ℝ hl₁]
  simp only [Nat.add_sub_cancel_right, hsub]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- Equation (19)'s external-commutator ratio. -/
theorem external_commutator_ratio (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) =
      ρ⁻¹ * ((j + 1 : ℕ) : ℝ) / ((j + l).choose l : ℝ) := by
  rw [Nat.cast_choose ℝ (Nat.le_add_left l j)]
  simp only [Nat.add_sub_cancel_right]
  unfold weight
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_add, pow_one]
  field_simp [factorial_cast_ne_zero, hρ]

/-- The source ratio in (18) is at most one, uniformly in the derivative indices. -/
theorem shifted_source_ratio_le_one (ρ : ℝ) (hρ : ρ ≠ 0) (j l : ℕ) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ 1 := by
  rw [shifted_source_ratio ρ hρ j l]
  have hn : 0 < (j + l + 1).choose l :=
    Nat.choose_pos ((Nat.le_add_left l j).trans (Nat.le_add_right _ _))
  have hp : (0 : ℝ) < ((j + l + 1).choose l : ℝ) := by exact_mod_cast hn
  apply (div_le_one hp).2
  exact_mod_cast hn

/-- The non-top ratio in (19) is at most the inverse radius, with no order loss. -/
theorem external_commutator_ratio_le (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (hl : 1 ≤ l) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) /
        (weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1)) ≤ ρ⁻¹ := by
  rw [external_commutator_ratio ρ hρ.ne' j l]
  have hp : (0 : ℝ) < ((j + l).choose l : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left l j)
  have hb : ((j + 1 : ℕ) : ℝ) ≤ ((j + l).choose l : ℝ) := by
    exact_mod_cast choose_add_lower j l hl
  exact (div_le_iff₀ hp).2 (mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hρ.le))

end EulerPacketWeights

end

section

/-!
The Hilbert-space inverse used for the packet pressure equation.
Invertibility is constructed from Lax--Milgram, not assumed.  The coercivity
hypothesis is an explicit quadratic inequality on the given bounded operator.
This does not assert the Fourier or Sobolev realization of the pressure space.
-/


namespace EulerCoerciveProjection

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded bilinear form associated with an operator and the real inner product. -/
def operatorBilinear (T : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp T

lemma operatorBilinear_coercive (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    IsCoercive (operatorBilinear T) := by
  refine ⟨c, hc, fun x => ?_⟩
  change c * ‖x‖ * ‖x‖ ≤ ⟪T x, x⟫_ℝ
  simpa only [pow_two, mul_assoc] using hT x

section Complete

variable [CompleteSpace E]

/-- Lax--Milgram constructs an equivalence from the operator's coercivity. -/
def coerciveEquiv (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E ≃L[ℝ] E :=
  (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin

@[simp]
theorem coerciveEquiv_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveEquiv T c hc hT x = T x := by
  apply ext_inner_right ℝ
  intro y
  exact (operatorBilinear_coercive T c hc hT).continuousLinearEquivOfBilin_apply x y

/-- The inverse operator constructed from the coercive Lax–Milgram equivalence. -/
def coerciveInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) : E →L[ℝ] E :=
  (coerciveEquiv T c hc hT).symm.toContinuousLinearMap

@[simp]
theorem operator_inverse_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    T (coerciveInverse T c hc hT y) = y := by
  change T ((coerciveEquiv T c hc hT).symm y) = y
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).apply_symm_apply y

@[simp]
theorem inverse_operator_apply (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (x : E) :
    coerciveInverse T c hc hT (T x) = x := by
  change (coerciveEquiv T c hc hT).symm (T x) = x
  rw [← coerciveEquiv_apply T c hc hT]
  exact (coerciveEquiv T c hc hT).symm_apply_apply x

theorem coerciveInverse_apply_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (y : E) :
    ‖coerciveInverse T c hc hT y‖ ≤ c⁻¹ * ‖y‖ := by
  let x := coerciveInverse T c hc hT y
  change ‖x‖ ≤ c⁻¹ * ‖y‖
  by_cases hx : x = 0
  · simp only [hx, norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : c * ‖x‖ ≤ ‖y‖ := by
    apply (mul_le_mul_iff_left₀ hn).mp
    calc
      c * ‖x‖ * ‖x‖ = c * ‖x‖ ^ 2 := by ring
      _ ≤ ⟪T x, x⟫_ℝ := hT x
      _ = ⟪y, x⟫_ℝ := by rw [show T x = y from operator_inverse_apply T c hc hT y]
      _ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
  have := (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hb)
  simpa only [div_eq_mul_inv, mul_comm] using this

theorem coerciveInverse_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT‖ ≤ c⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le)
  exact coerciveInverse_apply_norm_le T c hc hT

/-- The exact resolvent identity for the inverses constructed by Lax--Milgram. -/
theorem coerciveInverse_resolvent (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    coerciveInverse T c hc hT - coerciveInverse U d hd hU =
      (coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU)) := by
  ext y
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, sub_apply,
    ContinuousLinearMap.comp_apply, map_sub, operator_inverse_apply]

theorem coerciveInverse_norm_sub_le (T U : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ)
    (hU : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪U x, x⟫_ℝ) :
    ‖coerciveInverse T c hc hT - coerciveInverse U d hd hU‖ ≤
      c⁻¹ * d⁻¹ * ‖U - T‖ := by
  rw [coerciveInverse_resolvent T U c d hc hd hT hU]
  calc
    ‖(coerciveInverse T c hc hT).comp
        ((U - T).comp (coerciveInverse U d hd hU))‖ ≤
        ‖coerciveInverse T c hc hT‖ *
          ‖(U - T).comp (coerciveInverse U d hd hU)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖coerciveInverse T c hc hT‖ *
        (‖U - T‖ * ‖coerciveInverse U d hd hU‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ c⁻¹ * (‖U - T‖ * d⁻¹) :=
      mul_le_mul (coerciveInverse_norm_le T c hc hT)
        (mul_le_mul_of_nonneg_left (coerciveInverse_norm_le U d hd hU) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.2 hc.le)
    _ = c⁻¹ * d⁻¹ * ‖U - T‖ := by ring

end Complete

section Subspace

variable (S : Submodule ℝ E) [CompleteSpace S]

/-- Orthogonal projection of the given ambient operator, restricted to the subspace. -/
def projectedOperator (G : E →L[ℝ] E) : S →L[ℝ] S :=
  S.orthogonalProjectionOnto.comp (G.comp S.subtypeL)

theorem projectedOperator_inner (G : E →L[ℝ] E) (x y : S) :
    ⟪projectedOperator S G x, y⟫_ℝ = ⟪G (x : E), (y : E)⟫_ℝ := by
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right y (G x)

theorem projectedOperator_coercive (G : E →L[ℝ] E) (c : ℝ)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (x : S) :
    c * ‖x‖ ^ 2 ≤ ⟪projectedOperator S G x, x⟫_ℝ := by
  rw [projectedOperator_inner]
  exact hG x

/-- The projected-pressure inverse, constructed by applying Lax--Milgram on `S`. -/
def projectedInverse (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : S →L[ℝ] S :=
  coerciveInverse (projectedOperator S G) c hc (projectedOperator_coercive S G c hG)

@[simp]
theorem projectedOperator_inverse_apply (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : S) :
    projectedOperator S G (projectedInverse S G c hc hG f) = f :=
  operator_inverse_apply (projectedOperator S G) c hc (projectedOperator_coercive S G c hG) f

theorem projectedInverse_norm_le (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) :
    ‖projectedInverse S G c hc hG‖ ≤ c⁻¹ :=
  coerciveInverse_norm_le (projectedOperator S G) c hc (projectedOperator_coercive S G c hG)

@[simp]
theorem projectedOperator_sub (G H : E →L[ℝ] E) :
    projectedOperator S (G - H) = projectedOperator S G - projectedOperator S H := by
  ext x
  simp [projectedOperator]

theorem projectedOperator_norm_le (G : E →L[ℝ] E) :
    ‖projectedOperator S G‖ ≤ ‖G‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖projectedOperator S G x‖ ≤ ‖G (x : E)‖ :=
      S.norm_orthogonalProjectionOnto_apply_le (G x)
    _ ≤ ‖G‖ * ‖x‖ := G.le_opNorm x

theorem projectedInverse_norm_sub_le (G H : E →L[ℝ] E) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ)
    (hH : ∀ x, d * ‖x‖ ^ 2 ≤ ⟪H x, x⟫_ℝ) :
    ‖projectedInverse S G c hc hG - projectedInverse S H d hd hH‖ ≤
      c⁻¹ * d⁻¹ * ‖H - G‖ := by
  calc
    ‖projectedInverse S G c hc hG - projectedInverse S H d hd hH‖ ≤
        c⁻¹ * d⁻¹ * ‖projectedOperator S H - projectedOperator S G‖ :=
      coerciveInverse_norm_sub_le (projectedOperator S G) (projectedOperator S H)
        c d hc hd (projectedOperator_coercive S G c hG)
        (projectedOperator_coercive S H d hH)
    _ = c⁻¹ * d⁻¹ * ‖projectedOperator S (H - G)‖ := by rw [projectedOperator_sub]
    _ ≤ c⁻¹ * d⁻¹ * ‖H - G‖ :=
      mul_le_mul_of_nonneg_left (projectedOperator_norm_le S (H - G))
        (mul_nonneg (inv_nonneg.2 hc.le) (inv_nonneg.2 hd.le))

/-- Solves the projected equation with an ambient forcing vector. -/
def pressureSolver (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) : E →L[ℝ] S :=
  (projectedInverse S G c hc hG).comp S.orthogonalProjectionOnto

theorem pressureSolver_equation (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : E)) =
      S.orthogonalProjectionOnto f :=
  projectedOperator_inverse_apply S G c hc hG (S.orthogonalProjectionOnto f)

theorem pressureSolver_apply_norm_le (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖f‖ := by
  calc
    ‖pressureSolver S G c hc hG f‖ ≤ c⁻¹ * ‖S.orthogonalProjectionOnto f‖ :=
      coerciveInverse_apply_norm_le (projectedOperator S G) c hc
        (projectedOperator_coercive S G c hG) (S.orthogonalProjectionOnto f)
    _ ≤ c⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (S.norm_orthogonalProjectionOnto_apply_le f)
        (inv_nonneg.2 hc.le)

/-- Existence and uniqueness of the pressure variable in the closed subspace. -/
theorem existsUnique_projected_solution (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) (f : E) :
    ∃! p : S, S.orthogonalProjectionOnto (G (p : E)) =
      S.orthogonalProjectionOnto f := by
  refine ⟨pressureSolver S G c hc hG f, pressureSolver_equation S G c hc hG f, ?_⟩
  intro p hp
  apply (coerciveEquiv (projectedOperator S G) c hc
    (projectedOperator_coercive S G c hG)).injective
  simp only [coerciveEquiv_apply]
  change S.orthogonalProjectionOnto (G (p : E)) =
    S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : E))
  rw [hp, pressureSolver_equation]

end Subspace

/-- Closedness supplies completeness; no inverse or existence hypothesis is assumed. -/
theorem closed_subspace_inverse [CompleteSpace E] (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) (G : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪G x, x⟫_ℝ) :
    ∃ I : S →L[ℝ] S,
      (∀ f y : S, ⟪G (I f : E), (y : E)⟫_ℝ = ⟪(f : E), (y : E)⟫_ℝ) ∧
      ‖I‖ ≤ c⁻¹ := by
  let : CompleteSpace S := hS.completeSpace_coe
  refine ⟨projectedInverse S G c hc hG, ?_, projectedInverse_norm_le S G c hc hG⟩
  intro f y
  rw [← projectedOperator_inner S G (projectedInverse S G c hc hG f) y,
    projectedOperator_inverse_apply]
  rfl

end EulerCoerciveProjection

end

section

namespace EulerInverseRegularity

open EulerCoerciveProjection InnerProductSpace ContinuousLinearMap
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The bounded translation difference quotient with increment h. -/
def differenceQuotient (τ : E →L[ℝ] E) (h : ℝ) : E →L[ℝ] E :=
  h⁻¹ • (τ - ContinuousLinearMap.id ℝ E)

/-- The operator commutator D T minus T D. -/
def commutator (D T : E →L[ℝ] E) : E →L[ℝ] E := D.comp T - T.comp D

/-- Repeated commutation with an operator, defined by its actual algebraic formula. -/
def iteratedRingCommutator {R : Type*} [Ring R] (D T : R) : ℕ → R
  | 0 => T
  | n + 1 => D * iteratedRingCommutator D T n - iteratedRingCommutator D T n * D

theorem mul_iteratedRingCommutator {R : Type*} [Ring R] (D T : R) (n : ℕ) :
    D * iteratedRingCommutator D T n =
      iteratedRingCommutator D T n * D + iteratedRingCommutator D T (n + 1) := by
  simp only [iteratedRingCommutator]
  abel

/-- The complete noncommutative Leibniz formula, proved from the commutator definition. -/
theorem iterated_operator_leibniz {R : Type*} [Ring R] (D T : R) (n : ℕ) :
    D ^ n * T = ∑ l ∈ Finset.range (n + 1),
      n.choose l • (iteratedRingCommutator D T l * D ^ (n - l)) := by
  induction n with
  | zero => simp [iteratedRingCommutator]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum,
      Finset.sum_choose_succ_nsmul (fun l r => iteratedRingCommutator D T l * D ^ r) n,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hsub : n + 1 - l = (n - l) + 1 := by omega
    calc
      D * (n.choose l • (iteratedRingCommutator D T l * D ^ (n - l))) =
          n.choose l • ((D * iteratedRingCommutator D T l) * D ^ (n - l)) := by
        rw [mul_smul_comm, mul_assoc]
      _ = n.choose l • ((iteratedRingCommutator D T l * D +
          iteratedRingCommutator D T (l + 1)) * D ^ (n - l)) := by
        rw [mul_iteratedRingCommutator]
      _ = n.choose l • (iteratedRingCommutator D T l * D ^ (n + 1 - l)) +
          n.choose l • (iteratedRingCommutator D T (l + 1) * D ^ (n - l)) := by
        rw [add_mul, nsmul_add, hsub, pow_succ', mul_assoc]

theorem inverse_commutator_apply (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    D (coerciveInverse T c hc hT f) =
      coerciveInverse T c hc hT
        (D f - commutator D T (coerciveInverse T c hc hT f)) := by
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, operator_inverse_apply, commutator,
    sub_apply, ContinuousLinearMap.comp_apply]
  abel

theorem inverse_commutator_norm_le (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    ‖D (coerciveInverse T c hc hT f)‖ ≤
      c⁻¹ * (‖D f‖ + ‖commutator D T (coerciveInverse T c hc hT f)‖) := by
  rw [inverse_commutator_apply T D c hc hT f]
  exact (coerciveInverse_apply_norm_le T c hc hT _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.2 hc.le))

/-- The full differentiated inverse recurrence, derived from the operator equation. -/
theorem inverse_iterated_commutator_apply (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) (n : ℕ) :
    (D ^ (n + 1)) (coerciveInverse T c hc hT f) =
      coerciveInverse T c hc hT
        ((D ^ (n + 1)) f - ∑ l ∈ Finset.range (n + 1),
          (n + 1).choose (l + 1) •
            (iteratedRingCommutator D T (l + 1)
              ((D ^ (n - l)) (coerciveInverse T c hc hT f)))) := by
  have hprod := congrArg (fun A : E →L[ℝ] E => A (coerciveInverse T c hc hT f))
    (iterated_operator_leibniz D T (n + 1))
  simp only [mul_apply_eq_comp, operator_inverse_apply, sum_apply, smul_apply] at hprod
  rw [Finset.sum_range_succ'] at hprod
  simp only [Nat.choose_zero_right, iteratedRingCommutator, Nat.sub_zero,
    one_smul, Nat.add_sub_add_right] at hprod
  apply (coerciveEquiv T c hc hT).injective
  simp only [coerciveEquiv_apply, operator_inverse_apply]
  apply eq_sub_of_add_eq
  exact (add_comm _ _).trans hprod.symm

/-- The quantitative all-order recurrence follows from the exact commutator identity. -/
theorem inverse_iterated_commutator_norm_le (T D : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) (n : ℕ) :
    ‖(D ^ (n + 1)) (coerciveInverse T c hc hT f)‖ ≤ c⁻¹ *
      (‖(D ^ (n + 1)) f‖ + ∑ l ∈ Finset.range (n + 1),
        ((n + 1).choose (l + 1) : ℝ) * ‖iteratedRingCommutator D T (l + 1)‖ *
          ‖(D ^ (n - l)) (coerciveInverse T c hc hT f)‖) := by
  have hs : ‖∑ l ∈ Finset.range (n + 1), (n + 1).choose (l + 1) •
        (iteratedRingCommutator D T (l + 1)
          ((D ^ (n - l)) (coerciveInverse T c hc hT f)))‖ ≤
      ∑ l ∈ Finset.range (n + 1),
        ((n + 1).choose (l + 1) : ℝ) * ‖iteratedRingCommutator D T (l + 1)‖ *
          ‖(D ^ (n - l)) (coerciveInverse T c hc hT f)‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      ((iteratedRingCommutator D T (l + 1)).le_opNorm
        ((D ^ (n - l)) (coerciveInverse T c hc hT f)))
      (Nat.cast_nonneg ((n + 1).choose (l + 1)))
  rw [inverse_iterated_commutator_apply T D c hc hT f n]
  refine (coerciveInverse_apply_norm_le T c hc hT _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hc.le)
  exact (norm_sub_le _ _).trans (add_le_add_right hs _)

omit [CompleteSpace E] in
theorem differenceQuotient_commutator (τ T : E →L[ℝ] E) (h : ℝ) :
    commutator (differenceQuotient τ h) T = h⁻¹ • commutator τ T := by
  ext x
  simp only [commutator, differenceQuotient, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul]
  simp only [smul_sub]
  abel

/-- The spatial difference-quotient estimate, before any passage to weak derivatives. -/
theorem inverse_differenceQuotient_norm_le (T τ : E →L[ℝ] E) (h c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) (f : E) :
    ‖differenceQuotient τ h (coerciveInverse T c hc hT f)‖ ≤
      c⁻¹ * (‖differenceQuotient τ h f‖ +
        ‖h⁻¹ • commutator τ T (coerciveInverse T c hc hT f)‖) := by
  simpa only [differenceQuotient_commutator, smul_apply] using
    inverse_commutator_norm_le T (differenceQuotient τ h) c hc hT f

theorem coerciveInverse_eq_mapInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = T.inverse := by
  have he : (coerciveEquiv T c hc hT : E →L[ℝ] E) = T := by
    ext x
    exact coerciveEquiv_apply T c hc hT x
  calc
    coerciveInverse T c hc hT =
        (coerciveEquiv T c hc hT).symm.toContinuousLinearMap := rfl
    _ = (coerciveEquiv T c hc hT : E →L[ℝ] E).inverse :=
      (ContinuousLinearMap.inverse_equiv (coerciveEquiv T c hc hT)).symm
    _ = T.inverse := congrArg ContinuousLinearMap.inverse he

theorem coerciveInverse_eq_ringInverse (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ) :
    coerciveInverse T c hc hT = Ring.inverse T := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact coerciveInverse_eq_mapInverse T c hc hT

/-- A `Cⁿ` family of coercive operators has a `Cⁿ` family of the constructed inverses. -/
theorem contDiff_coerciveInverse (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n T) :
    ContDiff ℝ n (fun t => coerciveInverse (T t) c hc (hT t)) := by
  have he : ∀ t, (coerciveEquiv (T t) c hc (hT t) : E →L[ℝ] E) = T t := by
    intro t
    ext x
    exact coerciveEquiv_apply (T t) c hc (hT t) x
  have hfun : (fun t => coerciveInverse (T t) c hc (hT t)) =
      fun t => (T t).inverse := by
    funext t
    exact coerciveInverse_eq_mapInverse (T t) c hc (hT t)
  rw [hfun, contDiff_iff_contDiffAt]
  intro t
  have hinv : ContDiffAt ℝ n ContinuousLinearMap.inverse (T t) := by
    rw [← he t]
    exact contDiffAt_map_inverse (coerciveEquiv (T t) c hc (hT t))
  exact hinv.comp t hreg.contDiffAt

/-- The time derivative of the constructed inverse is `-I T' I`. -/
theorem hasDerivAt_coerciveInverse (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (t : ℝ) (T₁ : E →L[ℝ] E) (hder : HasDerivAt T T₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s))
      (-(coerciveInverse (T t) c hc (hT t)).comp
        (T₁.comp (coerciveInverse (T t) c hc (hT t)))) t := by
  let u : (E →L[ℝ] E)ˣ := (coerciveEquiv (T t) c hc (hT t)).toUnit
  have hu : (u : E →L[ℝ] E) = T t := by
    ext x
    exact coerciveEquiv_apply (T t) c hc (hT t) x
  have hui : (↑u⁻¹ : E →L[ℝ] E) = coerciveInverse (T t) c hc (hT t) := rfl
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  have hcomp := hi.comp_hasDerivAt t hder
  have hfun : (fun s => coerciveInverse (T s) c hc (hT s)) = Ring.inverse ∘ T := by
    funext s
    exact coerciveInverse_eq_ringInverse (T s) c hc (hT s)
  rw [hfun]
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hui,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcomp

theorem hasDerivAt_coerciveSolution (T : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hT : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪T t x, x⟫_ℝ)
    (f : ℝ → E) (t : ℝ) (T₁ : E →L[ℝ] E) (f₁ : E)
    (hder : HasDerivAt T T₁ t) (hf : HasDerivAt f f₁ t) :
    HasDerivAt (fun s => coerciveInverse (T s) c hc (hT s) (f s))
      (coerciveInverse (T t) c hc (hT t)
        (f₁ - T₁ (coerciveInverse (T t) c hc (hT t) (f t)))) t := by
  convert (hasDerivAt_coerciveInverse T c hc hT t T₁ hder).clm_apply hf using 1
  simp only [neg_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

section Projected

variable (S : Submodule ℝ E) [CompleteSpace S]

omit [CompleteSpace E] in
theorem contDiff_projectedOperator (G : ℝ → E →L[ℝ] E) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n G) :
    ContDiff ℝ n (fun t => projectedOperator S (G t)) := by
  exact contDiff_const.clm_comp (hreg.clm_comp contDiff_const)

omit [CompleteSpace E] in
theorem hasDerivAt_projectedOperator (G : ℝ → E →L[ℝ] E) (t : ℝ)
    (G₁ : E →L[ℝ] E) (hder : HasDerivAt G G₁ t) :
    HasDerivAt (fun s => projectedOperator S (G s)) (projectedOperator S G₁) t := by
  simpa only [zero_comp, comp_zero, zero_add, add_zero, projectedOperator, comp_assoc] using
    (hasDerivAt_const t S.orthogonalProjectionOnto).clm_comp
      (hder.clm_comp (hasDerivAt_const t S.subtypeL))

omit [CompleteSpace E] in
theorem contDiff_projectedInverse (G : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪G t x, x⟫_ℝ) {n : ℕ∞ω}
    (hreg : ContDiff ℝ n G) :
    ContDiff ℝ n (fun t => projectedInverse S (G t) c hc (hG t)) :=
  contDiff_coerciveInverse (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t))
    (contDiff_projectedOperator S G hreg)

omit [CompleteSpace E] in
theorem hasDerivAt_projectedInverse (G : ℝ → E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : ∀ t x, c * ‖x‖ ^ 2 ≤ ⟪G t x, x⟫_ℝ)
    (t : ℝ) (G₁ : E →L[ℝ] E) (hder : HasDerivAt G G₁ t) :
    HasDerivAt (fun s => projectedInverse S (G s) c hc (hG s))
      (-(projectedInverse S (G t) c hc (hG t)).comp
        ((projectedOperator S G₁).comp (projectedInverse S (G t) c hc (hG t)))) t :=
  hasDerivAt_coerciveInverse (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t)) t
    (projectedOperator S G₁) (hasDerivAt_projectedOperator S G t G₁ hder)

end Projected

end EulerInverseRegularity

end

section

/-!
An actual L² realization of the lifted pressure-gradient space on R³ × (R / period Z).
The generating vectors are L² representatives of Dφ, for smooth compactly supported
scalar test functions φ.  Smoothness is expressed through local lifts to R³ × R.
The angular measure here has total mass `period`; renormalizing it changes only a
fixed scalar in the L² norm and not the gradient subspace or projection.
-/


namespace EulerLiftedGradientSpace

open MeasureTheory InnerProductSpace
open scoped ContDiff ENNReal Topology

/-- Three dimensional real Euclidean vectors. -/
abbrev Vector3 := EuclideanSpace ℝ (Fin 3)
/-- The spatial cylinder with one periodic angle coordinate. -/
abbrev LiftDomain (period : ℝ) := Vector3 × AddCircle period
/-- The four dimensional real covering space of the cylinder. -/
abbrev LiftTangent := Vector3 × ℝ

variable (period : ℝ) [Fact (0 < period)]

/-- Product Lebesgue and angle Haar measure on the cylinder. -/
def liftMeasure : Measure (LiftDomain period) :=
  (volume : Measure Vector3).prod (volume : Measure (AddCircle period))

instance liftMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (liftMeasure period) := by
  unfold liftMeasure
  infer_instance

/-- The genuine Hilbert space of square integrable vector fields on the cylinder. -/
abbrev LiftL2 := Lp Vector3 2 (liftMeasure period)

/-- The scalar field pulled back to covering coordinates centered at x. -/
def localLift (φ : LiftDomain period → ℝ) (x : LiftDomain period) : LiftTangent → ℝ :=
  fun h => φ (x.1 + h.1, x.2 + (h.2 : AddCircle period))

/-- The quotient covering map from the real tangent space to the cylinder. -/
def coveringMap : LiftTangent → LiftDomain period :=
  fun z => (z.1, (z.2 : AddCircle period))

omit [Fact (0 < period)] in
theorem coveringMap_isOpenQuotient : IsOpenQuotientMap (coveringMap period) :=
  IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk

omit [Fact (0 < period)] in
theorem localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    localLift period φ (coveringMap period z) = fun h => localLift period φ 0 (z + h) := by
  funext h
  simp [localLift, coveringMap]

omit [Fact (0 < period)] in
theorem fderiv_localLift_cover (φ : LiftDomain period → ℝ) (z : LiftTangent) :
    fderiv ℝ (localLift period φ (coveringMap period z)) 0 =
      fderiv ℝ (localLift period φ 0) z := by
  rw [localLift_cover, fderiv_comp_add_left, add_zero]

/-- The actual differential expression `κ ∇_y φ + m ∂_θ φ`. -/
def liftedGradient (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  WithLp.toLp 2 fun i =>
    κ * fderiv ℝ (localLift period φ x) 0 (EuclideanSpace.single i 1, 0) +
      m i * fderiv ℝ (localLift period φ x) 0 (0, 1)

omit [Fact (0 < period)] in
theorem liftedGradient_continuous (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    Continuous (liftedGradient period κ m φ) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have hd : Continuous (fderiv ℝ (localLift period φ 0)) :=
    (hφ 0).continuous_fderiv (by simp)
  have hcomp : liftedGradient period κ m φ ∘ coveringMap period =
      fun z => WithLp.toLp 2 fun i =>
        κ * fderiv ℝ (localLift period φ 0) z (EuclideanSpace.single i 1, 0) +
          m i * fderiv ℝ (localLift period φ 0) z (0, 1) := by
    funext z
    simp only [Function.comp_def, liftedGradient, fderiv_localLift_cover]
  rw [hcomp]
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul (hd.clm_apply continuous_const)).add
    (continuous_const.mul (hd.clm_apply continuous_const))

omit [Fact (0 < period)] in
theorem liftedGradient_zero_of_notMem_tsupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) (hx : x ∉ tsupport φ) :
    liftedGradient period κ m φ x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localLift period φ x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : ℝ)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  have hd : fderiv ℝ (localLift period φ x) 0 = 0 := by
    rw [hz.fderiv_eq]
    simp
  simp [liftedGradient, hd]
  rfl

omit [Fact (0 < period)] in
theorem liftedGradient_hasCompactSupport (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (liftedGradient period κ m φ) :=
  HasCompactSupport.intro hφ (liftedGradient_zero_of_notMem_tsupport period κ m φ)

/-- Every smooth compact test has an actual L² lifted gradient. -/
theorem liftedGradient_memLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    MemLp (liftedGradient period κ m φ) 2 (liftMeasure period) := by
  exact (liftedGradient_continuous period κ m φ hφ.2).memLp_of_hasCompactSupport
    (liftedGradient_hasCompactSupport period κ m φ hφ.1)

/-- Translation of a scalar test function on the cylinder. -/
def translatedTest (a : LiftDomain period) (φ : LiftDomain period → ℝ) :
    LiftDomain period → ℝ := fun x => φ (x + a)

omit [Fact (0 < period)] in
@[simp]
theorem localLift_translated (a x : LiftDomain period) (φ : LiftDomain period → ℝ) :
    localLift period (translatedTest period a φ) x = localLift period φ (x + a) := by
  funext h
  change φ (x.1 + h.1 + a.1, x.2 + (h.2 : AddCircle period) + a.2) =
    φ (x.1 + a.1 + h.1, x.2 + a.2 + (h.2 : AddCircle period))
  congr 1
  exact Prod.ext (add_right_comm _ _ _) (add_right_comm _ _ _)

omit [Fact (0 < period)] in
theorem smoothCompactTest_translated (a : LiftDomain period) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    HasCompactSupport (translatedTest period a φ) ∧
      ∀ x, ContDiff ℝ ∞ (localLift period (translatedTest period a φ) x) := by
  refine ⟨hφ.1.comp_homeomorph (Homeomorph.addRight a), fun x => ?_⟩
  rw [localLift_translated]
  exact hφ.2 (x + a)

omit [Fact (0 < period)] in
@[simp]
theorem liftedGradient_translated (κ : ℝ) (m : Vector3) (a x : LiftDomain period)
    (φ : LiftDomain period → ℝ) :
    liftedGradient period κ m (translatedTest period a φ) x =
      liftedGradient period κ m φ (x + a) := by
  simp only [liftedGradient, localLift_translated]

theorem measurePreserving_translation (a : LiftDomain period) :
    MeasurePreserving (fun x : LiftDomain period => x + a)
      (liftMeasure period) (liftMeasure period) := by
  exact (measurePreserving_add_right (volume : Measure Vector3) a.1).prod
    (measurePreserving_add_right (volume : Measure (AddCircle period)) a.2)

/-- The measure preserving translation isometry on the actual L² space. -/
def translation (a : LiftDomain period) : LiftL2 period →ₗᵢ[ℝ] LiftL2 period :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : LiftDomain period => x + a)
    (measurePreserving_translation period a)

theorem translation_ae (a : LiftDomain period) (f : LiftL2 period) :
    translation period a f =ᵐ[liftMeasure period] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translation period a)

theorem translation_norm (a : LiftDomain period) (f : LiftL2 period) :
    ‖translation period a f‖ = ‖f‖ :=
  (translation period a).norm_map f

theorem translation_add (a b : LiftDomain period) (f : LiftL2 period) :
    translation period a (translation period b f) = translation period (a + b) f := by
  apply Lp.ext
  filter_upwards [translation_ae period a (translation period b f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (translation_ae period b f), translation_ae period (a + b) f] with x hx₁ hx₂ hx₃
  rw [hx₁, hx₂, hx₃, add_assoc]

@[simp]
theorem translation_zero (f : LiftL2 period) : translation period 0 f = f := by
  apply Lp.ext
  filter_upwards [translation_ae period 0 f] with x hx
  simpa only [add_zero] using hx

/-- The L² element represented by an actual smooth compact test gradient. -/
def testGradientLp (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) : LiftL2 period :=
  (liftedGradient_memLp period κ m φ hφ).toLp (liftedGradient period κ m φ)

theorem testGradientLp_ae (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ =ᵐ[liftMeasure period] liftedGradient period κ m φ :=
  (liftedGradient_memLp period κ m φ hφ).coeFn_toLp

theorem testGradientLp_mem_generators (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    testGradientLp period κ m φ hφ ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}) :=
  ⟨φ, hφ, testGradientLp_ae period κ m φ hφ⟩

/-- Closure of the span of genuine smooth test gradients in the concrete L² space. -/
def gradientSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).topologicalClosure

theorem gradientSpace_closed (κ : ℝ) (m : Vector3) :
    IsClosed (gradientSpace period κ m : Set (LiftL2 period)) :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).isClosed_topologicalClosure

instance gradientSpace_complete (κ : ℝ) (m : Vector3) :
    CompleteSpace (gradientSpace period κ m) :=
  (gradientSpace_closed period κ m).completeSpace_coe

/-- Orthogonal projection onto the closed lifted gradient subspace. -/
def gradientProjection (κ : ℝ) (m : Vector3) : LiftL2 period →L[ℝ] LiftL2 period :=
  (gradientSpace period κ m).starProjection

/-- The projection bound is independent of the frequency parameter κ. -/
theorem gradientProjection_norm_le (κ : ℝ) (m : Vector3) :
    ‖gradientProjection period κ m‖ ≤ 1 :=
  (gradientSpace period κ m).starProjection_norm_le

theorem gradientProjection_apply_norm_le (κ : ℝ) (m : Vector3) (f : LiftL2 period) :
    ‖gradientProjection period κ m f‖ ≤ ‖f‖ :=
  (gradientSpace period κ m).norm_starProjection_apply_le f

theorem testGradient_mem (κ : ℝ) (m : Vector3) {g : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) : g ∈ gradientSpace period κ m :=
  (Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}))).le_topologicalClosure
    (Submodule.subset_span hg)

theorem gradientGenerators_translated (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    translation period a g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ}) := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  refine ⟨translatedTest period a φ, smoothCompactTest_translated period a φ hφ, ?_⟩
  filter_upwards [translation_ae period a g,
    (measurePreserving_translation period a).quasiMeasurePreserving.ae hgφ] with x hx₁ hx₂
  rw [hx₁, hx₂, liftedGradient_translated]

theorem gradientSpace_translation_mem (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {g : LiftL2 period} (hg : g ∈ gradientSpace period κ m) :
    translation period a g ∈ gradientSpace period κ m := by
  let τ := (translation period a).toContinuousLinearMap
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤
      (gradientSpace period κ m).comap τ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact testGradient_mem period κ m (gradientGenerators_translated period κ m a hf)
  have hclosed : IsClosed ((gradientSpace period κ m).comap τ.toLinearMap : Set (LiftL2 period)) :=
    (gradientSpace_closed period κ m).preimage τ.continuous
  exact (Submodule.topologicalClosure_minimal _ hspan hclosed) hg

theorem gradientSpace_map_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period) :
    (gradientSpace period κ m).map (translation period a).toLinearMap =
      gradientSpace period κ m := by
  apply le_antisymm
  · rintro g ⟨f, hf, rfl⟩
    exact gradientSpace_translation_mem period κ m a hf
  · intro g hg
    refine ⟨translation period (-a) g, gradientSpace_translation_mem period κ m (-a) hg, ?_⟩
    change translation period a (translation period (-a) g) = g
    rw [translation_add, add_neg_cancel, translation_zero]

/-- Orthogonal pressure projection commutes with every spatial or angular translation. -/
theorem gradientProjection_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (f : LiftL2 period) :
    translation period a (gradientProjection period κ m f) =
      gradientProjection period κ m (translation period a f) := by
  have hmap := gradientSpace_map_translation period κ m a
  let : ((gradientSpace period κ m).map (translation period a).toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  simpa only [gradientProjection, hmap] using
    (translation period a).map_starProjection (gradientSpace period κ m) f

/-- The concrete L² weak divergence-free subspace. -/
def divergenceFreeSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (gradientSpace period κ m).orthogonal

/-- Pressure cancellation in the concrete lifted L² space. -/
theorem pressure_pairing_zero (κ : ℝ) (m : Vector3) {p e : LiftL2 period}
    (hp : p ∈ gradientSpace period κ m) (he : e ∈ divergenceFreeSpace period κ m) :
    ⟪p, e⟫_ℝ = 0 := he p hp

theorem testGradient_pairing_zero (κ : ℝ) (m : Vector3) {g e : LiftL2 period}
    (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) (he : e ∈ divergenceFreeSpace period κ m) :
    ⟪g, e⟫_ℝ = 0 :=
  pressure_pairing_zero period κ m (testGradient_mem period κ m hg) he

/-- Orthogonality is the actual weak-divergence integral against every smooth compact test. -/
theorem weak_divergence_test_integral (κ : ℝ) (m : Vector3) {e : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (φ : LiftDomain period → ℝ)
    (hφ : HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (localLift period φ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, e x⟫_ℝ ∂liftMeasure period = 0 := by
  have hz := testGradient_pairing_zero period κ m
    (testGradientLp_mem_generators period κ m φ hφ) he
  rw [MeasureTheory.L2.inner_def] at hz
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [testGradientLp_ae period κ m φ hφ] with x hx
  rw [hx]

end EulerLiftedGradientSpace

end

section

/-!
Pointwise bounded coefficient fields act on genuine L² functions.  Their
pointwise positive quadratic bound supplies the Hilbert-space coercivity used
by the lifted pressure solver.  No multiplication operator is assumed.
-/


namespace EulerLiftedPressure

open MeasureTheory InnerProductSpace EulerCoerciveProjection EulerLiftedGradientSpace
open scoped ENNReal NNReal

section Multiplication

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientApply_memLp (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    MemLp (fun x => A x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := (C : ℝ))
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk (Lp.aestronglyMeasurable f))
  · exact Filter.Eventually.of_forall fun x =>
      ((A x).le_opNorm (f x)).trans
        (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- Pointwise bounded coefficient application represented as an L² element. -/
def coefficientApply (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) : Lp V 2 μ :=
  (coefficientApply_memLp A hA C hbound f).toLp (fun x => A x (f x))

theorem coefficientApply_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientApply A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  (coefficientApply_memLp A hA C hbound f).coeFn_toLp

/-- The linear map induced by pointwise coefficient multiplication. -/
def coefficientLinearMap (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →ₗ[ℝ] Lp V 2 μ where
  toFun := coefficientApply A hA C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (f + g),
      coefficientApply_ae A hA C hbound f, coefficientApply_ae A hA C hbound g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (coefficientApply A hA C hbound f) (coefficientApply A hA C hbound g)]
      with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp only [Pi.add_apply] at hx₄ hx₅
    rw [hx₁, hx₅, hx₂, hx₃, hx₄, map_add]
  map_smul' r f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [coefficientApply_ae A hA C hbound (r • f),
      coefficientApply_ae A hA C hbound f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (coefficientApply A hA C hbound f)] with x hx₁ hx₂ hx₃ hx₄
    simp only [Pi.smul_apply] at hx₃ hx₄
    rw [hx₁, hx₄, hx₂, hx₃, map_smul]

theorem coefficientApply_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    ‖coefficientApply A hA C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coefficientApply_ae A hA C hbound f] with x hx
  rw [hx]
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

/-- The bounded operator induced by the actual coefficient field. -/
def coefficientOperator (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (coefficientLinearMap A hA C hbound).mkContinuous C
    (coefficientApply_norm_le A hA C hbound)

theorem coefficientOperator_ae (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (f : Lp V 2 μ) :
    coefficientOperator A hA C hbound f =ᵐ[μ] fun x => A x (f x) :=
  coefficientApply_ae A hA C hbound f

theorem coefficientOperator_norm_le (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) :
    ‖coefficientOperator A hA C hbound‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    (coefficientApply_norm_le A hA C hbound)

/-- Pointwise coercivity yields the actual integral L² coercivity. -/
theorem coefficientOperator_coercive (A : α → V →L[ℝ] V) (hA : AEStronglyMeasurable A μ)
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : Lp V 2 μ) :
    c * ‖f‖ ^ 2 ≤ ⟪coefficientOperator A hA C hbound f, f⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner f f).const_mul c)
    (L2.integrable_inner (coefficientOperator A hA C hbound f) f)
  filter_upwards [coefficientOperator_ae A hA C hbound f] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
  exact hpositive x (f x)

theorem coefficientOperator_comp_apply (A B : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (C D : ℝ≥0) (hA_bound : ∀ x, ‖A x‖ ≤ C) (hB_bound : ∀ x, ‖B x‖ ≤ D)
    (hAB : ∀ x v, A x (B x v) = v) (f : Lp V 2 μ) :
    coefficientOperator A hA C hA_bound (coefficientOperator B hB D hB_bound f) = f := by
  apply Lp.ext
  filter_upwards [coefficientOperator_ae A hA C hA_bound
      (coefficientOperator B hB D hB_bound f),
    coefficientOperator_ae B hB D hB_bound f] with x hx₁ hx₂
  rw [hx₁, hx₂, hAB]

/-- Pointwise symmetry gives symmetry of the actual L² multiplication operator. -/
theorem coefficientOperator_inner_swap (A : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C)
    (hsym : ∀ x v w, ⟪A x v, w⟫_ℝ = ⟪v, A x w⟫_ℝ) (f g : Lp V 2 μ) :
    ⟪coefficientOperator A hA C hbound f, g⟫_ℝ =
      ⟪f, coefficientOperator A hA C hbound g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae A hA C hbound f,
    coefficientOperator_ae A hA C hbound g] with x hx₁ hx₂
  rw [hx₁, hx₂, hsym]

end Multiplication

section LiftedSolver

variable (period : ℝ) [Fact (0 < period)]

theorem existsUnique_lifted_pressure (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    ∃! p : gradientSpace period κ m,
      (gradientSpace period κ m).orthogonalProjectionOnto
        (coefficientOperator A hA C hbound (p : LiftL2 period)) =
      (gradientSpace period κ m).orthogonalProjectionOnto f :=
  existsUnique_projected_solution (gradientSpace period κ m)
    (coefficientOperator A hA C hbound) c hc
    (coefficientOperator_coercive A hA C hbound c hpositive) f

theorem exists_lifted_pressure_with_bound (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hbound : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpositive : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    ∃ p : gradientSpace period κ m,
      (gradientSpace period κ m).orthogonalProjectionOnto
        (coefficientOperator A hA C hbound (p : LiftL2 period)) =
        (gradientSpace period κ m).orthogonalProjectionOnto f ∧
      ‖p‖ ≤ c⁻¹ * ‖f‖ := by
  let hcoercive := coefficientOperator_coercive A hA C hbound c hpositive
  refine ⟨pressureSolver (gradientSpace period κ m)
    (coefficientOperator A hA C hbound) c hc hcoercive f, ?_, ?_⟩
  · exact pressureSolver_equation (gradientSpace period κ m)
      (coefficientOperator A hA C hbound) c hc hcoercive f
  · exact pressureSolver_apply_norm_le (gradientSpace period κ m)
      (coefficientOperator A hA C hbound) c hc hcoercive f

/-- Exact metric-pressure cancellation for pointwise inverse symmetric coefficient fields. -/
theorem metric_pressure_cancellation (κ : ℝ) (m : Vector3)
    (K G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (hG : AEStronglyMeasurable G (liftMeasure period))
    (C D : ℝ≥0) (hK_bound : ∀ x, ‖K x‖ ≤ C) (hG_bound : ∀ x, ‖G x‖ ≤ D)
    (hK_sym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hKG : ∀ x v, K x (G x v) = v) {e p : LiftL2 period}
    (he : e ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m) :
    ⟪coefficientOperator K hK C hK_bound e,
      coefficientOperator G hG D hG_bound p⟫_ℝ = 0 := by
  rw [coefficientOperator_inner_swap K hK C hK_bound hK_sym,
    coefficientOperator_comp_apply K G hK hG C D hK_bound hG_bound hKG]
  rw [real_inner_comm]
  exact pressure_pairing_zero period κ m hp he

end LiftedSolver

end EulerLiftedPressure

end

section

/-!
Transport integration by parts on the actual lifted cylinder.  Compactly
supported smooth energy fields are tested against the concrete weak-divergence
condition; boundary terms are eliminated by that proved weak formulation.
-/


namespace EulerMetricTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A field pulled back to real covering coordinates centered at a cylinder point. -/
def localFieldLift {W : Type*} (f : LiftDomain period → W) (x : LiftDomain period) :
    LiftTangent → W := fun h => f (x.1 + h.1, x.2 + (h.2 : AddCircle period))

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [Fact (0 < period)] [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    localFieldLift period f (coveringMap period z) =
      fun h => localFieldLift period f 0 (z + h) := by
  funext h
  simp [localFieldLift, coveringMap]

omit [Fact (0 < period)] in
theorem fderiv_localFieldLift_cover (f : LiftDomain period → W) (z : LiftTangent) :
    fderiv ℝ (localFieldLift period f (coveringMap period z)) 0 =
      fderiv ℝ (localFieldLift period f 0) z := by
  rw [localFieldLift_cover, fderiv_comp_add_left, add_zero]

omit [Fact (0 < period)] in
theorem smoothField_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : Continuous f := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : f ∘ coveringMap period = localFieldLift period f 0 := by
    funext z
    simp [localFieldLift, coveringMap]
  rw [heq]
  exact (hf 0).continuous

omit [Fact (0 < period)] in
theorem localFDeriv_continuous (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    Continuous (fun x => fderiv ℝ (localFieldLift period f x) 0) := by
  apply (coveringMap_isOpenQuotient period).isQuotientMap.continuous_iff.mpr
  have heq : (fun x => fderiv ℝ (localFieldLift period f x) 0) ∘ coveringMap period =
      fderiv ℝ (localFieldLift period f 0) := by
    funext z
    exact fderiv_localFieldLift_cover period f z
  rw [heq]
  exact (hf 0).continuous_fderiv (by simp)

end Fields

/-- The covering-space direction corresponding to one lifted gradient component. -/
def coordinateDirection (κ : ℝ) (m : Vector3) (i : Fin 3) : LiftTangent :=
  (κ • EuclideanSpace.single i 1, m i)

/-- The actual four dimensional transport vector associated with a lifted velocity. -/
def transportDirection (κ : ℝ) (m v : Vector3) : LiftTangent :=
  (κ • v, ⟪m, v⟫_ℝ)

/-- The vector of a scalar differential evaluated on the lifted coordinate directions. -/
def vectorOfLinear (κ : ℝ) (m : Vector3) (L : LiftTangent →L[ℝ] ℝ) : Vector3 :=
  WithLp.toLp 2 fun i => L (coordinateDirection κ m i)

theorem coordinateDirections_sum (κ : ℝ) (m v : Vector3) :
    ∑ i : Fin 3, v i • coordinateDirection κ m i = transportDirection κ m v := by
  have hrepr : ∑ i : Fin 3, v i • EuclideanSpace.single i 1 = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  apply Prod.ext
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).1 = κ • v
    calc
      (∑ i : Fin 3, v i • coordinateDirection κ m i).1 =
          ∑ i : Fin 3, v i • (κ • EuclideanSpace.single i 1) := by
            simp [Prod.fst_sum, coordinateDirection]
      _ = κ • ∑ i : Fin 3, v i • EuclideanSpace.single i 1 := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_comm _ _ _
      _ = κ • v := by rw [hrepr]
  · change (∑ i : Fin 3, v i • coordinateDirection κ m i).2 = ⟪m, v⟫_ℝ
    simp [Prod.snd_sum, coordinateDirection, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]

theorem vectorOfLinear_inner (κ : ℝ) (m v : Vector3) (L : LiftTangent →L[ℝ] ℝ) :
    ⟪vectorOfLinear κ m L, v⟫_ℝ = L (transportDirection κ m v) := by
  rw [← coordinateDirections_sum κ m v, map_sum]
  simp [vectorOfLinear, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    map_smul, smul_eq_mul]

omit [Fact (0 < period)] in
theorem liftedGradient_eq_vectorOfLinear (κ : ℝ) (m : Vector3)
    (φ : LiftDomain period → ℝ) (x : LiftDomain period) :
    liftedGradient period κ m φ x =
      vectorOfLinear κ m (fderiv ℝ (localLift period φ x) 0) := by
  apply PiLp.ext
  intro i
  have hd : coordinateDirection κ m i =
      κ • (EuclideanSpace.single i 1, (0 : ℝ)) + m i • ((0 : Vector3), (1 : ℝ)) := by
    ext <;> simp [coordinateDirection]
  change κ * (fderiv ℝ (localLift period φ x) 0) (EuclideanSpace.single i 1, 0) +
      m i * (fderiv ℝ (localLift period φ x) 0) (0, 1) =
    (fderiv ℝ (localLift period φ x) 0) (coordinateDirection κ m i)
  rw [hd, map_add, map_smul, map_smul]
  rfl

/-- The pointwise quadratic metric energy of a vector field. -/
def metricEnergy (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : ℝ :=
  (1 / 2 : ℝ) * ⟪K x (e x), e x⟫_ℝ

omit [Fact (0 < period)] in
theorem metricEnergy_compact (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (metricEnergy period K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  simp [Function.mem_support, metricEnergy, hx]

omit [Fact (0 < period)] in
theorem metricEnergy_smooth (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (metricEnergy period K e) x) := by
  exact contDiff_const.mul (((hK x).clm_apply (he x)).inner ℝ (he x))

omit [Fact (0 < period)] in
theorem metricEnergy_fderiv (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ +
        (1 / 2 : ℝ) *
          ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ := by
  have hdK := ((hK x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hde := ((he x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hd := (((hdK.clm_apply hde).inner ℝ hde).const_mul (1 / 2 : ℝ)).fderiv
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) hd
  dsimp [localFieldLift] at heq
  change fderiv ℝ (localLift period (metricEnergy period K e) x) 0 v = _ at heq
  rw [heq]
  simp only [smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_apply,
    ContinuousLinearMap.flip_apply, add_zero, inner_add_left]
  have hs : ⟪K x (fderiv ℝ (localFieldLift period e x) 0 v), e x⟫_ℝ =
      ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0 v⟫_ℝ := by
    rw [hsym]
    exact real_inner_comm _ _
  rw [hs]
  ring

omit [Fact (0 < period)] in
theorem metricEnergy_gradient_transport (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (x : LiftDomain period) (z : Vector3) :
    ⟪liftedGradient period κ m (metricEnergy period K e) x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m z)) (e x), e x⟫_ℝ := by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  exact metricEnergy_fderiv period K e hK he hsym x _

theorem metric_transport_zero (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    ∫ x, (⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ +
      (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ∂liftMeasure period = 0 := by
  have htest := weak_divergence_test_integral period κ m hz (metricEnergy period K e)
    ⟨metricEnergy_compact period K e hec, metricEnergy_smooth period K e hK he⟩
  convert htest using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    (metricEnergy_gradient_transport period κ m K e hK he hsym x (z x)).symm

/-- The compact vector coefficient whose pairing with velocity is the metric transport term. -/
def transportFlux (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) : Vector3 :=
  vectorOfLinear κ m ((innerSL ℝ (K x (e x))).comp
    (fderiv ℝ (localFieldLift period e x) 0))

omit [Fact (0 < period)] in
theorem transportFlux_inner (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (x : LiftDomain period) (z : Vector3) :
    ⟪transportFlux period κ m K e x, z⟫_ℝ =
      ⟪K x (e x),
        fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m z)⟫_ℝ := by
  rw [transportFlux, vectorOfLinear_inner]
  rfl

omit [Fact (0 < period)] in
theorem transportFlux_continuous (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) :
    Continuous (transportFlux period κ m K e) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact ((smoothField_continuous period K hK).clm_apply
    (smoothField_continuous period e he)).inner
      ((localFDeriv_continuous period e he).clm_apply continuous_const)

omit [Fact (0 < period)] in
theorem transportFlux_compact (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (he : HasCompactSupport e) :
    HasCompactSupport (transportFlux period κ m K e) := by
  apply he.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  apply PiLp.ext
  intro i
  simp [transportFlux, vectorOfLinear, hx]

theorem compact_pairing_integrable (f : LiftDomain period → Vector3)
    (hf : Continuous f) (hfc : HasCompactSupport f) (z : LiftL2 period) :
    Integrable (fun x => ⟪f x, z x⟫_ℝ) (liftMeasure period) := by
  have hlp : MemLp f 2 (liftMeasure period) := hf.memLp_of_hasCompactSupport hfc
  apply (L2.integrable_inner (hlp.toLp f) z).congr
  filter_upwards [hlp.coeFn_toLp] with x hx
  rw [hx]

theorem metric_transport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x)) (z : LiftL2 period) :
    Integrable (fun x => ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ)
      (liftMeasure period) := by
  simpa only [transportFlux_inner] using
    compact_pairing_integrable period (transportFlux period κ m K e)
      (transportFlux_continuous period κ m K e hK he)
      (transportFlux_compact period κ m K e hec) z

theorem metric_transport_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m) :
    (∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have ht := metric_transport_integrable period κ m K e hec hK he z
  have hg := compact_pairing_integrable period
    (liftedGradient period κ m (metricEnergy period K e))
    (liftedGradient_continuous period κ m (metricEnergy period K e)
      (metricEnergy_smooth period K e hK he))
    (liftedGradient_hasCompactSupport period κ m (metricEnergy period K e)
      (metricEnergy_compact period K e hec)) z
  simp only [metricEnergy_gradient_transport period κ m K e hK he hsym] at hg
  have hq : Integrable (fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
    convert hg.sub ht using 1
    funext x
    simp
  have hzint := metric_transport_zero period κ m K e hec hK he hsym hz
  rw [integral_add ht hq] at hzint
  exact eq_neg_of_add_eq_zero_left hzint

theorem transportDirection_norm_le (κ : ℝ) (m v : Vector3) :
    ‖transportDirection κ m v‖ ≤ (|κ| + ‖m‖) * ‖v‖ := by
  rw [transportDirection, Prod.norm_mk, norm_smul, Real.norm_eq_abs]
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg m))
      (norm_nonneg v)
  · exact (norm_inner_le_norm m v).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg κ)) (norm_nonneg v))

theorem metric_transport_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3) (hec : HasCompactSupport e)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C B : ℝ≥0)
    (hDK : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ C)
    (hb : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    |∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))⟫_ℝ
      ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * C * B * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  rw [metric_transport_by_parts period κ m K e hec hK he hsym hz, abs_neg]
  have heLp : MemLp e 2 (liftMeasure period) :=
    (smoothField_continuous period e he).memLp_of_hasCompactSupport hec
  have heint := heLp.norm.integrable_sq
  have hbound := norm_integral_le_of_norm_le
    (heint.const_mul ((1 / 2 : ℝ) * C * B)) (f := fun x => (1 / 2 : ℝ) *
      ⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hb] with x hx
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))‖ ≤ (C : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul (hDK x) hx (norm_nonneg _) C.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x)‖ ≤ (C : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x), e x⟫_ℝ‖ := by
          rw [norm_mul]
          norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0
        (transportDirection κ m (z x))) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * B * ‖e x‖) * ‖e x‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hLe (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem metric_transport_L2_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftL2 period) (hec : HasCompactSupport (fun x => e x))
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C B : ℝ≥0)
    (hDK : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ C)
    (hb : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    |∫ x, ⟪K x (e x),
      fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * C * B * ‖e‖ ^ 2 := by
  have hn : (∫ x, ‖e x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_bound period κ m K (fun x => e x)
    hec hK he hsym hz C B hDK hb

end EulerMetricTransport

end

section

/-!
Actual directional differentiation of transport and coefficient multiplication.
The commutator is derived by the chain rule and symmetry of second derivatives,
rather than postulated as a recurrence on a norm sequence.
-/


namespace EulerTransportDerivatives

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal NNReal Topology

section Euclidean

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual Fréchet directional derivative along a constant vector. -/
def directionalDerivative (a : V) (f : V → W) (x : V) : W := fderiv ℝ f x a

/-- Differentiation of a field in the direction of a variable transport field. -/
def transport (b : V → V) (f : V → W) (x : V) : W := fderiv ℝ f x (b x)

theorem directionalDerivative_smooth (a : V) (f : V → W) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalDerivative a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem transport_smooth (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (transport b f) := by
  exact (hf.fderiv_right (by simp)).clm_apply hb

theorem directional_transport_commutator (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    directionalDerivative a (transport b f) x =
      transport b (directionalDerivative a f) x +
        fderiv ℝ f x (directionalDerivative a b x) := by
  have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp)) x).hasFDerivAt
  have hdb := (hb.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hdT := congrArg (fun L : V →L[ℝ] W => L a) (hdf.clm_apply hdb).fderiv
  have hdA := congrArg (fun L : V →L[ℝ] W => L (b x))
    (hdf.clm_apply (hasFDerivAt_const a x)).fderiv
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) a (b x)
  change fderiv ℝ (transport b f) x a = _ at hdT
  change fderiv ℝ (directionalDerivative a f) x (b x) = _ at hdA
  change fderiv ℝ (transport b f) x a =
    fderiv ℝ (directionalDerivative a f) x (b x) + fderiv ℝ f x (fderiv ℝ b x a)
  rw [hdT, hdA]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add]
  rw [hs]
  exact add_comm _ _

theorem directional_transport_commutator_norm (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    ‖directionalDerivative a (transport b f) x -
      transport b (directionalDerivative a f) x‖ ≤
        ‖fderiv ℝ f x‖ * ‖directionalDerivative a b x‖ := by
  rw [directional_transport_commutator a b f hb hf x, add_sub_cancel_left]
  exact (fderiv ℝ f x).le_opNorm _

end Euclidean

variable (period : ℝ)

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Directional differentiation in the cylinder covering coordinates. -/
def fieldDerivative (a : LiftTangent) (f : LiftDomain period → W)
    (x : LiftDomain period) : W := fderiv ℝ (localFieldLift period f x) 0 a

/-- The actual directional transport operator on a cylinder field. -/
def fieldTransport (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) : W :=
  fderiv ℝ (localFieldLift period f x) 0 (b x)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    localFieldLift period f (x.1 + h.1, x.2 + (h.2 : AddCircle period)) =
      fun u => localFieldLift period f x (h + u) := by
  funext u
  simp [localFieldLift, add_assoc]

theorem fderiv_localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    fderiv ℝ (localFieldLift period f
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) 0 =
      fderiv ℝ (localFieldLift period f x) h := by
  rw [localFieldLift_shift, fderiv_comp_add_left, add_zero]

theorem localFieldLift_fieldDerivative (a : LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldDerivative period a f) x =
      directionalDerivative a (localFieldLift period f x) := by
  funext h
  exact congrArg (fun L : LiftTangent →L[ℝ] W => L a)
    (fderiv_localFieldLift_shift period f x h)

theorem localFieldLift_fieldTransport (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldTransport period b f) x =
      transport (localFieldLift period b x) (localFieldLift period f x) := by
  funext h
  exact congrArg (fun L : LiftTangent →L[ℝ] W => L (localFieldLift period b x h))
    (fderiv_localFieldLift_shift period f x h)

theorem fieldDerivative_smooth (a : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldDerivative period a f) x) := by
  rw [localFieldLift_fieldDerivative]
  exact directionalDerivative_smooth a _ (hf x)

theorem fieldTransport_smooth (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldTransport period b f) x) := by
  rw [localFieldLift_fieldTransport]
  exact transport_smooth _ _ (hb x) (hf x)

theorem field_transport_commutator (a : LiftTangent)
    (b : LiftDomain period → LiftTangent) (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    fieldDerivative period a (fieldTransport period b f) x =
      fieldTransport period b (fieldDerivative period a f) x +
        fderiv ℝ (localFieldLift period f x) 0 (fieldDerivative period a b x) := by
  have hc := directional_transport_commutator a (localFieldLift period b x)
    (localFieldLift period f x) (hb x) (hf x) 0
  simpa only [fieldDerivative, fieldTransport, localFieldLift_fieldTransport,
    localFieldLift_fieldDerivative, directionalDerivative, transport, localFieldLift,
    Prod.fst_zero, Prod.snd_zero, AddCircle.coe_zero, add_zero] using hc

theorem field_transport_commutator_norm (a : LiftTangent)
    (b : LiftDomain period → LiftTangent) (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖fieldDerivative period a (fieldTransport period b f) x -
      fieldTransport period b (fieldDerivative period a f) x‖ ≤
        ‖fderiv ℝ (localFieldLift period f x) 0‖ *
          ‖fieldDerivative period a b x‖ := by
  rw [field_transport_commutator period a b f hb hf x, add_sub_cancel_left]
  exact (fderiv ℝ (localFieldLift period f x) 0).le_opNorm _

end Fields

end EulerTransportDerivatives

end

section

/-!
Spatial pressure regularity in the genuine lifted L² space.  Coefficient
translations are actual pointwise translations, and pressure translation
covariance follows from the uniquely constructed projected equation.
-/


namespace EulerPressureSpatialRegularity

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerCoerciveProjection EulerInverseRegularity EulerMetricTransport EulerTransportDerivatives
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

section CoefficientDifferentiation

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coefficientOperator_remainder_norm
    (A B D : α → V →L[ℝ] V)
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hD : AEStronglyMeasurable D μ) (CA CB CD R : ℝ≥0)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hBb : ∀ x, ‖B x‖ ≤ CB) (hDb : ∀ x, ‖D x‖ ≤ CD)
    (t : ℝ) (hR : ∀ x, ‖A x - B x - t • D x‖ ≤ R) :
    ‖coefficientOperator A hA CA hAb - coefficientOperator B hB CB hBb -
      t • coefficientOperator D hD CD hDb‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ R.coe_nonneg
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  let a := coefficientOperator A hA CA hAb f
  let b := coefficientOperator B hB CB hBb f
  let d := coefficientOperator D hD CD hDb f
  filter_upwards [coefficientOperator_ae A hA CA hAb f,
    coefficientOperator_ae B hB CB hBb f, coefficientOperator_ae D hD CD hDb f,
    Lp.coeFn_sub a b, Lp.coeFn_smul t d, Lp.coeFn_sub (a - b) (t • d)]
    with x ha hb hd hab htd hsub
  change ‖((a - b) - t • d) x‖ ≤ (R : ℝ) * ‖f x‖
  simp only [Pi.sub_apply, Pi.smul_apply] at hab htd hsub
  rw [hsub, hab, htd]
  change ‖a x - b x - t • d x‖ ≤ _
  rw [ha, hb, hd]
  change ‖(A x - B x - t • D x) (f x)‖ ≤ _
  exact ((A x - B x - t • D x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg _))

theorem uniform_derivative_remainder {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f f' : ℝ → W) (hf : ∀ s, HasDerivAt f (f' s) s) (L : ℝ≥0)
    (hL : ∀ s, ‖f' s - f' 0‖ ≤ L * |s|) (t : ℝ) :
    ‖f t - f 0 - t • f' 0‖ ≤ L * |t| ^ 2 := by
  have hd : ∀ s, HasDerivAt (fun u => f u - u • f' 0) (f' s - f' 0) s := by
    intro s
    convert (hf s).sub ((hasDerivAt_id s).smul_const (f' 0)) using 1
    · rfl
    · simp
  have hb : ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖f' s - f' 0‖ ≤ (L : ℝ) * |t| := by
    intro s hs
    exact (hL s).trans (mul_le_mul_of_nonneg_left
      (by simpa using Set.abs_sub_left_of_mem_uIcc hs) L.coe_nonneg)
  have hm := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, sub_zero, Real.norm_eq_abs] at hm
  calc
    ‖f t - f 0 - t • f' 0‖ = ‖f t - t • f' 0 - f 0‖ := by congr 1; abel
    _ ≤ (L : ℝ) * |t| * |t| := hm
    _ = _ := by ring

theorem coefficientOperator_hasDerivAt
    (A A' : ℝ → α → V →L[ℝ] V)
    (hA : ∀ t, AEStronglyMeasurable (A t) μ)
    (hA' : AEStronglyMeasurable (A' 0) μ)
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|) :
    HasDerivAt (fun t => coefficientOperator (A t) (hA t) C (hAb t))
      (coefficientOperator (A' 0) hA' D hDb) 0 := by
  apply (hasDerivAt_iff_tendsto
    (f := fun t => coefficientOperator (A t) (hA t) C (hAb t))
    (f' := coefficientOperator (A' 0) hA' D hDb) (x := (0 : ℝ))).mpr
  apply squeeze_zero
  · intro t
    positivity
  · intro t
    let R : ℝ≥0 := ⟨(L : ℝ) * |t| ^ 2, mul_nonneg L.coe_nonneg (sq_nonneg _)⟩
    have hr := coefficientOperator_remainder_norm (A t) (A 0) (A' 0)
      (hA t) (hA 0) hA' C C D R
      (hAb t) (hAb 0) hDb t
      (fun x => uniform_derivative_remainder (fun s => A s x) (fun s => A' s x)
        (fun s => hder s x) L (fun s => hLip s x) t)
    change ‖coefficientOperator (A t) (hA t) C (hAb t) -
      coefficientOperator (A 0) (hA 0) C (hAb 0) -
      t • coefficientOperator (A' 0) hA' D hDb‖ ≤ (L : ℝ) * |t| ^ 2 at hr
    simp only [sub_zero]
    calc
      _ ≤ ‖t‖⁻¹ * ((L : ℝ) * |t| ^ 2) :=
        mul_le_mul_of_nonneg_left hr (inv_nonneg.2 (norm_nonneg _))
      _ ≤ (L : ℝ) * |t| := by
        by_cases ht : t = 0
        · simp [ht]
        · rw [Real.norm_eq_abs]
          have ha : |t| ≠ 0 := abs_ne_zero.mpr ht
          field_simp
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

end CoefficientDifferentiation

theorem directionalDerivative_line_lipschitz
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (hf : ContDiff ℝ ∞ f) (M : ℝ≥0)
    (hDD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (a : V) (t : ℝ) :
    ‖fderiv ℝ f (t • a) a - fderiv ℝ f 0 a‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => fderiv ℝ f (u • a) a)
      ((fderiv ℝ (fderiv ℝ f) (s • a) a) a) s := by
    intro s
    have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp)) (s • a)).hasFDerivAt
    have hline := hdf.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a)
    simpa using hline.clm_apply (hasDerivAt_const s a)
  have hb : ∀ s ∈ (Set.univ : Set ℝ),
      ‖(fderiv ℝ (fderiv ℝ f) (s • a) a) a‖ ≤ (M : ℝ) * ‖a‖ ^ 2 := by
    intro s _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) (s • a) a‖ * ‖a‖ :=
        (fderiv ℝ (fderiv ℝ f) (s • a) a).le_opNorm a
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) (s • a)‖ * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          ((fderiv ℝ (fderiv ℝ f) (s • a)).le_opNorm a) (norm_nonneg _)
      _ ≤ ((M : ℝ) * ‖a‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hDD _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hm := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) hb (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [zero_smul, sub_zero, Real.norm_eq_abs] using hm

section LiftedTranslation

variable (period : ℝ) [Fact (0 < period)]

/-- Pointwise coefficient translation on the actual cylinder. -/
def translatedCoefficient (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (x : LiftDomain period) := A (x + a)

theorem translatedCoefficient_measurable (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period)) :
    AEStronglyMeasurable (translatedCoefficient period a A) (liftMeasure period) :=
  hA.comp_measurePreserving (measurePreserving_translation period a)

/-- The one-parameter spatial/angular translation determined by a covering-space direction. -/
def translationPath (a : LiftTangent) (t : ℝ) : LiftDomain period :=
  coveringMap period (t • a)

omit [Fact (0 < period)] in
@[simp]
theorem translationPath_zero (a : LiftTangent) : translationPath period a 0 = 0 := by
  simp [translationPath, coveringMap]

/-- The actual directional derivative of the translated coefficient field. -/
def translatedCoefficientDerivative (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :=
  fderiv ℝ (localFieldLift period A x) (t • a) a

omit [Fact (0 < period)] in
theorem translatedCoefficient_path (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (t : ℝ) (x : LiftDomain period) :
    translatedCoefficient period (translationPath period a t) A x =
      localFieldLift period A x (t • a) := rfl

omit [Fact (0 < period)] in
theorem translatedCoefficient_hasDerivAt (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (t : ℝ) (x : LiftDomain period) :
    HasDerivAt (fun s => translatedCoefficient period (translationPath period a s) A x)
      (translatedCoefficientDerivative period a A t x) t := by
  have hd := (((hA x).differentiable (by simp)) (t • a)).hasFDerivAt
  simpa only [translatedCoefficient_path, translatedCoefficientDerivative, one_smul,
    Function.comp_def, id_eq] using
    hd.comp_hasDerivAt t ((hasDerivAt_id t).smul_const a)

theorem translatedCoefficientDerivative_measurable (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) :
    AEStronglyMeasurable (translatedCoefficientDerivative period a A 0) (liftMeasure period) := by
  have hc := (localFDeriv_continuous period A hA).clm_apply (g := fun _ => a) continuous_const
  change AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period A x) (0 • a) a)
    (liftMeasure period)
  simpa only [zero_smul] using hc.aestronglyMeasurable (μ := liftMeasure period)

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_bound (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3) (D : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A 0 x‖ ≤ (D : ℝ) * ‖a‖ := by
  simp only [translatedCoefficientDerivative, zero_smul]
  exact ((fderiv ℝ (localFieldLift period A x) 0).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))

omit [Fact (0 < period)] in
theorem translatedCoefficientDerivative_lipschitz (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖translatedCoefficientDerivative period a A t x -
      translatedCoefficientDerivative period a A 0 x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| := by
  simpa only [translatedCoefficientDerivative, zero_smul] using
    directionalDerivative_line_lipschitz (localFieldLift period A x) (hA x) M (hDD x) a t

theorem coefficientOperator_translation (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (f : LiftL2 period) :
    translation period a (coefficientOperator A hA C hAb f) =
      coefficientOperator (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
        (translation period a f) := by
  apply Lp.ext
  filter_upwards [translation_ae period a (coefficientOperator A hA C hAb f),
    (measurePreserving_translation period a).quasiMeasurePreserving.ae
      (coefficientOperator_ae A hA C hAb f),
    coefficientOperator_ae (translatedCoefficient period a A)
      (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a))
      (translation period a f), translation_ae period a f] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂, hx₃, hx₄]
  rfl

/-- The concrete coercive pressure solution, viewed in ambient L². -/
def liftedPressure (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) : LiftL2 period :=
  pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f

theorem liftedPressure_mem (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    liftedPressure period κ m A hA C hAb c hc hpos f ∈ gradientSpace period κ m :=
  (pressureSolver (gradientSpace period κ m) (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f).property

theorem liftedPressure_equation (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    gradientProjection period κ m
      (coefficientOperator A hA C hAb (liftedPressure period κ m A hA C hAb c hc hpos f)) =
      gradientProjection period κ m f := by
  exact congrArg Subtype.val (pressureSolver_equation (gradientSpace period κ m)
    (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) f)

theorem liftedPressure_unique (κ : ℝ) (m : Vector3)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f p : LiftL2 period)
    (hp : p ∈ gradientSpace period κ m)
    (heq : gradientProjection period κ m (coefficientOperator A hA C hAb p) =
      gradientProjection period κ m f) :
    p = liftedPressure period κ m A hA C hAb c hc hpos f := by
  let S := gradientSpace period κ m
  let G := coefficientOperator A hA C hAb
  let hG := coefficientOperator_coercive A hA C hAb c hpos
  have hsub : (⟨p, hp⟩ : S) = pressureSolver S G c hc hG f := by
    apply (coerciveEquiv (projectedOperator S G) c hc
      (projectedOperator_coercive S G c hG)).injective
    simp only [coerciveEquiv_apply]
    change S.orthogonalProjectionOnto (G p) =
      S.orthogonalProjectionOnto (G (pressureSolver S G c hc hG f : LiftL2 period))
    rw [pressureSolver_equation]
    exact Subtype.ext heq
  exact congrArg Subtype.val hsub

theorem liftedPressure_translation (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (C : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ) (f : LiftL2 period) :
    translation period a (liftedPressure period κ m A hA C hAb c hc hpos f) =
      liftedPressure period κ m (translatedCoefficient period a A)
        (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
        (fun x v => hpos (x + a) v) (translation period a f) := by
  apply liftedPressure_unique period κ m (translatedCoefficient period a A)
    (translatedCoefficient_measurable period a A hA) C (fun x => hAb (x + a)) c hc
    (fun x v => hpos (x + a) v)
  · exact gradientSpace_translation_mem period κ m a
      (liftedPressure_mem period κ m A hA C hAb c hc hpos f)
  · rw [← coefficientOperator_translation period a A hA C hAb,
      ← gradientProjection_translation,
      liftedPressure_equation, gradientProjection_translation]

theorem liftedPressure_hasDerivAt (κ : ℝ) (m : Vector3)
    (A A' : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : ∀ t, AEStronglyMeasurable (A t) (liftMeasure period))
    (hA' : AEStronglyMeasurable (A' 0) (liftMeasure period))
    (C D L : ℝ≥0) (hAb : ∀ t x, ‖A t x‖ ≤ C) (hDb : ∀ x, ‖A' 0 x‖ ≤ D)
    (hder : ∀ t x, HasDerivAt (fun s => A s x) (A' t x) t)
    (hLip : ∀ t x, ‖A' t x - A' 0 x‖ ≤ L * |t|)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪A t x v, v⟫_ℝ)
    (f : ℝ → LiftL2 period) (f' : LiftL2 period) (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t => liftedPressure period κ m (A t) (hA t) C (hAb t) c hc
      (hpos t) (f t))
      (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0)
        (f' - coefficientOperator (A' 0) hA' D hDb
          (liftedPressure period κ m (A 0) (hA 0) C (hAb 0) c hc (hpos 0) (f 0)))) 0 := by
  let S := gradientSpace period κ m
  let G := fun t => coefficientOperator (A t) (hA t) C (hAb t)
  let G' := coefficientOperator (A' 0) hA' D hDb
  have hG : ∀ t u, c * ‖u‖ ^ 2 ≤ ⟪G t u, u⟫_ℝ :=
    fun t => coefficientOperator_coercive (A t) (hA t) C (hAb t) c (hpos t)
  have hGder : HasDerivAt G G' 0 :=
    coefficientOperator_hasDerivAt A A' hA hA' C D L hAb hDb hder hLip
  have hsol := hasDerivAt_coerciveSolution (fun t => projectedOperator S (G t)) c hc
    (fun t => projectedOperator_coercive S (G t) c (hG t))
    (fun t => S.orthogonalProjectionOnto (f t)) 0 (projectedOperator S G')
    (S.orthogonalProjectionOnto f')
    (hasDerivAt_projectedOperator S G 0 G' hGder)
    (S.orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt 0 hf)
  have hval := S.subtypeL.hasFDerivAt.comp_hasDerivAt 0 hsol
  convert hval using 1
  · rfl
  · rfl
  · rfl
  · simp [liftedPressure, pressureSolver, projectedInverse, projectedOperator,
      S, G, G', ContinuousLinearMap.comp_apply, map_sub]

theorem pressure_translation_hasDerivAt (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (liftedPressure period κ m A hA C hAb c hc hpos f))
      (liftedPressure period κ m A hA C hAb c hc hpos
        (f' - coefficientOperator (translatedCoefficientDerivative period a A 0)
          (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
          (fun x => translatedCoefficientDerivative_bound period a A D hDA x)
          (liftedPressure period κ m A hA C hAb c hc hpos f))) 0 := by
  let At := fun t => translatedCoefficient period (translationPath period a t) A
  let Ad := translatedCoefficientDerivative period a A
  have hAt : ∀ t, AEStronglyMeasurable (At t) (liftMeasure period) :=
    fun t => translatedCoefficient_measurable period (translationPath period a t) A hA
  have hAtb : ∀ t x, ‖At t x‖ ≤ C := fun t x => hAb (x + translationPath period a t)
  have hAtpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪At t x v, v⟫_ℝ :=
    fun t x v => hpos (x + translationPath period a t) v
  have hAdb : ∀ x, ‖Ad 0 x‖ ≤ (D * ‖a‖₊ : ℝ≥0) :=
    fun x => translatedCoefficientDerivative_bound period a A D hDA x
  have hAdL : ∀ t x, ‖Ad t x - Ad 0 x‖ ≤ (M * ‖a‖₊ ^ 2 : ℝ≥0) * |t| := by
    intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A hAs M hDDA t x
  have hsol := liftedPressure_hasDerivAt period κ m At Ad hAt
    (translatedCoefficientDerivative_measurable period a A hAs)
    C (D * ‖a‖₊) (M * ‖a‖₊ ^ 2) hAtb hAdb
    (translatedCoefficient_hasDerivAt period a A hAs) hAdL c hc hAtpos
    (fun t => translation period (translationPath period a t) f) f' hf
  have hcov : (fun t => liftedPressure period κ m (At t) (hAt t) C (hAtb t)
      c hc (hAtpos t) (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t)
        (liftedPressure period κ m A hA C hAb c hc hpos f) := by
    funext t
    exact (liftedPressure_translation period κ m (translationPath period a t)
      A hA C hAb c hc hpos f).symm
  rw [hcov] at hsol
  have hzero : At 0 = A := by
    funext x
    simp [At, translatedCoefficient]
  simpa only [hzero, translationPath_zero, translation_zero] using hsol

theorem pressure_translation_derivative_norm (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    ‖deriv (fun t => translation period (translationPath period a t)
      (liftedPressure period κ m A hA C hAb c hc hpos f)) 0‖ ≤
        c⁻¹ * (‖f'‖ + (D : ℝ) * ‖a‖ *
          ‖liftedPressure period κ m A hA C hAb c hc hpos f‖) := by
  have hd := pressure_translation_hasDerivAt period κ m a A hA hAs C D M hAb hDA hDDA
    c hc hpos f f' hf
  rw [hd.deriv]
  refine (pressureSolver_apply_norm_le (gradientSpace period κ m)
    (coefficientOperator A hA C hAb) c hc
    (coefficientOperator_coercive A hA C hAb c hpos) _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ ‖f'‖)
  exact coefficientApply_norm_le (translatedCoefficientDerivative period a A 0)
    (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
    (fun x => translatedCoefficientDerivative_bound period a A D hDA x)
    (liftedPressure period κ m A hA C hAb c hc hpos f)

end LiftedTranslation

end EulerPressureSpatialRegularity

end

section

/-!
Translation derivatives and actual weak derivatives on the lifted cylinder.
Smooth compact test fields are realized in L², and their translation orbits
are differentiated in the strong L² topology.
-/


namespace EulerLiftedWeakDerivative

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

section FieldCalculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The full derivative of a field in covering coordinates, evaluated at the center. -/
def fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) : LiftTangent →L[ℝ] W :=
  fderiv ℝ (localFieldLift period f x) 0

omit [Fact (0 < period)] in
theorem localFieldLift_fieldFDeriv (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldFDeriv period f) x = fderiv ℝ (localFieldLift period f x) := by
  funext h
  exact fderiv_localFieldLift_shift period f x h

omit [Fact (0 < period)] in
theorem fieldFDeriv_smooth (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldFDeriv period f) x) := by
  rw [localFieldLift_fieldFDeriv]
  exact (hf x).fderiv_right (by simp)

omit [Fact (0 < period)] in
theorem fieldFDeriv_zero_outside (f : LiftDomain period → W) (x : LiftDomain period)
    (hx : x ∉ tsupport f) : fieldFDeriv period f x = 0 := by
  have hc : Continuous (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) :=
    (continuous_const.add continuous_fst).prodMk
      (continuous_const.add ((AddCircle.continuous_mk' period).comp continuous_snd))
  have ht : Filter.Tendsto (fun h : LiftTangent =>
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) (𝓝 0) (𝓝 x) := by
    simpa using hc.tendsto (0 : LiftTangent)
  have hz : localFieldLift period f x =ᶠ[𝓝 0] (fun _ : LiftTangent => (0 : W)) :=
    (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto ht
  change fderiv ℝ (localFieldLift period f x) 0 = 0
  rw [hz.fderiv_eq]
  simp

omit [Fact (0 < period)] in
theorem fieldFDeriv_compact (f : LiftDomain period → W) (hf : HasCompactSupport f) :
    HasCompactSupport (fieldFDeriv period f) :=
  HasCompactSupport.intro hf (fieldFDeriv_zero_outside period f)

omit [Fact (0 < period)] in
theorem fieldDerivative_compact (a : LiftTangent) (f : LiftDomain period → W)
    (hf : HasCompactSupport f) : HasCompactSupport (fieldDerivative period a f) := by
  apply (fieldFDeriv_compact period f hf).mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  change fieldFDeriv period f x a = 0
  rw [hx]
  rfl

theorem fieldDerivative_memLp (a : LiftTangent) (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (fieldDerivative period a f) 2 (liftMeasure period) :=
  (smoothField_continuous period _ (fieldDerivative_smooth period a f hf)).memLp_of_hasCompactSupport
    (fieldDerivative_compact period a f hfc)

omit [Fact (0 < period)] in
theorem compact_smooth_second_derivative_bound (f : LiftDomain period → W)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∃ M : ℝ≥0, ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M := by
  let F := fieldFDeriv period (fieldFDeriv period f)
  have hFc : HasCompactSupport F := fieldFDeriv_compact period _ (fieldFDeriv_compact period f hfc)
  have hFs : ∀ x, ContDiff ℝ ∞ (localFieldLift period F x) :=
    fieldFDeriv_smooth period _ (fieldFDeriv_smooth period f hf)
  have hFb := (hFc.isCompact_range (smoothField_continuous period F hFs)).isBounded
  obtain ⟨M, hM, hbound⟩ := hFb.exists_pos_norm_le
  refine ⟨⟨M, hM.le⟩, fun x y => ?_⟩
  have hBy := hbound (F (x.1 + y.1, x.2 + (y.2 : AddCircle period))) (Set.mem_range_self _)
  change ‖fderiv ℝ (localFieldLift period (fieldFDeriv period f)
    (x.1 + y.1, x.2 + (y.2 : AddCircle period))) 0‖ ≤ M at hBy
  rw [fderiv_localFieldLift_shift, localFieldLift_fieldFDeriv] at hBy
  exact hBy

end FieldCalculus

omit [Fact (0 < period)] in
theorem translationPath_continuous (a : LiftTangent) : Continuous (translationPath period a) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp
    (continuous_id.smul continuous_const)

omit [Fact (0 < period)] in
theorem translationPath_add (a : LiftTangent) (s t : ℝ) :
    translationPath period a (s + t) = translationPath period a s + translationPath period a t := by
  simp [translationPath, coveringMap, add_smul]

omit [Fact (0 < period)] in
theorem translationPath_neg (a : LiftTangent) (t : ℝ) :
    translationPath period a (-t) = -translationPath period a t := by
  simp [translationPath, coveringMap]

theorem translation_pairing (a : LiftDomain period) (f g : LiftL2 period) :
    ⟪translation period a f, g⟫_ℝ = ⟪f, translation period (-a) g⟫_ℝ := by
  have hi := (translation period a).inner_map_map f (translation period (-a) g)
  simpa only [translation_add, add_neg_cancel, translation_zero] using hi

omit [Fact (0 < period)] in
theorem compact_translation_support (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f) :
    ∃ K : Set (LiftDomain period), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x ∉ K, f (x + translationPath period a t) = 0 := by
  let K := (fun p : LiftDomain period × ℝ => p.1 - translationPath period a p.2) ''
    (tsupport f ×ˢ Set.Icc (-1 : ℝ) 1)
  have hK : IsCompact K := (hfc.isCompact.prod isCompact_Icc).image
    (continuous_fst.sub ((translationPath_continuous period a).comp continuous_snd))
  refine ⟨K, hK, ?_, ?_⟩
  · intro x hx
    refine ⟨(x, 0), ⟨hx, by constructor <;> norm_num⟩, ?_⟩
    simp
  · intro t ht x hx
    by_contra hn
    apply hx
    refine ⟨(x + translationPath period a t, t),
      ⟨subset_tsupport f (Function.mem_support.mpr hn), abs_le.mp ht⟩, ?_⟩
    simp

/-- The actual L² element represented by a smooth compact vector field. -/
def smoothFieldLp (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) : LiftL2 period :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).toLp f

theorem smoothFieldLp_ae (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    smoothFieldLp period f hfc hf =ᵐ[liftMeasure period] f :=
  ((smoothField_continuous period f hf).memLp_of_hasCompactSupport hfc).coeFn_toLp

/-- The L² element represented by the actual directional derivative of a compact test field. -/
def derivativeFieldLp (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    LiftL2 period := (fieldDerivative_memLp period a f hfc hf).toLp (fieldDerivative period a f)

theorem derivativeFieldLp_ae (a : LiftTangent) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    derivativeFieldLp period a f hfc hf =ᵐ[liftMeasure period] fieldDerivative period a f :=
  (fieldDerivative_memLp period a f hfc hf).coeFn_toLp

omit [Fact (0 < period)] in
theorem field_translation_remainder (a : LiftTangent)
    (f : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (M : ℝ≥0)
    (hDD : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period f x)) y‖ ≤ M)
    (t : ℝ) (x : LiftDomain period) :
    ‖f (x + translationPath period a t) - f x - t • fieldDerivative period a f x‖ ≤
      (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => localFieldLift period f x (u • a))
      (fderiv ℝ (localFieldLift period f x) (s • a) a) s := by
    intro s
    have hF := (((hf x).differentiable (by simp)) (s • a)).hasFDerivAt
    convert hF.comp_hasDerivAt s ((hasDerivAt_id s).smul_const a) using 1 <;>
      first | rfl | simp
  have hr := uniform_derivative_remainder
    (fun s => localFieldLift period f x (s • a))
    (fun s => fderiv ℝ (localFieldLift period f x) (s • a) a) hd (M * ‖a‖₊ ^ 2)
    (fun s => by simpa only [zero_smul, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      directionalDerivative_line_lipschitz (localFieldLift period f x) (hf x) M (hDD x) a s) t
  change ‖f (x.1 + (t • a).1, x.2 + ((t • a).2 : AddCircle period)) - f x -
    t • fieldDerivative period a f x‖ ≤ _
  simpa only [localFieldLift, zero_smul, Prod.fst_zero, Prod.snd_zero,
    AddCircle.coe_zero, add_zero, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
    fieldDerivative] using hr

theorem smoothFieldLp_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (smoothFieldLp period f hfc hf)) (derivativeFieldLp period a f hfc hf) 0 := by
  obtain ⟨M, hM⟩ := compact_smooth_second_derivative_bound period f hfc hf
  obtain ⟨K, hK, hKf, hKshift⟩ := compact_translation_support period a f hfc
  let f₀ := smoothFieldLp period f hfc hf
  let df := derivativeFieldLp period a f hfc hf
  let χ : Lp ℝ 2 (liftMeasure period) :=
    indicatorConstLp 2 hK.isClosed.measurableSet hK.measure_ne_top (1 : ℝ)
  have hR : ∀ t : ℝ, |t| ≤ 1 →
      ‖translation period (translationPath period a t) f₀ - f₀ - t • df‖ ≤
        ((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖ := by
    intro t ht
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [translation_ae period (translationPath period a t) f₀,
      (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae
        (smoothFieldLp_ae period f hfc hf), smoothFieldLp_ae period f hfc hf,
      derivativeFieldLp_ae period a f hfc hf,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀) f₀,
      Lp.coeFn_smul t df,
      Lp.coeFn_sub (translation period (translationPath period a t) f₀ - f₀) (t • df),
      (indicatorConstLp_coeFn (p := 2) (hs := hK.isClosed.measurableSet)
        (hμs := hK.measure_ne_top) (c := (1 : ℝ)))]
      with x hτ hfx hf₀ hdf hsub hsmul hrem hχ
    simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hrem
    rw [hrem, hsub, hsmul, hτ, hfx, hf₀, hdf]
    change ‖f (x + translationPath period a t) - f x -
      t • fieldDerivative period a f x‖ ≤ (M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2 * ‖χ x‖
    change χ x = _ at hχ
    rw [hχ]
    by_cases hx : x ∈ K
    · simpa only [Set.indicator_of_mem hx, norm_one, mul_one] using
        field_translation_remainder period a f hf M hM t x
    · have hxf : x ∉ tsupport f := fun h => hx (hKf h)
      have hdz : fieldDerivative period a f x = 0 := by
        change fieldFDeriv period f x a = 0
        rw [fieldFDeriv_zero_outside period f x hxf]
        rfl
      rw [hKshift t ht x hx, image_eq_zero_of_notMem_tsupport hxf, hdz,
        Set.indicator_of_notMem hx]
      simp
  apply (hasDerivAt_iff_tendsto
    (f := fun t => translation period (translationPath period a t) f₀)
    (f' := df) (x := (0 : ℝ))).mpr
  simp only [translationPath_zero, translation_zero, sub_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t => by positivity
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    have ht' : |t| ≤ 1 := by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht.le
    calc
      _ ≤ ‖t‖⁻¹ * (((M : ℝ) * ‖a‖ ^ 2 * |t| ^ 2) * ‖χ‖) :=
        mul_le_mul_of_nonneg_left (hR t ht') (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ((M : ℝ) * ‖a‖ ^ 2 * ‖χ‖) * |t| := by
        by_cases ht0 : t = 0
        · simp [ht0]
        · rw [Real.norm_eq_abs]
          have hta : |t| ≠ 0 := abs_ne_zero.mpr ht0
          field_simp
          ring_nf
          exact le_rfl
  · simpa only [Pi.mul_def, abs_zero, mul_zero] using
      (continuous_const.mul continuous_abs).tendsto (0 : ℝ)

theorem translation_derivative_pairing (a : LiftTangent) (f f' g g' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (hg : HasDerivAt (fun t => translation period (translationPath period a t) g) g' 0) :
    ⟪f', g⟫_ℝ = -⟪f, g'⟫_ℝ := by
  have hleft : HasDerivAt (fun t =>
      ⟪translation period (translationPath period a t) f, g⟫_ℝ) ⟪f', g⟫_ℝ 0 := by
    simpa only [translationPath_zero, translation_zero, inner_zero_right, zero_add] using
      hf.inner ℝ (hasDerivAt_const (0 : ℝ) g)
  have hneg : HasDerivAt (fun t => translation period (translationPath period a (-t)) g) (-g') 0 := by
    convert hg.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp) using 1 <;>
      first | rfl | simp
  have hright : HasDerivAt (fun t =>
      ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ) (-⟪f, g'⟫_ℝ) 0 := by
    simpa only [inner_neg_right, inner_zero_left, add_zero] using
      (hasDerivAt_const (0 : ℝ) f).inner ℝ hneg
  have heq : (fun t => ⟪translation period (translationPath period a t) f, g⟫_ℝ) =
      fun t => ⟪f, translation period (translationPath period a (-t)) g⟫_ℝ := by
    funext t
    simpa only [translationPath_neg] using
      translation_pairing period (translationPath period a t) f g
  rw [heq] at hleft
  exact hleft.unique hright

/-- A strong L² translation derivative is the actual distributional derivative. -/
theorem strong_translation_derivative_weak (a : LiftTangent) (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0)
    (φ : LiftDomain period → Vector3) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) :
    (∫ x, ⟪f' x, φ x⟫_ℝ ∂liftMeasure period) =
      -(∫ x, ⟪f x, fieldDerivative period a φ x⟫_ℝ ∂liftMeasure period) := by
  have hp := translation_derivative_pairing period a f f'
    (smoothFieldLp period φ hφc hφ) (derivativeFieldLp period a φ hφc hφ) hf
    (smoothFieldLp_translation_hasDerivAt period a φ hφc hφ)
  calc
    _ = ⟪f', smoothFieldLp period φ hφc hφ⟫_ℝ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [smoothFieldLp_ae period φ hφc hφ] with x hx
      rw [hx]
    _ = -⟪f, derivativeFieldLp period a φ hφc hφ⟫_ℝ := hp
    _ = _ := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivativeFieldLp_ae period a φ hφc hφ] with x hx
      rw [hx]

theorem divergenceFree_translation_mem (κ : ℝ) (m : Vector3) (a : LiftDomain period)
    {f : LiftL2 period} (hf : f ∈ divergenceFreeSpace period κ m) :
    translation period a f ∈ divergenceFreeSpace period κ m := by
  intro g hg
  rw [real_inner_comm, translation_pairing, real_inner_comm]
  exact hf (translation period (-a) g) (gradientSpace_translation_mem period κ m (-a) hg)

theorem divergenceFree_translation_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    {f f' : LiftL2 period} (hf : f ∈ divergenceFreeSpace period κ m)
    (hder : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    f' ∈ divergenceFreeSpace period κ m := by
  have hlim := hder.tendsto_slope_zero
  simp only [zero_add, translationPath_zero, translation_zero] at hlim
  apply (gradientSpace period κ m).isClosed_orthogonal.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun t => (divergenceFreeSpace period κ m).smul_mem _
    ((divergenceFreeSpace period κ m).sub_mem
      (divergenceFree_translation_mem period κ m (translationPath period a t) hf) hf)

theorem pressure_has_weak_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    (A : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hAs : ∀ x, ContDiff ℝ ∞ (localFieldLift period A x))
    (C D M : ℝ≥0) (hAb : ∀ x, ‖A x‖ ≤ C)
    (hDA : ∀ x, ‖fderiv ℝ (localFieldLift period A x) 0‖ ≤ D)
    (hDDA : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period A x)) y‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    ∃ p' : LiftL2 period,
      HasDerivAt (fun t => translation period (translationPath period a t)
        (liftedPressure period κ m A hA C hAb c hc hpos f)) p' 0 ∧
      p' ∈ gradientSpace period κ m ∧
      ‖p'‖ ≤ c⁻¹ * (‖f'‖ + (D : ℝ) * ‖a‖ *
        ‖liftedPressure period κ m A hA C hAb c hc hpos f‖) ∧
      ∀ (φ : LiftDomain period → Vector3), HasCompactSupport φ →
        (∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) →
        (∫ x, ⟪p' x, φ x⟫_ℝ ∂liftMeasure period) =
          -(∫ x, ⟪(liftedPressure period κ m A hA C hAb c hc hpos f) x,
            fieldDerivative period a φ x⟫_ℝ ∂liftMeasure period) := by
  let p := liftedPressure period κ m A hA C hAb c hc hpos f
  let p' := liftedPressure period κ m A hA C hAb c hc hpos
    (f' - EulerLiftedPressure.coefficientOperator (translatedCoefficientDerivative period a A 0)
      (translatedCoefficientDerivative_measurable period a A hAs) (D * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A D hDA x) p)
  have hpd : HasDerivAt (fun t => translation period (translationPath period a t) p) p' 0 :=
    pressure_translation_hasDerivAt period κ m a A hA hAs C D M hAb hDA hDDA
      c hc hpos f f' hf
  refine ⟨p', hpd, liftedPressure_mem period κ m A hA C hAb c hc hpos _, ?_, ?_⟩
  · have hn := pressure_translation_derivative_norm period κ m a A hA hAs C D M hAb hDA hDDA
      c hc hpos f f' hf
    rwa [hpd.deriv] at hn
  · intro φ hφc hφ
    exact strong_translation_derivative_weak period a p p' hpd φ hφc hφ

end EulerLiftedWeakDerivative

end

section

/-!
Finite spatial Sobolev jets in the actual lifted L² space.  Jet entries are
actual strong translation derivatives and therefore genuine weak derivatives.
The pressure jet is constructed, rather than assumed, from coercivity and
pointwise smooth coefficient data.
-/


namespace EulerSpatialSobolevInverse


open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerTransportDerivatives EulerPressureSpatialRegularity
  EulerLiftedWeakDerivative EulerCoerciveProjection
open scoped ContDiff ENNReal NNReal Topology

/-- The existing Mathlib normed group instance for matrix coefficients, named to keep inference shallow. -/
local instance coefficientValueNormedGroup : NormedAddCommGroup (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for matrix coefficients. -/
local instance coefficientValueNormedSpace : NormedSpace ℝ (Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace

/-- The existing Mathlib normed group instance for first coefficient derivatives. -/
local instance coefficientFirstNormedGroup :
    NormedAddCommGroup (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The existing Mathlib real normed-space instance for first coefficient derivatives. -/
local instance coefficientFirstNormedSpace :
    NormedSpace ℝ (LiftTangent →L[ℝ] Vector3 →L[ℝ] Vector3) :=
  ContinuousLinearMap.toNormedSpace


variable (period : ℝ) [Fact (0 < period)]

/-- A bounded smooth pointwise coefficient field with quantitative first and second derivatives. -/
structure SmoothCoefficient where
  /-- The actual pointwise coefficient matrix field. -/
  coefficient : LiftDomain period → Vector3 →L[ℝ] Vector3
  smooth : ∀ x, ContDiff ℝ ∞ (localFieldLift period coefficient x)
  /-- A uniform operator-norm bound for the coefficient field. -/
  bound : ℝ≥0
  norm_bound : ∀ x, ‖coefficient x‖ ≤ bound
  /-- A uniform norm bound for the first covering derivative. -/
  firstBound : ℝ≥0
  norm_first : ∀ x, ‖fderiv ℝ (localFieldLift period coefficient x) 0‖ ≤ firstBound
  /-- A uniform norm bound for the second covering derivative. -/
  secondBound : ℝ≥0
  norm_second : ∀ x y, ‖fderiv ℝ (fderiv ℝ (localFieldLift period coefficient x)) y‖ ≤ secondBound

namespace SmoothCoefficient

variable {period}

theorem measurable (A : SmoothCoefficient period) :
    AEStronglyMeasurable A.coefficient (liftMeasure period) :=
  (smoothField_continuous period A.coefficient A.smooth).aestronglyMeasurable

/-- Actual multiplication by the coefficient field in L². -/
def operator (A : SmoothCoefficient period) : LiftL2 period →L[ℝ] LiftL2 period :=
  coefficientOperator A.coefficient A.measurable A.bound A.norm_bound

theorem operator_ae (A : SmoothCoefficient period) (f : LiftL2 period) :
    A.operator f =ᵐ[liftMeasure period] fun x => A.coefficient x (f x) :=
  coefficientOperator_ae A.coefficient A.measurable A.bound A.norm_bound f

theorem operator_norm (A : SmoothCoefficient period) (f : LiftL2 period) :
    ‖A.operator f‖ ≤ A.bound * ‖f‖ :=
  coefficientApply_norm_le A.coefficient A.measurable A.bound A.norm_bound f

/-- The Lax–Milgram pressure associated with this actual coefficient. -/
def pressure (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f : LiftL2 period) : LiftL2 period :=
  liftedPressure period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f

theorem pressure_norm (A : SmoothCoefficient period) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (f : LiftL2 period) :
    ‖A.pressure κ m c hc hpos f‖ ≤ c⁻¹ * ‖f‖ :=
  pressureSolver_apply_norm_le (gradientSpace period κ m) A.operator c hc
    (coefficientOperator_coercive A.coefficient A.measurable A.bound A.norm_bound c hpos) f

theorem derivative_operator_eq (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x) :
    coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) = B.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coefficientOperator_ae (translatedCoefficientDerivative period a A.coefficient 0)
      (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
      (A.firstBound * ‖a‖₊)
      (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
        A.norm_first x) f, B.operator_ae f] with x hx hy
  rw [hx, hy, hB]
  simp [translatedCoefficientDerivative, fieldDerivative]

theorem operator_translation_hasDerivAt (A : SmoothCoefficient period) (a : LiftTangent) :
    HasDerivAt (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t)))
      (coefficientOperator (translatedCoefficientDerivative period a A.coefficient 0)
        (translatedCoefficientDerivative_measurable period a A.coefficient A.smooth)
        (A.firstBound * ‖a‖₊)
        (fun x => translatedCoefficientDerivative_bound period a A.coefficient A.firstBound
          A.norm_first x)) 0 := by
  apply coefficientOperator_hasDerivAt
    (A' := translatedCoefficientDerivative period a A.coefficient)
    (L := A.secondBound * ‖a‖₊ ^ 2)
  · exact translatedCoefficient_hasDerivAt period a A.coefficient A.smooth
  · intro t x
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] using
      translatedCoefficientDerivative_lipschitz period a A.coefficient A.smooth
        A.secondBound A.norm_second t x

theorem product_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t) (A.operator f))
      (A.operator f' + B.operator f) 0 := by
  have hprod := (A.operator_translation_hasDerivAt a).clm_apply hf
  rw [A.derivative_operator_eq B a hB] at hprod
  have hcov : (fun t => coefficientOperator
      (translatedCoefficient period (translationPath period a t) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a t) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a t))
      (translation period (translationPath period a t) f)) =
      fun t => translation period (translationPath period a t) (A.operator f) := by
    funext t
    exact (coefficientOperator_translation period (translationPath period a t) A.coefficient
      A.measurable A.bound A.norm_bound f).symm
  rw [hcov] at hprod
  have hop0 : coefficientOperator
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) = A.operator := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    filter_upwards [coefficientOperator_ae
      (translatedCoefficient period (translationPath period a 0) A.coefficient)
      (translatedCoefficient_measurable period (translationPath period a 0) A.coefficient A.measurable)
      A.bound (fun x => A.norm_bound (x + translationPath period a 0)) u,
      A.operator_ae u] with x hx hy
    rw [hx, hy]
    simp [translatedCoefficient]
  rw [hop0] at hprod
  simp only [translationPath_zero, translation_zero] at hprod
  convert hprod using 1 <;> first | rfl | exact add_comm _ _

theorem pressure_hasDerivAt (A B : SmoothCoefficient period) (a : LiftTangent)
    (hB : ∀ x, B.coefficient x = fieldDerivative period a A.coefficient x)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (f f' : LiftL2 period)
    (hf : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (A.pressure κ m c hc hpos f))
      (A.pressure κ m c hc hpos (f' - B.operator (A.pressure κ m c hc hpos f))) 0 := by
  have hp := pressure_translation_hasDerivAt period κ m a A.coefficient A.measurable A.smooth
    A.bound A.firstBound A.secondBound A.norm_bound A.norm_first A.norm_second c hc hpos f f' hf
  rwa [A.derivative_operator_eq B a hB] at hp

end SmoothCoefficient

/-- A finite tree of actual strong translation derivatives of an L² field. -/
inductive SpatialJet (directions : Fin 4 → LiftTangent) : ℕ → LiftL2 period → Type
  | zero (f : LiftL2 period) : SpatialJet directions 0 f
  | succ {n : ℕ} {f : LiftL2 period} (derivatives : Fin 4 → LiftL2 period)
      (lower : ∀ i, SpatialJet directions n (derivatives i))
      (hasDeriv : ∀ i, HasDerivAt (fun t => translation period
        (translationPath period (directions i) t) f) (derivatives i) 0) :
      SpatialJet directions (n + 1) f

/-- A finite tree of actual coefficient derivatives, with bounded smooth data at every node. -/
inductive CoefficientJet (directions : Fin 4 → LiftTangent) : ℕ → SmoothCoefficient period → Type
  | zero (A : SmoothCoefficient period) : CoefficientJet directions 0 A
  | succ {n : ℕ} {A : SmoothCoefficient period} (derivatives : Fin 4 → SmoothCoefficient period)
      (lower : ∀ i, CoefficientJet directions n (derivatives i))
      (derivative_eq : ∀ i x, (derivatives i).coefficient x =
        fieldDerivative period (directions i) A.coefficient x) :
      CoefficientJet directions (n + 1) A

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative order of a genuine spatial jet. -/
def truncate {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions (n + 1) f) :
    SpatialJet period directions n f :=
  match n, J with
  | 0, _ => .zero f
  | _n + 1, .succ df lower hd => .succ df (fun i => (lower i).truncate) hd

/-- The sum of all derivative-word L² norms represented by the jet. -/
def sobolevNorm {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) : ℝ :=
  match J with
  | .zero f => ‖f‖
  | .succ _ lower _ => ‖f‖ + ∑ i, (lower i).sobolevNorm

theorem nonneg {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    0 ≤ J.sobolevNorm := by
  induction J with
  | zero f => exact norm_nonneg f
  | succ df lower hd ih =>
    exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => ih i)

theorem value_norm_le {n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions n f) :
    ‖f‖ ≤ J.sobolevNorm := by
  cases J with
  | zero => exact le_rfl
  | succ df lower hd =>
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (lower i).nonneg)

theorem truncate_norm_le {n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (n + 1) f) :
    J.truncate.sobolevNorm ≤ J.sobolevNorm := by
  induction n generalizing f with
  | zero => exact J.value_norm_le
  | succ n ih =>
    cases J with
    | succ df lower hd =>
      exact add_le_add_right (Finset.sum_le_sum fun i _ => ih (lower i)) ‖f‖

theorem lower_norm_le {n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions n (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (i : Fin 4) :
    (lower i).sobolevNorm ≤ (SpatialJet.succ df lower hd).sobolevNorm := by
  exact (Finset.single_le_sum (fun j _ => (lower j).nonneg) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (norm_nonneg f))

/-- Addition preserves the actual strong derivatives recorded in a spatial jet. -/
def add {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f + g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f + g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i + dg i) (fun i => (Jd i).add (Kd i)) (fun i => by
      convert (hJ i).add (hK i) using 1 <;> first | rfl | (funext t; simp))

/-- Subtraction preserves the actual strong derivatives recorded in a spatial jet. -/
def sub {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    SpatialJet period directions n (f - g) :=
  match J, K with
  | .zero _, .zero _ => .zero (f - g)
  | .succ df Jd hJ, .succ dg Kd hK =>
    .succ (fun i => df i - dg i) (fun i => (Jd i).sub (Kd i)) (fun i => by
      convert (hJ i).sub (hK i) using 1 <;> first | rfl | (funext t; simp))

theorem add_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.add K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_add_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f + g‖ + ∑ i, ((Jd i).add (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_add_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

theorem sub_norm_le {n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions n f) (K : SpatialJet period directions n g) :
    (J.sub K).sobolevNorm ≤ J.sobolevNorm + K.sobolevNorm := by
  induction n generalizing f g with
  | zero => cases J; cases K; exact norm_sub_le _ _
  | succ n ih =>
    cases J with
    | succ df Jd hJ =>
      cases K with
      | succ dg Kd hK =>
        change ‖f - g‖ + ∑ i, ((Jd i).sub (Kd i)).sobolevNorm ≤ _
        calc
          _ ≤ (‖f‖ + ‖g‖) + ∑ i, ((Jd i).sobolevNorm + (Kd i).sobolevNorm) :=
            add_le_add (norm_sub_le _ _) (Finset.sum_le_sum fun i _ => ih (Jd i) (Kd i))
          _ = _ := by simp only [Finset.sum_add_distrib, sobolevNorm]; ring

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Forget the highest derivative level while retaining the original coefficient. -/
def truncate {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions (n + 1) A) : CoefficientJet period directions n A :=
  match n, J with
  | 0, _ => .zero A
  | _n + 1, .succ dA lower hd => .succ dA (fun i => (lower i).truncate) hd

/-- A finite polynomial bound for multiplication in the jet Sobolev norm. -/
def productConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : ℝ :=
  match J with
  | .zero A => A.bound
  | .succ dA lower hd => A.bound + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.productConstant + (lower i).productConstant)
termination_by n

omit [Fact (0 < period)] in
theorem productConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) : 0 ≤ J.productConstant := by
  induction n generalizing A with
  | zero => cases J; rw [productConstant]; exact NNReal.coe_nonneg _
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [productConstant]
      exact add_nonneg A.bound.coe_nonneg (Finset.sum_nonneg fun i _ =>
        add_nonneg (ih (CoefficientJet.succ dA lower hd).truncate) (ih (lower i)))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct every finite-order derivative of actual coefficient multiplication. -/
def multiply {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.operator f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.operator f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    .succ (fun i => A.operator (df i) + (dA i).operator f)
      (fun i => (multiply (CoefficientJet.succ dA KA hA).truncate (Jf i)).add
        (multiply (KA i) (SpatialJet.succ df Jf hf).truncate))
      (fun i => A.product_hasDerivAt (dA i) (directions i) (hA i) f (df i) (hf i))
termination_by n

theorem multiply_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (J : SpatialJet period directions n f) :
    (multiply K J).sobolevNorm ≤ K.productConstant * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [multiply, sobolevNorm, CoefficientJet.productConstant] using A.operator_norm f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hterms : ∀ i,
            ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤
              (K₀.productConstant + (KA i).productConstant) * N := by
          intro i
          calc
            _ ≤ (multiply K₀ (Jf i)).sobolevNorm + (multiply (KA i) J₀).sobolevNorm :=
              add_norm_le _ _
            _ ≤ K₀.productConstant * (Jf i).sobolevNorm +
                (KA i).productConstant * J₀.sobolevNorm := add_le_add (ih K₀ (Jf i)) (ih (KA i) J₀)
            _ ≤ K₀.productConstant * N + (KA i).productConstant * N :=
              add_le_add (mul_le_mul_of_nonneg_left (hkid i) K₀.productConstant_nonneg)
                (mul_le_mul_of_nonneg_left hlow (KA i).productConstant_nonneg)
            _ = _ := by ring
        rw [multiply, sobolevNorm]
        change ‖A.operator f‖ + ∑ i,
          ((multiply K₀ (Jf i)).add (multiply (KA i) J₀)).sobolevNorm ≤ _
        calc
          _ ≤ A.bound * N + ∑ i, (K₀.productConstant + (KA i).productConstant) * N :=
            add_le_add ((A.operator_norm f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le A.bound.coe_nonneg))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.productConstant]

end SpatialJet

namespace CoefficientJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- The explicit finite-order inverse constant obtained from coercivity and coefficient products. -/
def pressureConstant {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) : ℝ :=
  match J with
  | .zero _ => c⁻¹
  | .succ dA lower hd => c⁻¹ + ∑ i : Fin 4,
      ((CoefficientJet.succ dA lower hd).truncate.pressureConstant c *
        (1 + (lower i).productConstant *
          (CoefficientJet.succ dA lower hd).truncate.pressureConstant c))
termination_by n

omit [Fact (0 < period)] in
theorem pressureConstant_nonneg {n : ℕ} {A : SmoothCoefficient period}
    (J : CoefficientJet period directions n A) (c : ℝ) (hc : 0 < c) :
    0 ≤ J.pressureConstant c := by
  induction n generalizing A with
  | zero => cases J; rw [pressureConstant]; exact inv_nonneg.mpr hc.le
  | succ n ih =>
    cases J with
    | succ dA lower hd =>
      rw [pressureConstant]
      exact add_nonneg (inv_nonneg.mpr hc.le) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (ih (CoefficientJet.succ dA lower hd).truncate)
          (add_nonneg zero_le_one (mul_nonneg (lower i).productConstant_nonneg
            (ih (CoefficientJet.succ dA lower hd).truncate))))

end CoefficientJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Construct a genuine pressure Sobolev jet at every finite order. -/
def solvePressure {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    SpatialJet period directions n (A.pressure κ m c hc hpos f) :=
  match n, K, J with
  | 0, .zero _, .zero _ => .zero (A.pressure κ m c hc hpos f)
  | _n + 1, .succ dA KA hA, .succ df Jf hf =>
    let K₀ := (CoefficientJet.succ dA KA hA).truncate
    let J₀ := (SpatialJet.succ df Jf hf).truncate
    let P₀ := solvePressure K₀ κ m c hc hpos J₀
    .succ (fun i => A.pressure κ m c hc hpos
        (df i - (dA i).operator (A.pressure κ m c hc hpos f)))
      (fun i => solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀)))
      (fun i => A.pressure_hasDerivAt (dA i) (directions i) (hA i)
        κ m c hc hpos f (df i) (hf i))
termination_by n

theorem solvePressure_norm_le {n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions n A) (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (J : SpatialJet period directions n f) :
    (solvePressure K κ m c hc hpos J).sobolevNorm ≤ K.pressureConstant c * J.sobolevNorm := by
  induction n generalizing A f with
  | zero =>
    cases K; cases J
    simpa only [solvePressure, sobolevNorm, CoefficientJet.pressureConstant] using
      A.pressure_norm κ m c hc hpos f
  | succ n ih =>
    cases K with
    | succ dA KA hA =>
      cases J with
      | succ df Jf hf =>
        let K₀ := (CoefficientJet.succ dA KA hA).truncate
        let J₀ := (SpatialJet.succ df Jf hf).truncate
        let P₀ := solvePressure K₀ κ m c hc hpos J₀
        let N := (SpatialJet.succ df Jf hf).sobolevNorm
        have hlow : J₀.sobolevNorm ≤ N := (SpatialJet.succ df Jf hf).truncate_norm_le
        have hkid : ∀ i, (Jf i).sobolevNorm ≤ N := lower_norm_le df Jf hf
        have hp : P₀.sobolevNorm ≤ K₀.pressureConstant c * N :=
          (ih K₀ hpos J₀).trans
            (mul_le_mul_of_nonneg_left hlow (K₀.pressureConstant_nonneg c hc))
        have hterms : ∀ i,
            (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N := by
          intro i
          calc
            _ ≤ K₀.pressureConstant c * ((Jf i).sub (multiply (KA i) P₀)).sobolevNorm :=
              ih K₀ hpos _
            _ ≤ K₀.pressureConstant c * ((Jf i).sobolevNorm + (multiply (KA i) P₀).sobolevNorm) :=
              mul_le_mul_of_nonneg_left (sub_norm_le _ _) (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * P₀.sobolevNorm) :=
              mul_le_mul_of_nonneg_left (add_le_add (hkid i) (multiply_norm_le (KA i) P₀))
                (K₀.pressureConstant_nonneg c hc)
            _ ≤ K₀.pressureConstant c * (N + (KA i).productConstant * (K₀.pressureConstant c * N)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add_right (mul_le_mul_of_nonneg_left hp (KA i).productConstant_nonneg) N)
                (K₀.pressureConstant_nonneg c hc)
            _ = _ := by ring
        rw [solvePressure, sobolevNorm]
        change ‖A.pressure κ m c hc hpos f‖ + ∑ i,
          (solvePressure K₀ κ m c hc hpos ((Jf i).sub (multiply (KA i) P₀))).sobolevNorm ≤ _
        calc
          _ ≤ c⁻¹ * N + ∑ i,
              (K₀.pressureConstant c * (1 + (KA i).productConstant * K₀.pressureConstant c)) * N :=
            add_le_add ((A.pressure_norm κ m c hc hpos f).trans
              (mul_le_mul_of_nonneg_left (SpatialJet.succ df Jf hf).value_norm_le (inv_nonneg.mpr hc.le)))
              (Finset.sum_le_sum fun i _ => hterms i)
          _ = _ := by
            rw [← Finset.sum_mul, ← add_mul, CoefficientJet.pressureConstant]

end SpatialJet

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- A derivative word, ordered with its head differentiated last; invalid orders return zero. -/
def word {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    {n : ℕ} (w : Fin n → Fin 4) : LiftL2 period :=
  match n, J with
  | 0, _ => f
  | _n + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => (lower (w (Fin.last n))).word (Fin.init w)
termination_by s

@[simp]
theorem word_zero {s : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f)
    (w : Fin 0 → Fin 4) : J.word w = f := by rw [word]

@[simp]
theorem word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) (w : Fin (n + 1) → Fin 4) :
    (SpatialJet.succ df lower hd).word w = (lower (w (Fin.last n))).word (Fin.init w) := by
  rw [word]

theorem word_hasDerivAt {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (hn : n < s) (w : Fin n → Fin 4) (i : Fin 4) :
    HasDerivAt (fun t => translation period (translationPath period (directions i) t) (J.word w))
      (J.word (Fin.cons i w)) 0 := by
  induction n generalizing s f with
  | zero =>
    cases J with
    | zero => omega
    | succ df lower hd => simpa using hd i
  | succ n ih =>
    cases J with
    | zero => omega
    | succ df lower hd =>
      have h := ih (lower (w (Fin.last n))) (by omega) (Fin.init w)
      have hi : Fin.init (n := n + 1) (α := fun _ : Fin (n + 2) => Fin 4)
          (Fin.cons (α := fun _ : Fin (n + 2) => Fin 4) i w) =
          Fin.cons (α := fun _ : Fin (n + 1) => Fin 4) i (Fin.init w) := by
        funext j
        cases j using Fin.cases <;> rfl
      simp only [word_succ, hi]
      convert h using 1
      rfl

/-- Split a coordinate word into its last direction and its initial word. -/
def wordSnocEquiv (n : ℕ) : (Fin (n + 1) → Fin 4) ≃ Fin 4 × (Fin n → Fin 4) where
  toFun w := (w (Fin.last n), Fin.init w)
  invFun v := Fin.snoc v.2 v.1
  left_inv w := Fin.snoc_init_self w
  right_inv v := by simp

/-- The sum over words of positive length is the sum over final directions and initial words. -/
theorem sum_word_succ {s n : ℕ} {f : LiftL2 period} (df : Fin 4 → LiftL2 period)
    (lower : ∀ i, SpatialJet period directions s (df i))
    (hd : ∀ i, HasDerivAt (fun t => translation period
      (translationPath period (directions i) t) f) (df i) 0) :
    (∑ w : Fin (n + 1) → Fin 4, ‖(SpatialJet.succ df lower hd).word w‖) =
      ∑ i, ∑ w : Fin n → Fin 4, ‖(lower i).word w‖ := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), ‖(lower v.1).word v.2‖ :=
      Fintype.sum_equiv (wordSnocEquiv n)
        (fun w => ‖(SpatialJet.succ df lower hd).word w‖)
        (fun v => ‖(lower v.1).word v.2‖) (fun _ => by rw [word_succ]; rfl)
    _ = _ := Fintype.sum_prod_type _

/-- The recursive jet norm equals the explicit sum of the norms of all coordinate words. -/
theorem sobolevNorm_eq_sum_words {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) :
    J.sobolevNorm = ∑ n ∈ Finset.range (s + 1), ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction s generalizing f with
  | zero => cases J; simp [sobolevNorm]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      rw [sobolevNorm, Finset.sum_range_succ']
      simp only [word_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, pow_zero, one_smul]
      simp_rw [sum_word_succ]
      rw [Finset.sum_comm]
      simp_rw [← ih]
      exact add_comm _ _

end SpatialJet

end EulerSpatialSobolevInverse

end

section

/-!
The closed lifted gradient space consists of distributionally curl-free
fields.  The proof uses actual compact scalar tests and mixed derivative
symmetry, then passes to the L² closure through continuous inner products.
-/


namespace EulerLiftedCurl

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerPressureSpatialRegularity EulerLiftedWeakDerivative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Isometric inclusion of a scalar into the first Euclidean component. -/
def scalarEmbedding : ℝ →L[ℝ] Vector3 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 3) 1)

omit [Fact (0 < period)] in
theorem scalarEmbedding_inner (r s : ℝ) :
    ⟪scalarEmbedding r, scalarEmbedding s⟫_ℝ = r * s := by
  simp [scalarEmbedding, inner_smul_left, inner_smul_right, mul_comm]

omit [Fact (0 < period)] in
theorem fieldDerivative_linear {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (f : LiftDomain period → V) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (a : LiftTangent) (x : LiftDomain period) :
    fieldDerivative period a (fun y => L (f y)) x = L (fieldDerivative period a f x) := by
  have hd := L.hasFDerivAt.comp (0 : LiftTangent)
    (((hf x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun D : LiftTangent →L[ℝ] W => D a) hd.fderiv
  exact he

omit [Fact (0 < period)] in
theorem scalar_embedding_smooth (φ : LiftDomain period → ℝ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fun y => scalarEmbedding (φ y)) x) :=
  scalarEmbedding.contDiff.comp (hφ x)

omit [Fact (0 < period)] in
theorem scalar_embedding_compact (φ : LiftDomain period → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun x => scalarEmbedding (φ x)) := by
  apply hφ.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  rw [hx, map_zero]

/-- Genuine scalar integration by parts on the cylinder in any constant covering direction. -/
theorem scalar_integration_by_parts (a : LiftTangent) (φ ψ : LiftDomain period → ℝ)
    (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    (∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period) =
      -(∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period) := by
  let F := fun x => scalarEmbedding (φ x)
  let G := fun x => scalarEmbedding (ψ x)
  let hFc := scalar_embedding_compact period φ hφc
  let hGc := scalar_embedding_compact period ψ hψc
  let hFs := scalar_embedding_smooth period φ hφ
  let hGs := scalar_embedding_smooth period ψ hψ
  have hi := strong_translation_derivative_weak period a
    (smoothFieldLp period F hFc hFs) (derivativeFieldLp period a F hFc hFs)
    (smoothFieldLp_translation_hasDerivAt period a F hFc hFs) G hGc hGs
  have hleft : (∫ x, ⟪(derivativeFieldLp period a F hFc hFs) x, G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, fieldDerivative period a φ x * ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [derivativeFieldLp_ae period a F hFc hFs] with x hx
    rw [hx]
    change ⟪fieldDerivative period a (fun y => scalarEmbedding (φ y)) x,
      scalarEmbedding (ψ x)⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding φ hφ, scalarEmbedding_inner]
  have hright : (∫ x, ⟪(smoothFieldLp period F hFc hFs) x, fieldDerivative period a G x⟫_ℝ
      ∂liftMeasure period) = ∫ x, φ x * fieldDerivative period a ψ x ∂liftMeasure period := by
    apply integral_congr_ae
    filter_upwards [smoothFieldLp_ae period F hFc hFs] with x hx
    rw [hx]
    change ⟪scalarEmbedding (φ x),
      fieldDerivative period a (fun y => scalarEmbedding (ψ y)) x⟫_ℝ = _
    rw [fieldDerivative_linear period scalarEmbedding ψ hψ, scalarEmbedding_inner]
  rw [hleft, hright] at hi
  exact hi

omit [Fact (0 < period)] in
theorem fieldDerivatives_commute {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (a b : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    fieldDerivative period a (fieldDerivative period b f) x =
      fieldDerivative period b (fieldDerivative period a f) x := by
  have h := directional_transport_commutator a (fun _ : LiftTangent => b)
    (localFieldLift period f x) contDiff_const (hf x) 0
  change fderiv ℝ (localFieldLift period (fieldDerivative period b f) x) 0 a =
    fderiv ℝ (localFieldLift period (fieldDerivative period a f) x) 0 b
  rw [localFieldLift_fieldDerivative, localFieldLift_fieldDerivative]
  change fderiv ℝ (directionalDerivative b (localFieldLift period f x)) 0 a =
    fderiv ℝ (directionalDerivative a (localFieldLift period f x)) 0 b +
      fderiv ℝ (localFieldLift period f x) 0 (fderiv ℝ (fun _ : LiftTangent => b) 0 a) at h
  have hc : fderiv ℝ (fun _ : LiftTangent => b) 0 = 0 := by simp
  rw [hc, zero_apply, map_zero, add_zero] at h
  exact h

/-- A compact antisymmetric derivative test field for one lifted curl component. -/
def curlTest (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (x : LiftDomain period) : Vector3 :=
  fieldDerivative period (coordinateDirection κ m j) ψ x • EuclideanSpace.single i 1 -
    fieldDerivative period (coordinateDirection κ m i) ψ x • EuclideanSpace.single j 1

omit [Fact (0 < period)] in
theorem curlTest_smooth (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (curlTest period κ m i j ψ) x) := by
  exact ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const).sub
    ((fieldDerivative_smooth period _ ψ hψ x).smul contDiff_const)

omit [Fact (0 < period)] in
theorem curlTest_compact (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (curlTest period κ m i j ψ) := by
  apply HasCompactSupport.intro hψ
  intro x hx
  have hd : ∀ a, fieldDerivative period a ψ x = 0 := by
    intro a
    change fieldFDeriv period ψ x a = 0
    rw [fieldFDeriv_zero_outside period ψ x hx]
    rfl
  simp [curlTest, hd]

omit [Fact (0 < period)] in
theorem vector_curlTest_inner (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (x : LiftDomain period) (v : Vector3) :
    ⟪v, curlTest period κ m i j ψ x⟫_ℝ =
      v i * fieldDerivative period (coordinateDirection κ m j) ψ x -
        v j * fieldDerivative period (coordinateDirection κ m i) ψ x := by
  simp [curlTest, inner_sub_right, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]

omit [Fact (0 < period)] in
theorem liftedGradient_component (κ : ℝ) (m : Vector3) (φ : LiftDomain period → ℝ)
    (x : LiftDomain period) (i : Fin 3) :
    liftedGradient period κ m φ x i = fieldDerivative period (coordinateDirection κ m i) φ x := by
  rw [liftedGradient_eq_vectorOfLinear]
  rfl

theorem scalar_derivative_product_integrable (a b : LiftTangent)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    Integrable (fun x => fieldDerivative period a φ x * fieldDerivative period b ψ x)
      (liftMeasure period) := by
  have hc := (smoothField_continuous period _ (fieldDerivative_smooth period a φ hφ)).mul
    (smoothField_continuous period _ (fieldDerivative_smooth period b ψ hψ))
  exact hc.integrable_of_hasCompactSupport (fieldDerivative_compact period a φ hφc).mul_right

theorem test_gradient_curl_integral (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (φ ψ : LiftDomain period → ℝ) (hφc : HasCompactSupport φ) (hψc : HasCompactSupport ψ)
    (hφ : ∀ x, ContDiff ℝ ∞ (localFieldLift period φ x))
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ⟪liftedGradient period κ m φ x, curlTest period κ m i j ψ x⟫_ℝ
      ∂liftMeasure period = 0 := by
  simp only [vector_curlTest_inner, liftedGradient_component]
  rw [integral_sub (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)
    (scalar_derivative_product_integrable period _ _ φ ψ hφc hφ hψ)]
  have hi := scalar_integration_by_parts period (coordinateDirection κ m i) φ
    (fieldDerivative period (coordinateDirection κ m j) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  have hj := scalar_integration_by_parts period (coordinateDirection κ m j) φ
    (fieldDerivative period (coordinateDirection κ m i) ψ) hφc
    (fieldDerivative_compact period _ ψ hψc) hφ (fieldDerivative_smooth period _ ψ hψ)
  rw [hi, hj]
  have heq : (fun x => φ x * fieldDerivative period (coordinateDirection κ m i)
      (fieldDerivative period (coordinateDirection κ m j) ψ) x) =
      fun x => φ x * fieldDerivative period (coordinateDirection κ m j)
        (fieldDerivative period (coordinateDirection κ m i) ψ) x := by
    funext x
    rw [fieldDerivatives_commute period _ _ ψ hψ]
  rw [heq, sub_self]

/-- The L² realization of an actual compact lifted curl test. -/
def curlTestLp (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    LiftL2 period := smoothFieldLp period (curlTest period κ m i j ψ)
      (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem curlTestLp_ae (κ : ℝ) (m : Vector3) (i j : Fin 3) (ψ : LiftDomain period → ℝ)
    (hψc : HasCompactSupport ψ) (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    curlTestLp period κ m i j ψ hψc hψ =ᵐ[liftMeasure period] curlTest period κ m i j ψ :=
  smoothFieldLp_ae period (curlTest period κ m i j ψ)
    (curlTest_compact period κ m i j ψ hψc) (curlTest_smooth period κ m i j ψ hψ)

theorem generator_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {g : LiftL2 period} (hg : g ∈ ({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) :
    ⟪g, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  obtain ⟨φ, hφ, hgφ⟩ := hg
  rw [L2.inner_def]
  rw [← test_gradient_curl_integral period κ m i j φ ψ hφ.1 hψc hφ.2 hψ]
  apply integral_congr_ae
  filter_upwards [hgφ, curlTestLp_ae period κ m i j ψ hψc hψ] with x hx hy
  rw [hx, hy]

theorem gradient_curl_pairing (κ : ℝ) (m : Vector3) (i j : Fin 3)
    (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x))
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m) :
    ⟪p, curlTestLp period κ m i j ψ hψc hψ⟫_ℝ = 0 := by
  let L := innerSL ℝ (curlTestLp period κ m i j ψ hψc hψ)
  have hspan : Submodule.span ℝ (({g : EulerLiftedGradientSpace.LiftL2 period | ∃ φ : EulerLiftedGradientSpace.LiftDomain period → ℝ, (HasCompactSupport φ ∧ ∀ x, ContDiff ℝ ∞ (EulerLiftedGradientSpace.localLift period φ x)) ∧ g =ᵐ[EulerLiftedGradientSpace.liftMeasure period] EulerLiftedGradientSpace.liftedGradient period κ m φ})) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro g hg
    change ⟪curlTestLp period κ m i j ψ hψc hψ, g⟫_ℝ = 0
    rw [real_inner_comm]
    exact generator_curl_pairing period κ m i j ψ hψc hψ hg
  have hclosed : IsClosed (L.ker : Set (LiftL2 period)) := L.isClosed_ker
  have hclosure : gradientSpace period κ m ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan hclosed
  have h := hclosure hp
  change ⟪curlTestLp period κ m i j ψ hψc hψ, p⟫_ℝ = 0 at h
  rwa [real_inner_comm] at h

/-- Every field in the closed lifted gradient space has zero distributional lifted curl. -/
theorem gradientSpace_weak_curl_zero (κ : ℝ) (m : Vector3)
    {p : LiftL2 period} (hp : p ∈ gradientSpace period κ m)
    (i j : Fin 3) (ψ : LiftDomain period → ℝ) (hψc : HasCompactSupport ψ)
    (hψ : ∀ x, ContDiff ℝ ∞ (localFieldLift period ψ x)) :
    ∫ x, ((p x) i * fieldDerivative period (coordinateDirection κ m j) ψ x -
      (p x) j * fieldDerivative period (coordinateDirection κ m i) ψ x)
      ∂liftMeasure period = 0 := by
  have h := gradient_curl_pairing period κ m i j ψ hψc hψ hp
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [curlTestLp_ae period κ m i j ψ hψc hψ] with x hx
  rw [hx, vector_curlTest_inner]

end EulerLiftedCurl

end

section

/-! Expanding spatial cutoffs and transport cancellation for noncompact fields on the cylinder. -/


namespace EulerNoncompactTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A fixed smooth spatial cutoff equal to one on the unit ball. -/
def spatialBump : ContDiffBump (0 : Vector3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The reciprocal spatial scale in the expanding cutoff sequence. -/
def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

/-- Smooth expanding cutoffs on the cylinder; the angular variable is unchanged. -/
def spatialCutoff (n : ℕ) (x : LiftDomain period) : ℝ :=
  spatialBump (cutoffScale n • x.1)

omit [Fact (0 < period)] in
theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  exact inv_pos.mpr (by positivity)

omit [Fact (0 < period)] in
theorem cutoffScale_le_one (n : ℕ) : cutoffScale n ≤ 1 := by
  exact inv_le_one_of_one_le₀ (by have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

omit [Fact (0 < period)] in
theorem cutoffScale_tendsto : Filter.Tendsto cutoffScale Filter.atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

omit [Fact (0 < period)] in
theorem spatialCutoff_bounds (n : ℕ) (x : LiftDomain period) :
    0 ≤ spatialCutoff period n x ∧ spatialCutoff period n x ≤ 1 :=
  ⟨spatialBump.nonneg, spatialBump.le_one⟩

omit [Fact (0 < period)] in
theorem spatialCutoff_smooth (n : ℕ) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localLift period (spatialCutoff period n) x) := by
  exact spatialBump.contDiff.comp ((contDiff_const.add contDiff_fst).const_smul _)

omit [Fact (0 < period)] in
theorem spatialCutoff_tendsto (x : LiftDomain period) :
    Filter.Tendsto (fun n => spatialCutoff period n x) Filter.atTop (𝓝 1) := by
  have h := spatialBump.continuous.continuousAt.tendsto.comp
    (cutoffScale_tendsto.smul_const x.1)
  have hb : spatialBump 0 = 1 := spatialBump.one_of_mem_closedBall (by simp [spatialBump])
  convert h using 1 <;> simp [spatialCutoff, hb, Function.comp_def]

theorem spatialCutoff_compact (n : ℕ) : HasCompactSupport (spatialCutoff period n) := by
  apply HasCompactSupport.intro
    ((isCompact_closedBall (0 : Vector3) (2 * ((n : ℝ) + 1))).prod
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle period))))
  intro x hx
  have hnorm : 2 * ((n : ℝ) + 1) < ‖x.1‖ := by
    simpa only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, Set.mem_univ,
      and_true, not_le] using hx
  apply spatialBump.zero_of_le_dist
  change 2 ≤ dist (cutoffScale n • x.1) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
  change 2 ≤ ((n : ℝ) + 1)⁻¹ * ‖x.1‖
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hnorm.le

omit [Fact (0 < period)] in
theorem spatialCutoff_fderiv (n : ℕ) (x : LiftDomain period) (v : LiftTangent) :
    fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v =
      fderiv ℝ spatialBump (cutoffScale n • x.1) (cutoffScale n • v.1) := by
  have hi : HasFDerivAt (fun h : LiftTangent => cutoffScale n • (x.1 + h.1))
      (cutoffScale n • ContinuousLinearMap.fst ℝ Vector3 ℝ) 0 := by
    convert ((ContinuousLinearMap.fst ℝ Vector3 ℝ).hasFDerivAt.const_add x.1).const_smul
      (cutoffScale n) using 1 <;> rfl
  have ho := ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).differentiable
    (by simp)).differentiableAt.hasFDerivAt (x := cutoffScale n • (x.1 + (0 : LiftTangent).1))
  have h := ho.comp 0 hi
  have heq := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L v) h.fderiv
  simpa +unfoldPartialApp [spatialCutoff, localLift, Function.comp_def] using heq

omit [Fact (0 < period)] in
/-- The cutoff derivatives have a uniform constant times their reciprocal spatial scale. -/
theorem spatialCutoff_derivative_bound : ∃ M : ℝ, 0 < M ∧ ∀ n x v,
    ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v‖ ≤
      M * cutoffScale n * ‖v‖ := by
  obtain ⟨M, hM, hbound⟩ :=
    ((spatialBump.hasCompactSupport.fderiv ℝ).isCompact_range
      ((spatialBump.contDiff : ContDiff ℝ ∞ spatialBump).continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨M, hM, fun n x v => ?_⟩
  rw [spatialCutoff_fderiv]
  calc
    _ ≤ ‖fderiv ℝ spatialBump (cutoffScale n • x.1)‖ * ‖cutoffScale n • v.1‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * (cutoffScale n * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
      exact mul_le_mul (hbound _ (Set.mem_range_self _))
        (mul_le_mul_of_nonneg_left (norm_fst_le v) (cutoffScale_pos n).le)
        (mul_nonneg (cutoffScale_pos n).le (norm_nonneg _)) hM.le
    _ = _ := by ring

omit [Fact (0 < period)] in
theorem spatialCutoff_derivative_tendsto (x : LiftDomain period) (v : LiftTangent) :
    Filter.Tendsto (fun n => fderiv ℝ (localLift period (spatialCutoff period n) x) 0 v)
      Filter.atTop (𝓝 0) := by
  obtain ⟨M, _, hM⟩ := spatialCutoff_derivative_bound period
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hM n x v)
  simpa using (tendsto_const_nhds.mul cutoffScale_tendsto).mul_const (‖v‖ : ℝ)

omit [Fact (0 < period)] in
theorem cutoff_product_transport (κ : ℝ) (m : Vector3) (n : ℕ)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (x : LiftDomain period) (v : Vector3) :
    ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, v⟫_ℝ =
      spatialCutoff period n x * fderiv ℝ (localLift period φ x) 0 (transportDirection κ m v) +
      φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0 (transportDirection κ m v) := by
  rw [liftedGradient_eq_vectorOfLinear, vectorOfLinear_inner]
  have hc := ((spatialCutoff_smooth period n x).differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := 0)
  have hf := ((hφ x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have h := congrArg (fun L : LiftTangent →L[ℝ] ℝ => L (transportDirection κ m v))
    (hc.mul hf).fderiv
  simpa +unfoldPartialApp [localLift, Pi.mul_def] using h

/-- Smooth scalar weak-divergence tests extend to integrable noncompact energies. -/
theorem weak_divergence_integral_noncompact (κ : ℝ) (m : Vector3)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (_hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (φ : LiftDomain period → ℝ) (hφ : ∀ x, ContDiff ℝ ∞ (localLift period φ x))
    (hφI : Integrable φ (liftMeasure period))
    (hflux : Integrable (fun x => fderiv ℝ (localLift period φ x) 0
      (transportDirection κ m (z x))) (liftMeasure period)) :
    ∫ x, fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
      ∂liftMeasure period = 0 := by
  obtain ⟨M, hM, hMb⟩ := spatialCutoff_derivative_bound period
  let C := M * (|κ| + ‖m‖) * B
  let flux := fun x => fderiv ℝ (localLift period φ x) 0 (transportDirection κ m (z x))
  let F := fun n x => ⟪liftedGradient period κ m (fun y => spatialCutoff period n y * φ y) x, z x⟫_ℝ
  have hs : ∀ n x, ContDiff ℝ ∞ (localLift period (fun y => spatialCutoff period n y * φ y) x) :=
    fun n x => (spatialCutoff_smooth period n x).mul (hφ x)
  have hc : ∀ n, HasCompactSupport (fun y => spatialCutoff period n y * φ y) :=
    fun n => (spatialCutoff_compact period n).mul_right
  have hF0 : ∀ n, ∫ x, F n x ∂liftMeasure period = 0 :=
    fun n => weak_divergence_test_integral period κ m hz _ ⟨hc n, hs n⟩
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (liftMeasure period) := by
    intro n
    exact (liftedGradient_continuous period κ m _ (hs n)).aestronglyMeasurable.inner
      (Lp.aestronglyMeasurable z)
  have hbound : ∀ n, ∀ᵐ x ∂liftMeasure period, ‖F n x‖ ≤ ‖flux x‖ + C * ‖φ x‖ := by
    intro n
    filter_upwards [hzB] with x hx
    have hcut := spatialCutoff_bounds period n x
    have hv : ‖transportDirection κ m (z x)‖ ≤ (|κ| + ‖m‖) * B :=
      (transportDirection_norm_le κ m (z x)).trans
        (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
    have hd : ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
        (transportDirection κ m (z x))‖ ≤ C := by
      calc
        _ ≤ M * cutoffScale n * ‖transportDirection κ m (z x)‖ := hMb n x _
        _ ≤ M * 1 * ((|κ| + ‖m‖) * B) := by
          gcongr
          exact cutoffScale_le_one n
        _ = C := by dsimp [C]; ring
    dsimp [F]
    rw [cutoff_product_transport period κ m n φ hφ]
    calc
      _ ≤ ‖spatialCutoff period n x * flux x‖ +
          ‖φ x * fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := norm_add_le _ _
      _ = ‖spatialCutoff period n x‖ * ‖flux x‖ + ‖φ x‖ *
          ‖fderiv ℝ (localLift period (spatialCutoff period n) x) 0
            (transportDirection κ m (z x))‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖flux x‖ + ‖φ x‖ * C := by
        gcongr
        simpa only [Real.norm_eq_abs, abs_of_nonneg hcut.1] using hcut.2
      _ = _ := by simp only [Real.norm_eq_abs]; ring
  have hlim : ∀ᵐ x ∂liftMeasure period, Filter.Tendsto (fun n => F n x)
      Filter.atTop (𝓝 (flux x)) := by
    apply Filter.Eventually.of_forall
    intro x
    simp_rw [F, cutoff_product_transport period κ m _ φ hφ]
    convert ((spatialCutoff_tendsto period x).mul_const (flux x)).add
      ((spatialCutoff_derivative_tendsto period x (transportDirection κ m (z x))).const_mul
        (φ x)) using 1
    simp
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖flux x‖ + C * ‖φ x‖)
    hmeas (hflux.norm.add (hφI.norm.const_mul C)) hbound hlim
  have heq : (fun n => ∫ x, F n x ∂liftMeasure period) = fun _ : ℕ => 0 := by
    funext n
    exact hF0 n
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Integration by parts for a noncompact smooth metric energy with integrable terms. -/
theorem metric_transport_noncompact_by_parts (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (B : ℝ) (hB : 0 ≤ B) (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (hE : Integrable (metricEnergy period K e) (liftMeasure period))
    (hT : Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period))
    (hQ : Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period)) :
    (∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period) =
    -(∫ x, (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ ∂liftMeasure period) := by
  have hf : Integrable (fun x => fderiv ℝ (localLift period (metricEnergy period K e) x) 0
      (transportDirection κ m (z x))) (liftMeasure period) := by
    simp only [metricEnergy_fderiv period K e hK he hsym]
    exact hT.add hQ
  have hz0 := weak_divergence_integral_noncompact period κ m hz B hB hzB
    (metricEnergy period K e) (metricEnergy_smooth period K e hK he) hE hf
  simp only [metricEnergy_fderiv period K e hK he hsym] at hz0
  rw [integral_add hT hQ] at hz0
  exact eq_neg_of_add_eq_zero_left hz0

theorem aestronglyMeasurable_apply {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : LiftDomain period → V →L[ℝ] W} {u : LiftDomain period → V}
    (hA : AEStronglyMeasurable A (liftMeasure period))
    (hu : AEStronglyMeasurable u (liftMeasure period)) :
    AEStronglyMeasurable (fun x => A x (u x)) (liftMeasure period) :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hu)

/-- Bounded metrics have integrable quadratic energy on every actual L² field. -/
theorem metricEnergy_integrable (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) :
    Integrable (metricEnergy period K e) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * C)).mono'
  · exact aestronglyMeasurable_const.mul ((aestronglyMeasurable_apply period hK he.aestronglyMeasurable).inner
      he.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪K x (e x), e x⟫_ℝ‖ := by dsimp [metricEnergy]; rw [abs_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖K x (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((C : ℝ) * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The actual lifted transport velocity of an L² field is measurable. -/
theorem transportDirection_aestronglyMeasurable (κ : ℝ) (m : Vector3) (z : LiftL2 period) :
    AEStronglyMeasurable (fun x => transportDirection κ m (z x)) (liftMeasure period) := by
  exact ((Lp.aestronglyMeasurable z).const_smul κ).prodMk
    (aestronglyMeasurable_const.inner (Lp.aestronglyMeasurable z))

/-- The principal transport pairing is integrable for smooth H¹ fields and bounded velocity. -/
theorem metricTransport_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : AEStronglyMeasurable K (liftMeasure period))
    (he : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (C B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C) (z : LiftL2 period)
    (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ) (liftMeasure period) := by
  apply ((he.norm.integrable_mul hDe.norm).const_mul ((C : ℝ) * B)).mono'
  · exact (aestronglyMeasurable_apply period hK he.aestronglyMeasurable).inner
      (aestronglyMeasurable_apply period hDe.aestronglyMeasurable
        (transportDirection_aestronglyMeasurable period κ m z))
  filter_upwards [hz] with x hx
  have hKe : ‖K x (e x)‖ ≤ (C : ℝ) * ‖e x‖ :=
    ((K x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hDv : ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ ≤
      ‖fderiv ℝ (localFieldLift period e x) 0‖ * B :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  calc
    _ ≤ ‖K x (e x)‖ * ‖fderiv ℝ (localFieldLift period e x) 0 (transportDirection κ m (z x))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ((C : ℝ) * ‖e x‖) * (‖fderiv ℝ (localFieldLift period e x) 0‖ * B) :=
      mul_le_mul hKe hDv (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Pi.mul_apply]; ring

omit [Fact (0 < period)] in
theorem metricCorrection_pointwise_bound
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (D B : ℝ≥0) (x : LiftDomain period) (v : LiftTangent)
    (hD : ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D) (hv : ‖v‖ ≤ B) :
    ‖(1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ ≤
      (1 / 2 : ℝ) * D * B * ‖e x‖ ^ 2 := by
  have hL : ‖fderiv ℝ (localFieldLift period K x) 0 v‖ ≤ (D : ℝ) * B :=
    ((fderiv ℝ (localFieldLift period K x) 0).le_opNorm _).trans
      (mul_le_mul hD hv (norm_nonneg _) D.coe_nonneg)
  have hLe : ‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ ≤ (D : ℝ) * B * ‖e x‖ :=
    ((fderiv ℝ (localFieldLift period K x) 0 v).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    _ = (1 / 2 : ℝ) * ‖⟪(fderiv ℝ (localFieldLift period K x) 0 v) (e x), e x⟫_ℝ‖ := by
      rw [norm_mul]; norm_num
    _ ≤ (1 / 2 : ℝ) * (‖(fderiv ℝ (localFieldLift period K x) 0 v) (e x)‖ * ‖e x‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (((D : ℝ) * B * ‖e x‖) * ‖e x‖) := by gcongr
    _ = _ := by ring

/-- The metric correction is integrable for L² fields and bounded metric derivative and velocity. -/
theorem metricCorrection_integrable (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hDK : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period)) (he : MemLp e 2 (liftMeasure period))
    (D B : ℝ≥0) (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (z : LiftL2 period) (hz : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ B) :
    Integrable (fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) (liftMeasure period) := by
  apply (he.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * B)).mono'
  · exact aestronglyMeasurable_const.mul
      ((aestronglyMeasurable_apply period
        (aestronglyMeasurable_apply period hDK (transportDirection_aestronglyMeasurable period κ m z))
          he.aestronglyMeasurable).inner he.aestronglyMeasurable)
  filter_upwards [hz] with x hx
  exact metricCorrection_pointwise_bound period K e D B x _ (hD x) hx

/-- The genuine noncompact H¹ metric transport estimate; no cancellation is assumed. -/
theorem metric_transport_H1_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftDomain period → Vector3)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (heLp : MemLp e 2 (liftMeasure period))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period e x) 0) 2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period e x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
  let β : ℝ≥0 := ⟨(|κ| + ‖m‖) * B,
    mul_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _)) B.coe_nonneg⟩
  have hv : ∀ᵐ x ∂liftMeasure period, ‖transportDirection κ m (z x)‖ ≤ β := by
    filter_upwards [hzB] with x hx
    exact (transportDirection_norm_le κ m (z x)).trans
      (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  have hKm : AEStronglyMeasurable K (liftMeasure period) :=
    (smoothField_continuous period K hK).aestronglyMeasurable
  have hDKm : AEStronglyMeasurable (fun x => fderiv ℝ (localFieldLift period K x) 0)
      (liftMeasure period) :=
    (localFDeriv_continuous period K hK).aestronglyMeasurable
  have hT := metricTransport_integrable period κ m K e hKm heLp hDe C β hC z hv
  have hQ := metricCorrection_integrable period κ m K e hDKm heLp D β hD z hv
  rw [metric_transport_noncompact_by_parts period κ m K e hK he hsym hz B B.coe_nonneg hzB
    (metricEnergy_integrable period K e hKm heLp C hC) hT hQ, abs_neg]
  have hbound := norm_integral_le_of_norm_le
    (heLp.norm.integrable_sq.const_mul ((1 / 2 : ℝ) * D * β))
    (f := fun x => (1 / 2 : ℝ) * ⟪(fderiv ℝ (localFieldLift period K x) 0
      (transportDirection κ m (z x))) (e x), e x⟫_ℝ) ?_
  · have hβ : (β : ℝ) = (|κ| + ‖m‖) * B := rfl
    rw [hβ] at hbound
    simpa only [Real.norm_eq_abs, integral_const_mul] using hbound
  filter_upwards [hv] with x hx
  exact metricCorrection_pointwise_bound period K e D β x _ (hD x) hx

/-- The noncompact transport estimate expressed in the genuine L² Hilbert norm. -/
theorem metric_transport_L2_H1_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3) (e : LiftL2 period)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    {z : LiftL2 period} (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period (fun y => e y) x) 0
      (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  have hn : (∫ x, ‖e x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_H1_bound period κ m K (fun x => e x)
    hK he (Lp.memLp e) hDe hsym hz C D B hC hD hzB

end EulerNoncompactTransport

end

section

namespace EulerMetricEnergyEvolution

open InnerProductSpace Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact time derivative of a quadratic energy with a moving metric. -/
theorem metric_energy_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), e'⟫_ℝ) t := by
  refine ((hK.clm_apply he).inner ℝ he).congr_deriv ?_
  rw [inner_add_left, hsym e' (e t), real_inner_comm e' (K t (e t))]
  ring

/-- Cancellation of pressure and integration by parts for transport leave only
metric variation and the forcing in the time derivative. -/
theorem metric_energy_evolution (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : e' + transport + pressure = forcing)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), forcing⟫_ℝ -
        2 * ⟪K t (e t), transport⟫_ℝ) t := by
  refine (metric_energy_hasDerivAt K e t K' e' hK he hsym).congr_deriv ?_
  have h := congrArg (fun v => ⟪K t (e t), v⟫_ℝ) heq
  simp only [inner_add_right, hp, add_zero] at h
  linarith

theorem energy_derivative_bound (K K' : H →L[ℝ] H) (e transport forcing : H)
    (B : ℝ) (_hB : 0 ≤ B) (ht : |⟪K e, transport⟫_ℝ| ≤ B * ‖e‖ ^ 2) :
    ⟪K' e, e⟫_ℝ + 2 * ⟪K e, forcing⟫_ℝ - 2 * ⟪K e, transport⟫_ℝ ≤
      (‖K'‖ + 2 * B) * ‖e‖ ^ 2 + 2 * ‖K‖ * ‖e‖ * ‖forcing‖ := by
  have hk : ⟪K' e, e⟫_ℝ ≤ ‖K'‖ * ‖e‖ ^ 2 := by
    calc
      _ ≤ ‖K' e‖ * ‖e‖ := real_inner_le_norm _ _
      _ ≤ (‖K'‖ * ‖e‖) * ‖e‖ := by gcongr; exact K'.le_opNorm e
      _ = _ := by ring
  have hf : ⟪K e, forcing⟫_ℝ ≤ ‖K‖ * ‖e‖ * ‖forcing‖ := by
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (K.le_opNorm e) (norm_nonneg _))
  have ht' := (abs_le.mp ht).1
  nlinarith

/-- A positive regularization gives a differentiable metric norm even at zero. -/
theorem regularized_metric_norm_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t δ : ℝ) (K' : H →L[ℝ] H) (e' : H)
    (hδ : 0 < δ) (hpos : 0 ≤ ⟪K t (e t), e t⟫_ℝ)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ) :
    HasDerivAt (fun s => √(⟪K s (e s), e s⟫_ℝ + δ ^ 2))
      ((⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), e'⟫_ℝ) /
        (2 * √(⟪K t (e t), e t⟫_ℝ + δ ^ 2))) t := by
  exact HasDerivAt.sqrt
    ((metric_energy_hasDerivAt K e t K' e' hK he hsym).add_const (δ ^ 2)) (by nlinarith)

/-- The norm estimate used before summing Gevrey weights. All terms come from
the actual differential equation; no estimate for the energy derivative is assumed. -/
theorem regularized_metric_norm_evolution (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t δ c B : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing : H)
    (hδ : 0 < δ) (hc : 0 < c) (hB : 0 ≤ B)
    (hcoercive : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪K t (e t), e t⟫_ℝ)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : e' + transport + pressure = forcing)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0)
    (ht : |⟪K t (e t), transport⟫_ℝ| ≤ B * ‖e t‖ ^ 2) :
    deriv (fun s => √(⟪K s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + 2 * B) / (2 * c ^ 2)) * √(⟪K t (e t), e t⟫_ℝ + δ ^ 2) +
        (‖K t‖ / c) * ‖forcing‖ := by
  let E := √(⟪K t (e t), e t⟫_ℝ + δ ^ 2)
  have hq : 0 ≤ ⟪K t (e t), e t⟫_ℝ :=
    (mul_nonneg (sq_nonneg c) (sq_nonneg ‖e t‖)).trans hcoercive
  have hE : 0 < E := sqrt_pos.2 (by nlinarith)
  have hE2 : E ^ 2 = ⟪K t (e t), e t⟫_ℝ + δ ^ 2 := sq_sqrt (by nlinarith)
  have hnorm : ‖e t‖ ≤ E / c := by
    apply (le_div_iff₀ hc).2
    nlinarith [norm_nonneg (e t)]
  have hnorm2 : ‖e t‖ ^ 2 ≤ E ^ 2 / c ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hdiff := metric_energy_evolution K e t K' e' transport pressure forcing hK he hsym heq hp
  have hroot := HasDerivAt.sqrt (hdiff.add_const (δ ^ 2)) (by nlinarith :
    ⟪K t (e t), e t⟫_ℝ + δ ^ 2 ≠ 0)
  rw [hroot.deriv]
  change (_ / (2 * E)) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 2 * E)).2
  have hb := energy_derivative_bound (K t) K' (e t) transport forcing B hB ht
  have h1 := mul_le_mul_of_nonneg_left hnorm2
    (show 0 ≤ ‖K'‖ + 2 * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ 2 * ‖K t‖ * ‖forcing‖ by positivity)
  calc
    _ ≤ (‖K'‖ + 2 * B) * ‖e t‖ ^ 2 + 2 * ‖K t‖ * ‖e t‖ * ‖forcing‖ := hb
    _ ≤ (‖K'‖ + 2 * B) * (E ^ 2 / c ^ 2) +
        2 * ‖K t‖ * (E / c) * ‖forcing‖ := by nlinarith
    _ = _ := by dsimp [E]; field_simp

end EulerMetricEnergyEvolution

end

section

/-! Concrete L² transport and metric-energy evolution on the lifted cylinder. -/


namespace EulerLiftedMetricEvolution

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerNoncompactTransport EulerMetricEnergyEvolution
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual directional transport derivative is square integrable under H¹ and bounded velocity. -/
theorem liftedTransport_memLp (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0
      (transportDirection κ m (z x))) 2 (liftMeasure period) := by
  apply hDe.of_le_mul (c := (|κ| + ‖m‖) * B)
  · exact aestronglyMeasurable_apply period hDe.aestronglyMeasurable
      (transportDirection_aestronglyMeasurable period κ m z)
  filter_upwards [hzB] with x hx
  have hv := (transportDirection_norm_le κ m (z x)).trans
    (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ ‖fderiv ℝ (localFieldLift period (fun y => e y) x) 0‖ *
        ‖transportDirection κ m (z x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (localFieldLift period (fun y => e y) x) 0‖ * ((|κ| + ‖m‖) * B) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := by ring

/-- The genuine L² element represented by the lifted directional transport derivative. -/
def liftedTransport (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) : LiftL2 period :=
  (liftedTransport_memLp period κ m e z hDe B hzB).toLp _

theorem liftedTransport_ae (κ : ℝ) (m : Vector3) (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    liftedTransport period κ m e z hDe B hzB =ᵐ[liftMeasure period]
      fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x)) :=
  (liftedTransport_memLp period κ m e z hDe B hzB).coeFn_toLp

/-- The Hilbert metric pairing equals the actual spatial transport integral. -/
theorem metric_transport_inner_eq (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period)) (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (e z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    ⟪coefficientOperator K hKm C hC e, liftedTransport period κ m e z hDe B hzB⟫_ℝ =
      ∫ x, ⟪K x (e x), fderiv ℝ (localFieldLift period (fun y => e y) x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae K hKm C hC e, liftedTransport_ae period κ m e z hDe B hzB]
    with x hx hy
  rw [hx, hy]

/-- The transport bound required by the Hilbert energy theorem, with genuine spatial fields. -/
theorem metric_transport_inner_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period))
    (e z : LiftL2 period)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |⟪coefficientOperator K hKm C hC e, liftedTransport period κ m e z hDe B hzB⟫_ℝ| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  rw [metric_transport_inner_eq]
  exact metric_transport_L2_H1_bound period κ m K e hK he hDe hsym hz C D B hC hD hzB

/-- A pointwise matrix family acting on the actual lifted L² space. -/
def metricFamily (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C) : ℝ → LiftL2 period →L[ℝ] LiftL2 period :=
  fun t => coefficientOperator (K t) (hKm t) C (hC t)

/-- The metric norm estimate for the actual lifted transport-pressure equation. -/
theorem lifted_regularized_energy_evolution (κ : ℝ) (m : Vector3)
    (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C)
    (e : ℝ → LiftL2 period) (t δ c : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (e' z p forcing : LiftL2 period)
    (hδ : 0 < δ) (hc : 0 < c)
    (hKt : HasDerivAt (metricFamily period K hKm C hC) K' t) (het : HasDerivAt e e' t)
    (hKs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (K t) x))
    (hes : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => e t y) x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period (fun y => e t y) x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K t x v, w⟫_ℝ = ⟪v, K t x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K t x v, v⟫_ℝ)
    (G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hGm : AEStronglyMeasurable G (liftMeasure period)) (E : ℝ≥0) (hG : ∀ x, ‖G x‖ ≤ E)
    (hKG : ∀ x v, K t x (G x v) = v)
    (hep : e t ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m)
    (hz : z ∈ divergenceFreeSpace period κ m) (D B : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period (K t) x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (heq : e' + liftedTransport period κ m (e t) z hDe B hzB +
      coefficientOperator G hGm E hG p = forcing) :
    deriv (fun s => Real.sqrt (⟪metricFamily period K hKm C hC s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + (D : ℝ) * ((|κ| + ‖m‖) * B)) / (2 * c ^ 2)) *
        Real.sqrt (⟪metricFamily period K hKm C hC t (e t), e t⟫_ℝ + δ ^ 2) +
      ((C : ℝ) / c) * ‖forcing‖ := by
  let A := metricFamily period K hKm C hC
  let β : ℝ := (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsymL : ∀ v w, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ :=
    coefficientOperator_inner_swap (K t) (hKm t) C (hC t) hsym
  have hposL : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪A t (e t), e t⟫_ℝ :=
    coefficientOperator_coercive (K t) (hKm t) C (hC t) (c ^ 2) hpos (e t)
  have hpL : ⟪A t (e t), coefficientOperator G hGm E hG p⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t) G (hKm t) hGm C E (hC t) hG hsym hKG hep hp
  have htL := metric_transport_inner_bound period κ m (K t) (hKm t) (e t) z
    hKs hes hDe hsym hz C D B (hC t) hD hzB
  have h := regularized_metric_norm_evolution A e t δ c β K' e'
    (liftedTransport period κ m (e t) z hDe B hzB) (coefficientOperator G hGm E hG p)
    forcing hδ hc hβ hposL hKt het hsymL heq hpL htL
  have hA : ‖A t‖ ≤ C := coefficientOperator_norm_le (K t) (hKm t) C (hC t)
  have hb : 2 * β = (D : ℝ) * ((|κ| + ‖m‖) * B) := by dsimp [β]; ring
  rw [hb] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hA hc.le) (norm_nonneg forcing)) _)

end EulerLiftedMetricEvolution

end

section

/-! Metric-energy evolution using a separate actual smooth representative of each L² class. -/


namespace EulerRepresentativeMetricEvolution

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerMetricTransport EulerNoncompactTransport EulerMetricEnergyEvolution
open scoped ContDiff ENNReal NNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual directional transport derivative is square integrable under H¹ and bounded velocity. -/
theorem liftedTransport_memLp (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0
      (transportDirection κ m (z x))) 2 (liftMeasure period) := by
  apply hDe.of_le_mul (c := (|κ| + ‖m‖) * B)
  · exact aestronglyMeasurable_apply period hDe.aestronglyMeasurable
      (transportDirection_aestronglyMeasurable period κ m z)
  filter_upwards [hzB] with x hx
  have hv := (transportDirection_norm_le κ m (z x)).trans
    (mul_le_mul_of_nonneg_left hx (add_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ *
        ‖transportDirection κ m (z x)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (localFieldLift period g x) 0‖ * ((|κ| + ‖m‖) * B) :=
      mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := by ring

/-- The genuine L² element represented by the lifted directional transport derivative. -/
def liftedTransport (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) : LiftL2 period :=
  (liftedTransport_memLp period κ m g z hDe B hzB).toLp _

theorem liftedTransport_ae (κ : ℝ) (m : Vector3) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    liftedTransport period κ m g z hDe B hzB =ᵐ[liftMeasure period]
      fun x => fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x)) :=
  (liftedTransport_memLp period κ m g z hDe B hzB).coeFn_toLp

/-- The Hilbert metric pairing equals the actual spatial transport integral. -/
theorem metric_transport_inner_eq (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period)) (C : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period)) (B : ℝ≥0)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    ⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ =
      ∫ x, ⟪K x (g x), fderiv ℝ (localFieldLift period g x) 0
        (transportDirection κ m (z x))⟫_ℝ ∂liftMeasure period := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientOperator_ae K hKm C hC e, liftedTransport_ae period κ m g z hDe B hzB, hrep]
    with x hx hy hr
  rw [hx, hy, hr]

/-- The transport bound required by the Hilbert energy theorem, with genuine spatial fields. -/
theorem metric_transport_inner_bound (κ : ℝ) (m : Vector3)
    (K : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : AEStronglyMeasurable K (liftMeasure period))
    (e : LiftL2 period) (g : LiftDomain period → Vector3) (z : LiftL2 period)
    (hrep : (e : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hK : ∀ x, ContDiff ℝ ∞ (localFieldLift period K x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K x v, w⟫_ℝ = ⟪v, K x w⟫_ℝ)
    (hz : z ∈ divergenceFreeSpace period κ m)
    (C D B : ℝ≥0) (hC : ∀ x, ‖K x‖ ≤ C)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period K x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B) :
    |⟪coefficientOperator K hKm C hC e, liftedTransport period κ m g z hDe B hzB⟫_ℝ| ≤
      (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B) * ‖e‖ ^ 2 := by
  rw [metric_transport_inner_eq period κ m K hKm C hC e g z hrep hDe B hzB]
  have hn : (∫ x, ‖g x‖ ^ 2 ∂liftMeasure period) = ‖e‖ ^ 2 := by
    calc
      _ = ∫ x, ‖e x‖ ^ 2 ∂liftMeasure period := by
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        rw [hx]
      _ = _ := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
  simpa only [hn] using metric_transport_H1_bound period κ m K g
    hK he ((memLp_congr_ae hrep).mp (Lp.memLp e)) hDe hsym hz C D B hC hD hzB

/-- A pointwise matrix family acting on the actual lifted L² space. -/
def metricFamily (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C) : ℝ → LiftL2 period →L[ℝ] LiftL2 period :=
  fun t => coefficientOperator (K t) (hKm t) C (hC t)

/-- The metric norm estimate for the actual lifted transport-pressure equation. -/
theorem lifted_regularized_energy_evolution (κ : ℝ) (m : Vector3)
    (K : ℝ → LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hKm : ∀ t, AEStronglyMeasurable (K t) (liftMeasure period))
    (C : ℝ≥0) (hC : ∀ t x, ‖K t x‖ ≤ C)
    (e : ℝ → LiftL2 period) (t δ c : ℝ)
    (K' : LiftL2 period →L[ℝ] LiftL2 period) (e' z p forcing : LiftL2 period)
    (hδ : 0 < δ) (hc : 0 < c)
    (hKt : HasDerivAt (metricFamily period K hKm C hC) K' t) (het : HasDerivAt e e' t)
    (hKs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (K t) x))
    (g : LiftDomain period → Vector3)
    (hrep : (e t : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hes : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hDe : MemLp (fun x => fderiv ℝ (localFieldLift period g x) 0)
      2 (liftMeasure period))
    (hsym : ∀ x v w, ⟪K t x v, w⟫_ℝ = ⟪v, K t x w⟫_ℝ)
    (hpos : ∀ x v, c ^ 2 * ‖v‖ ^ 2 ≤ ⟪K t x v, v⟫_ℝ)
    (G : LiftDomain period → Vector3 →L[ℝ] Vector3)
    (hGm : AEStronglyMeasurable G (liftMeasure period)) (E : ℝ≥0) (hG : ∀ x, ‖G x‖ ≤ E)
    (hKG : ∀ x v, K t x (G x v) = v)
    (hep : e t ∈ divergenceFreeSpace period κ m) (hp : p ∈ gradientSpace period κ m)
    (hz : z ∈ divergenceFreeSpace period κ m) (D B : ℝ≥0)
    (hD : ∀ x, ‖fderiv ℝ (localFieldLift period (K t) x) 0‖ ≤ D)
    (hzB : ∀ᵐ x ∂liftMeasure period, ‖z x‖ ≤ B)
    (heq : e' + liftedTransport period κ m g z hDe B hzB +
      coefficientOperator G hGm E hG p = forcing) :
    deriv (fun s => Real.sqrt (⟪metricFamily period K hKm C hC s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + (D : ℝ) * ((|κ| + ‖m‖) * B)) / (2 * c ^ 2)) *
        Real.sqrt (⟪metricFamily period K hKm C hC t (e t), e t⟫_ℝ + δ ^ 2) +
      ((C : ℝ) / c) * ‖forcing‖ := by
  let A := metricFamily period K hKm C hC
  let β : ℝ := (1 / 2 : ℝ) * D * ((|κ| + ‖m‖) * B)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hsymL : ∀ v w, ⟪A t v, w⟫_ℝ = ⟪v, A t w⟫_ℝ :=
    coefficientOperator_inner_swap (K t) (hKm t) C (hC t) hsym
  have hposL : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪A t (e t), e t⟫_ℝ :=
    coefficientOperator_coercive (K t) (hKm t) C (hC t) (c ^ 2) hpos (e t)
  have hpL : ⟪A t (e t), coefficientOperator G hGm E hG p⟫_ℝ = 0 :=
    metric_pressure_cancellation period κ m (K t) G (hKm t) hGm C E (hC t) hG hsym hKG hep hp
  have htL := metric_transport_inner_bound period κ m (K t) (hKm t) (e t) g z hrep
    hKs hes hDe hsym hz C D B (hC t) hD hzB
  have h := regularized_metric_norm_evolution A e t δ c β K' e'
    (liftedTransport period κ m g z hDe B hzB) (coefficientOperator G hGm E hG p)
    forcing hδ hc hβ hposL hKt het hsymL heq hpL htL
  have hA : ‖A t‖ ≤ C := coefficientOperator_norm_le (K t) (hKm t) C (hC t)
  have hb : 2 * β = (D : ℝ) * ((|κ| + ‖m‖) * B) := by dsimp [β]; ring
  rw [hb] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hA hc.le) (norm_nonneg forcing)) _)

end EulerRepresentativeMetricEvolution

end

section

/-! Exact differentiated projected-pressure equations for actual translation Sobolev jets. -/


namespace EulerPressureJetIdentities

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerLiftedWeakDerivative EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Strong derivatives preserve the actual closed lifted gradient subspace. -/
theorem gradientSpace_translation_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    {f f' : LiftL2 period} (hf : f ∈ gradientSpace period κ m)
    (hder : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    f' ∈ gradientSpace period κ m := by
  have hlim := hder.tendsto_slope_zero
  simp only [zero_add, translationPath_zero, translation_zero] at hlim
  apply (gradientSpace_closed period κ m).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun t => (gradientSpace period κ m).smul_mem _
    ((gradientSpace period κ m).sub_mem
      (gradientSpace_translation_mem period κ m (translationPath period a t) hf) hf)

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Actual strong derivative words are independent of the chosen derivative witness tree. -/
theorem word_unique {s t n : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions t g)
    (hfg : f = g) (hn : n ≤ s) (hm : n ≤ t) (w : Fin n → Fin 4) : J.word w = K.word w := by
  subst g
  induction n with
  | zero => simp
  | succ n ih =>
    have hbase := ih (by omega) (by omega) (Fin.tail w)
    have hJ := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have hK := K.word_hasDerivAt (by omega : n < t) (Fin.tail w) (w 0)
    rw [hbase] at hJ
    simpa only [Fin.cons_self_tail] using hJ.unique hK

/-- Every valid word of a gradient-valued Sobolev jet remains in the gradient subspace. -/
theorem word_mem_gradientSpace {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (hf : f ∈ gradientSpace period κ m) (hn : n ≤ s)
    (w : Fin n → Fin 4) : J.word w ∈ gradientSpace period κ m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := gradientSpace_translation_derivative period κ m (directions (w 0))
      (ih (by omega) (Fin.tail w))
      (J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0))
    simpa only [Fin.cons_self_tail] using h

/-- Every valid word of a solenoidal Sobolev jet remains genuinely weakly solenoidal. -/
theorem word_mem_divergenceFreeSpace {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (hf : f ∈ divergenceFreeSpace period κ m) (hn : n ≤ s)
    (w : Fin n → Fin 4) : J.word w ∈ divergenceFreeSpace period κ m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := divergenceFree_translation_derivative period κ m (directions (w 0))
      (ih (by omega) (Fin.tail w))
      (J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0))
    simpa only [Fin.cons_self_tail] using h

/-- A bounded operator commuting with actual translations maps genuine spatial jets. -/
def map (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    {s : ℕ} {f : LiftL2 period} (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) :
    EulerSpatialSobolevInverse.SpatialJet period directions s (L f) :=
  match J with
  | .zero f => .zero (L f)
  | .succ df lower hd => .succ (fun i => L (df i)) (fun i => map L hL (lower i))
      (fun i => by
        have h := L.hasFDerivAt.comp_hasDerivAt 0 (hd i)
        convert h using 1 <;> first | rfl | (funext t; exact hL _ _))

theorem map_word {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    (w : Fin n → Fin 4) : (map L hL J).word w = L (J.word w) := by
  induction J generalizing n with
  | zero f => cases n <;> simp [map, EulerSpatialSobolevInverse.SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [map, EulerSpatialSobolevInverse.SpatialJet.word_succ] using
        (ih (w (Fin.last n)) (Fin.init w))

/-- At every derivative word, the actual projected equation differentiates exactly. -/
theorem pressure_word_projected_equation {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    gradientProjection period κ m
      ((EulerSpatialSobolevInverse.SpatialJet.multiply K (J.solvePressure K κ m c hc hpos)).word w) =
      gradientProjection period κ m (J.word w) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  have heq : gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos f)) =
      gradientProjection period κ m f :=
    liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f
  have h := word_unique (map (gradientProjection period κ m)
      (gradientProjection_translation period κ m) M)
    (map (gradientProjection period κ m) (gradientProjection_translation period κ m) J) heq hn hn w
  simpa only [map_word] using h

/-- The actual derivative word is the coercive inverse applied to its differentiated source
minus the genuine product commutator. -/
theorem pressure_word_inverse {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    (J.solvePressure K κ m c hc hpos).word w = A.pressure κ m c hc hpos
      (J.word w - ((EulerSpatialSobolevInverse.SpatialJet.multiply K
        (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w))) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
  · exact word_mem_gradientSpace P κ m
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f) hn w
  · have hp := pressure_word_projected_equation K J κ m c hc hpos hn w
    change gradientProjection period κ m (A.operator (P.word w)) =
      gradientProjection period κ m (J.word w - (M.word w - A.operator (P.word w)))
    rw [map_sub, map_sub, hp]
    abel

/-- The rigorous triangular pressure estimate before its product commutator is summed. -/
theorem pressure_word_norm_le {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    ‖(J.solvePressure K κ m c hc hpos).word w‖ ≤ c⁻¹ *
      (‖J.word w‖ + ‖(EulerSpatialSobolevInverse.SpatialJet.multiply K
        (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w)‖) := by
  calc
    _ = ‖A.pressure κ m c hc hpos (J.word w -
        ((EulerSpatialSobolevInverse.SpatialJet.multiply K (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w)))‖ := by
      congr 1
      exact pressure_word_inverse K J κ m c hc hpos hn w
    _ ≤ _ := (A.pressure_norm κ m c hc hpos _).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hc.le))

end SpatialJet

end EulerPressureJetIdentities

end

section

/-! Sharp order-by-order Leibniz bounds for actual cylinder Sobolev jets. -/


namespace EulerJetProductBounds

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of the L² norms of all actual derivative words of one order. -/
def levelNorm {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) : ℝ :=
  match n, J with
  | 0, _ => ‖f‖
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, levelNorm (lower i) n
termination_by s

/-- The sum of the uniform bounds of all coefficient derivatives of one order. -/
def boundLevel {directions : Fin 4 → LiftTangent} {s : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) (n : ℕ) : ℝ :=
  match n, K with
  | 0, _ => A.bound
  | _ + 1, .zero _ => 0
  | n + 1, .succ _ lower _ => ∑ i, boundLevel (lower i) n
termination_by s

variable {period} {directions : Fin 4 → LiftTangent}

theorem levelNorm_nonneg {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    0 ≤ levelNorm period J n := by
  induction J generalizing n with
  | zero => cases n <;> simp [levelNorm]
  | succ df lower hd ih =>
    cases n with
    | zero => rw [levelNorm]; exact norm_nonneg _
    | succ n =>
      rw [levelNorm]
      exact Finset.sum_nonneg fun i _ => ih i

omit [Fact (0 < period)] in
theorem boundLevel_nonneg {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions s A) : 0 ≤ boundLevel period K n := by
  induction K generalizing n with
  | zero => cases n <;> simp [boundLevel]
  | succ dA lower hd ih =>
    cases n with
    | zero => rw [boundLevel]; exact NNReal.coe_nonneg _
    | succ n =>
      rw [boundLevel]
      exact Finset.sum_nonneg fun i _ => ih i

/-- The recursive level norm is exactly the finite sum over coordinate words. -/
theorem levelNorm_eq_words {s n : ℕ} {f : LiftL2 period} (J : SpatialJet period directions s f) :
    levelNorm period J n = ∑ w : Fin n → Fin 4, ‖J.word w‖ := by
  induction J generalizing n with
  | zero f => cases n <;> simp [levelNorm, SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp [levelNorm]
    | succ n =>
      rw [levelNorm, SpatialJet.sum_word_succ]
      exact Finset.sum_congr rfl fun i _ => ih i

theorem levelNorm_truncate {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions (s + 1) f) (hn : n ≤ s) :
    levelNorm period J.truncate n = levelNorm period J n := by
  induction s generalizing f n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [levelNorm]
  | succ s ih =>
    cases n with
    | zero => simp only [levelNorm]
    | succ n =>
      cases J with
      | succ df lower hd =>
        simp only [SpatialJet.truncate, levelNorm]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

omit [Fact (0 < period)] in
theorem boundLevel_truncate {s n : ℕ} {A : SmoothCoefficient period}
    (K : CoefficientJet period directions (s + 1) A) (hn : n ≤ s) :
    boundLevel period K.truncate n = boundLevel period K n := by
  induction s generalizing A n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    simp only [boundLevel]
  | succ s ih =>
    cases n with
    | zero => simp only [boundLevel]
    | succ n =>
      cases K with
      | succ dA lower hd =>
        simp only [CoefficientJet.truncate, boundLevel]
        exact Finset.sum_congr rfl fun i _ => ih (lower i) (by omega)

theorem levelNorm_add_le {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g) :
    levelNorm period (J.add K) n ≤ levelNorm period J n + levelNorm period K n := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, levelNorm, norm_add_le]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp only [levelNorm]; exact norm_add_le _ _
        | succ n =>
          rw [SpatialJet.add, levelNorm, levelNorm, levelNorm, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ => ih (lower i) (lowerG i)

/-- Binomial convolution of nonnegative derivative-order bounds. -/
def leibnizConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (n + 1)) (fun l => (n.choose l : ℝ) * A l * B (n - l))

theorem leibnizConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    leibnizConvolution A B (n + 1) =
      leibnizConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  simp only [leibnizConvolution, mul_assoc]
  rw [Finset.sum_choose_succ_mul (fun l r => A l * B r) n]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hln : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [show n + 1 - l = n - l + 1 by omega]

theorem leibnizConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    leibnizConvolution A B n = leibnizConvolution C D n := by
  apply Finset.sum_congr rfl
  intro l hl
  have hl : l ≤ n := by simpa using Finset.mem_range.mp hl
  rw [hA l hl, hB (n - l) (by omega)]

theorem sum_leibnizConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution A (B i) n) = leibnizConvolution A (fun l => ∑ i, B i l) n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum ..).symm

theorem sum_leibnizConvolution_left (A : Fin 4 → ℕ → ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (∑ i, leibnizConvolution (A i) B n) = leibnizConvolution (fun l => ∑ i, A i l) B n := by
  simp only [leibnizConvolution]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Sharp binomial Leibniz estimate for the actual product jet, at every finite derivative order. -/
theorem multiply_levelNorm_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (hn : n ≤ s) :
    levelNorm period (SpatialJet.multiply K J) n ≤
      leibnizConvolution (boundLevel period K) (levelNorm period J) n := by
  induction n generalizing s A f with
  | zero =>
    simpa [levelNorm, leibnizConvolution, boundLevel] using A.operator_norm f
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := CoefficientJet.succ dA lowerA hA
          let J := SpatialJet.succ df lowerF hF
          have hterm : ∀ i,
              levelNorm period ((SpatialJet.multiply K.truncate (lowerF i)).add
                (SpatialJet.multiply (lowerA i) J.truncate)) n ≤
              leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
              leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n ≤ s)
            have hright := ih (lowerA i) J.truncate (by omega : n ≤ s)
            have heqL : leibnizConvolution (boundLevel period K.truncate)
                (levelNorm period (lowerF i)) n =
                leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun l hl => boundLevel_truncate K (by omega)) (fun _ _ => rfl)
            have heqR : leibnizConvolution (boundLevel period (lowerA i))
                (levelNorm period J.truncate) n =
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n :=
              leibnizConvolution_congr _ _ _ _ n
                (fun _ _ => rfl) (fun l hl => levelNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact (levelNorm_add_le _ _).trans (add_le_add hleft hright)
          rw [SpatialJet.multiply, levelNorm]
          calc
            _ ≤ ∑ i, (leibnizConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n) :=
              Finset.sum_le_sum fun i _ => hterm i
            _ = leibnizConvolution (boundLevel period K)
                  (fun l => ∑ i, levelNorm period (lowerF i) l) n +
                leibnizConvolution (fun l => ∑ i, boundLevel period (lowerA i) l)
                  (levelNorm period J) n := by
              rw [Finset.sum_add_distrib, sum_leibnizConvolution_right, sum_leibnizConvolution_left]
            _ = leibnizConvolution (boundLevel period K) (levelNorm period J) (n + 1) := by
              rw [leibnizConvolution_succ]
              congr 2 <;> funext l <;> simp only [K, J, levelNorm, boundLevel]

theorem word_add {s n : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin n → Fin 4) : (J.add K).word w = J.word w + K.word w := by
  induction s generalizing f g n with
  | zero => cases J; cases K; cases n <;> simp [SpatialJet.add, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases n with
        | zero => simp
        | succ n =>
          simp only [SpatialJet.add, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- Binomial derivative convolution with its undifferentiated-coefficient term removed. -/
def commutatorConvolution (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  leibnizConvolution A B n - A 0 * B n

theorem commutatorConvolution_eq_sum (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B n =
      ∑ l ∈ Finset.range n, (n.choose (l + 1) : ℝ) * A (l + 1) * B (n - (l + 1)) := by
  rw [commutatorConvolution, leibnizConvolution, Finset.sum_range_succ']
  simp

theorem commutatorConvolution_congr (A B C D : ℕ → ℝ) (n : ℕ)
    (hA : ∀ l ≤ n, A l = C l) (hB : ∀ l ≤ n, B l = D l) :
    commutatorConvolution A B n = commutatorConvolution C D n := by
  rw [commutatorConvolution, commutatorConvolution, leibnizConvolution_congr A B C D n hA hB,
    hA 0 (Nat.zero_le n), hB n le_rfl]

theorem commutatorConvolution_succ (A B : ℕ → ℝ) (n : ℕ) :
    commutatorConvolution A B (n + 1) =
      commutatorConvolution A (fun k => B (k + 1)) n +
      leibnizConvolution (fun k => A (k + 1)) B n := by
  rw [commutatorConvolution, leibnizConvolution_succ, commutatorConvolution]
  ring

theorem sum_commutatorConvolution_right (A : ℕ → ℝ) (B : Fin 4 → ℕ → ℝ) (n : ℕ) :
    (∑ i, commutatorConvolution A (B i) n) =
      commutatorConvolution A (fun l => ∑ i, B i l) n := by
  simp only [commutatorConvolution]
  rw [Finset.sum_sub_distrib, sum_leibnizConvolution_right, Finset.mul_sum]

/-- The actual product commutator at one derivative order, summed over coordinate words. -/
def commutatorLevel {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖(SpatialJet.multiply K J).word w - A.operator (J.word w)‖

theorem sum_word_snoc (n : ℕ) (F : (Fin (n + 1) → Fin 4) → ℝ) :
    (∑ w, F w) = ∑ i, ∑ w : Fin n → Fin 4, F (Fin.snoc w i) := by
  calc
    _ = ∑ v : Fin 4 × (Fin n → Fin 4), F ((SpatialJet.wordSnocEquiv n).symm v) :=
      ((SpatialJet.wordSnocEquiv n).symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

theorem multiply_word_snoc {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lowerA : ∀ i, CoefficientJet period directions s (dA i))
    (hA : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (df : Fin 4 → LiftL2 period) (lowerF : ∀ i, SpatialJet period directions s (df i))
    (hF : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f)
      (df i) 0) (i : Fin 4) (w : Fin n → Fin 4) :
    (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA) (SpatialJet.succ df lowerF hF)).word
        (Fin.snoc w i) =
      (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w +
      (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w := by
  rw [SpatialJet.multiply, SpatialJet.word_succ]
  simp only [Fin.init_snoc, word_add, Fin.snoc, Fin.val_last, cast_eq]
  generalize hval : (if h : n < n then w ((Fin.last n).castLT h) else i) = j
  have hj : j = i := hval.symm.trans (dite_eq_right (Nat.lt_irrefl n))
  clear hval
  subst j
  rfl

theorem commutatorLevel_succ_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (dA : Fin 4 → SmoothCoefficient period)
    (lowerA : ∀ i, CoefficientJet period directions s (dA i))
    (hA : ∀ i x, (dA i).coefficient x = EulerTransportDerivatives.fieldDerivative period
      (directions i) A.coefficient x)
    (df : Fin 4 → LiftL2 period) (lowerF : ∀ i, SpatialJet period directions s (df i))
    (hF : ∀ i, HasDerivAt (fun t => translation period (translationPath period (directions i) t) f)
      (df i) 0) :
    commutatorLevel (CoefficientJet.succ dA lowerA hA) (SpatialJet.succ df lowerF hF) (n + 1) ≤
      ∑ i, (commutatorLevel (CoefficientJet.succ dA lowerA hA).truncate (lowerF i) n +
        levelNorm period (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate) n) := by
  rw [commutatorLevel, sum_word_snoc]
  apply Finset.sum_le_sum
  intro i _
  rw [commutatorLevel, levelNorm_eq_words, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  rw [multiply_word_snoc]
  simp only [SpatialJet.word_succ, Fin.init_snoc]
  simp only [Fin.snoc, Fin.val_last, cast_eq]
  generalize hval : (if h : n < n then w ((Fin.last n).castLT h) else i) = j
  have hj : j = i := hval.symm.trans (dite_eq_right (Nat.lt_irrefl n))
  clear hval
  subst j
  have heq : (SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w +
      (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w -
      A.operator ((lowerF i).word w) =
      ((SpatialJet.multiply (CoefficientJet.succ dA lowerA hA).truncate (lowerF i)).word w -
        A.operator ((lowerF i).word w)) +
        (SpatialJet.multiply (lowerA i) (SpatialJet.succ df lowerF hF).truncate).word w := by abel
  rw [heq]
  exact norm_add_le _ _
/-- Sharp all-order commutator estimate, with only positive coefficient derivative orders. -/
theorem commutatorLevel_le {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (hn : n ≤ s) :
    commutatorLevel K J n ≤
      commutatorConvolution (boundLevel period K) (levelNorm period J) n := by
  induction n generalizing s A f with
  | zero => simp [commutatorLevel, commutatorConvolution_eq_sum]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      cases K with
      | succ dA lowerA hA =>
        cases J with
        | succ df lowerF hF =>
          let K := CoefficientJet.succ dA lowerA hA
          let J := SpatialJet.succ df lowerF hF
          have hterm : ∀ i,
              commutatorLevel K.truncate (lowerF i) n +
                levelNorm period (SpatialJet.multiply (lowerA i) J.truncate) n ≤
              commutatorConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n := by
            intro i
            have hleft := ih K.truncate (lowerF i) (by omega : n ≤ s)
            have hright := multiply_levelNorm_le (lowerA i) J.truncate (by omega : n ≤ s)
            have heqL := commutatorConvolution_congr (boundLevel period K.truncate)
              (levelNorm period (lowerF i)) (boundLevel period K) (levelNorm period (lowerF i)) n
              (fun l hl => boundLevel_truncate K (by omega)) (fun _ _ => rfl)
            have heqR := leibnizConvolution_congr (boundLevel period (lowerA i))
              (levelNorm period J.truncate) (boundLevel period (lowerA i)) (levelNorm period J) n
              (fun _ _ => rfl) (fun l hl => levelNorm_truncate J (by omega))
            rw [heqL] at hleft
            rw [heqR] at hright
            exact add_le_add hleft hright
          calc
            _ ≤ ∑ i, (commutatorLevel K.truncate (lowerF i) n +
                levelNorm period (SpatialJet.multiply (lowerA i) J.truncate) n) :=
              commutatorLevel_succ_le dA lowerA hA df lowerF hF
            _ ≤ ∑ i, (commutatorConvolution (boundLevel period K) (levelNorm period (lowerF i)) n +
                leibnizConvolution (boundLevel period (lowerA i)) (levelNorm period J) n) :=
              Finset.sum_le_sum fun i _ => hterm i
            _ = commutatorConvolution (boundLevel period K)
                  (fun l => ∑ i, levelNorm period (lowerF i) l) n +
                leibnizConvolution (fun l => ∑ i, boundLevel period (lowerA i) l)
                  (levelNorm period J) n := by
              rw [Finset.sum_add_distrib, sum_commutatorConvolution_right, sum_leibnizConvolution_left]
            _ = commutatorConvolution (boundLevel period K) (levelNorm period J) (n + 1) := by
              rw [commutatorConvolution_succ]
              congr 2 <;> funext l <;> simp only [K, J, levelNorm, boundLevel]

/-- The all-order pressure recurrence for actual L² derivative words, with the entire
positive-order coefficient convolution derived from the product rule. -/
theorem pressure_level_recurrence {s n : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ) (hn : n ≤ s) :
    levelNorm period (J.solvePressure K κ m c hc hpos) n ≤ c⁻¹ *
      (levelNorm period J n + ∑ l ∈ Finset.range n,
        (n.choose (l + 1) : ℝ) * boundLevel period K (l + 1) *
          levelNorm period (J.solvePressure K κ m c hc hpos) (n - (l + 1))) := by
  let P := J.solvePressure K κ m c hc hpos
  have hw := fun w : Fin n → Fin 4 =>
    EulerPressureJetIdentities.SpatialJet.pressure_word_norm_le K J κ m c hc hpos hn w
  calc
    _ = ∑ w : Fin n → Fin 4, ‖P.word w‖ := levelNorm_eq_words P
    _ ≤ ∑ w : Fin n → Fin 4, c⁻¹ * (‖J.word w‖ +
        ‖(SpatialJet.multiply K P).word w - A.operator (P.word w)‖) :=
      Finset.sum_le_sum fun w _ => hw w
    _ = c⁻¹ * (levelNorm period J n + commutatorLevel K P n) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← levelNorm_eq_words]
      rfl
    _ ≤ c⁻¹ * (levelNorm period J n +
        commutatorConvolution (boundLevel period K) (levelNorm period P) n) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (commutatorLevel_le K P hn) _)
        (inv_nonneg.mpr hc.le)
    _ = _ := by rw [commutatorConvolution_eq_sum]

/-- A finite jet has no stored derivatives above its order. -/
theorem levelNorm_eq_zero_of_lt {s n : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (hn : s < n) : levelNorm period J n = 0 := by
  induction s generalizing f n with
  | zero =>
    cases J
    cases n with
    | zero => omega
    | succ n => rw [levelNorm]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases n with
      | zero => omega
      | succ n =>
        rw [levelNorm]
        apply Finset.sum_eq_zero
        intro i _
        exact ih (lower i) (by omega)

end EulerJetProductBounds

end

section

/-! Gevrey pressure regularity derived from actual cylinder derivative jets and coercivity. -/


namespace EulerPressureGevrey

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse
  EulerJetProductBounds EulerGevrey

variable (period : ℝ) [Fact (0 < period)]

/-- Every finite pressure solve obeys a Gevrey bound uniform in the cutoff order.
The triangular recurrence is derived from genuine strong translation derivatives. -/
theorem pressure_gevrey_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    levelNorm period (J.solvePressure K κ m c hc hpos) n ≤ majorant R (d + 1) n := by
  let P := J.solvePressure K κ m c hc hpos
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  have hz : ∀ j, 0 ≤ levelNorm period P j := fun _ => levelNorm_nonneg P
  have hf : ∀ j, 0 ≤ levelNorm period J j := fun _ => levelNorm_nonneg J
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (levelNorm period J) (levelNorm period P) _ _ n
  · intro j
    by_cases hj : j ≤ s
    · exact hsource j hj
    · rw [levelNorm_eq_zero_of_lt J (by omega)]
      exact majorant_nonneg R hR0 d j
  · intro j
    have hsum0 : 0 ≤ ∑ l ∈ Finset.range j,
        (j.choose (l + 1) : ℝ) * Rc ^ (l + 1) * ((l + 1).factorial : ℝ) ^ 2 *
          levelNorm period P (j - (l + 1)) := by
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (by positivity) (hz _)
    by_cases hj : j ≤ s
    · have hrec := pressure_level_recurrence K J κ m c hc hpos hj
      have hsum : (∑ l ∈ Finset.range j,
          (j.choose (l + 1) : ℝ) * boundLevel period K (l + 1) *
            levelNorm period P (j - (l + 1))) ≤
          ∑ l ∈ Finset.range j,
            (j.choose (l + 1) : ℝ) * Rc ^ (l + 1) * ((l + 1).factorial : ℝ) ^ 2 *
              levelNorm period P (j - (l + 1)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlj : l < j := Finset.mem_range.mp hl
        have hcoef := hcoeff (l + 1) (by omega) (by omega)
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (j.choose (l + 1)))) (hz (j - (l + 1)))
        simpa only [majorant, Nat.add_zero, mul_assoc] using hm
      exact hrec.trans ((mul_le_mul_of_nonneg_left (add_le_add_right hsum _) (inv_nonneg.mpr hc.le)).trans
        (mul_le_mul_of_nonneg_right hcM (add_nonneg (hf j) hsum0)))
    · rw [levelNorm_eq_zero_of_lt P (by omega)]
      exact mul_nonneg hM0 (add_nonneg (hf j) hsum0)

/-- The same Gevrey inverse estimate written as the actual sum over all coordinate derivative words. -/
theorem pressure_word_sum_majorant {directions : Fin 4 → LiftTangent}
    {s : ℕ} {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (M Rc R : ℝ) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M) (hRc : 0 ≤ Rc)
    (hR : 2 * M * (Rc + 1) ≤ R) (d : ℕ)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l)
    (hsource : ∀ n ≤ s, levelNorm period J n ≤ majorant R d n) (n : ℕ) :
    (∑ w : Fin n → Fin 4, ‖(J.solvePressure K κ m c hc hpos).word w‖) ≤ majorant R (d + 1) n := by
  rw [← levelNorm_eq_words]
  exact pressure_gevrey_majorant period K J κ m c hc hpos M Rc R hM hcM hRc hR d hcoeff hsource n

end EulerPressureGevrey

end

section

/-!
The smooth compactly supported limit step for the proposed Euler construction.
The hypotheses are summable uniform estimates for every actual iterated Fréchet
derivative of the increments. Smoothness and convergence of the limit are proved,
not assumed. The divergence is the usual coordinate trace of the first derivative.
-/

namespace EulerSmoothLimit

open Filter MeasureTheory
open scoped Topology ContDiff ENNReal

/-- The physical three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The trace of a continuous linear map, written in the standard Euclidean coordinates. -/
noncomputable def coordinateTrace : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ Space (EuclideanSpace.single i 1))

/-- The coordinate formula is exactly the basis-independent linear-algebraic trace. -/
theorem coordinateTrace_eq_linearTrace (A : Space →L[ℝ] Space) :
    coordinateTrace A = LinearMap.trace ℝ Space A.toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [coordinateTrace, Matrix.trace, LinearMap.toMatrix_apply]

/-- Classical divergence, defined canonically as the trace of the Fréchet derivative. -/
noncomputable def divergence (f : Space → Space) (x : Space) : ℝ :=
  LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap

theorem divergence_eq_coordinate_sum (f : Space → Space) (x : Space) :
    divergence f x = ∑ i : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) i := by
  rw [divergence, ← coordinateTrace_eq_linearTrace]
  simp [coordinateTrace]

theorem divergence_eq_trace (f : Space → Space) (x : Space) :
    divergence f x = LinearMap.trace ℝ Space (fderiv ℝ f x).toLinearMap :=
  rfl

/-- Order-zero bounds prove actual pointwise convergence of the series. -/
theorem summable_values (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (x : Space) :
    Summable (fun n => f n x) := by
  apply Summable.of_norm_bounded (hv 0)
  intro n
  simpa only [norm_iteratedFDeriv_zero] using hb 0 n x

/-- Uniform convergence of the ordinary sequence of finite partial sums. -/
theorem uniform_convergence (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) :
    TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x)
      (fun x => ∑' n, f n x) atTop := by
  apply tendstoUniformly_tsum_nat (hv 0)
  intro n x
  simpa only [norm_iteratedFDeriv_zero] using hb 0 n x

/-- Every order of differentiability is retained by the convergent series. -/
theorem contDiff_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) :
    ContDiff ℝ ∞ (fun x => ∑' n, f n x) := by
  exact contDiff_tsum hf (fun k _ => hv k) (fun k n x _ => hb k n x)

/-- All iterated derivatives of the sum are the sums of the actual derivatives. -/
theorem iterated_derivative_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (k : ℕ) (x : Space) :
    iteratedFDeriv ℝ k (fun y => ∑' n, f n y) x = ∑' n, iteratedFDeriv ℝ k (f n) x := by
  exact iteratedFDeriv_tsum_apply hf (fun j _ => hv j) (fun j n y _ => hb j n y) le_top x

/-- Uniform convergence holds separately at every derivative order. -/
theorem uniform_derivative_convergence (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (k : ℕ) :
    TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, iteratedFDeriv ℝ k (f n) x)
      (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) atTop := by
  rw [iteratedFDeriv_tsum hf (fun j _ => hv j) (fun j n x _ => hb j n x) le_top]
  exact tendstoUniformly_tsum_nat (hv k) (fun n x => hb k n x)

/-- A common closed support set also contains the topological support of the sum. -/
theorem tsupport_sum_subset (f : ℕ → Space → Space) (K : Set Space) (hK : IsClosed K)
    (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    tsupport (fun x => ∑' n, f n x) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  have hz : ∀ n, f n x = 0 := by
    intro n
    by_contra hn
    exact hxK (hsupp n hn)
  exact hx (by simp [hz])

/-- Compact support follows from the prescribed common compact set. -/
theorem compactSupport_sum (f : ℕ → Space → Space) (K : Set Space) (hK : IsCompact K)
    (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    HasCompactSupport (fun x => ∑' n, f n x) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_sum_subset f K hK.isClosed hsupp)

/-- The divergence of the series is the series of the divergences. -/
theorem divergence_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n) (x : Space) :
    divergence (fun y => ∑' n, f n y) x = ∑' n, divergence (f n) x := by
  have hd : ∀ n y, ‖fderiv ℝ (f n) y‖ ≤ v 1 n := by
    intro n y
    simpa only [norm_iteratedFDeriv_one] using hb 1 n y
  have hsd : Summable (fun n => fderiv ℝ (f n) x) :=
    Summable.of_norm_bounded (hv 1) (fun n => hd n x)
  simp only [divergence, ← coordinateTrace_eq_linearTrace]
  rw [fderiv_tsum_apply (hv 1) (fun n => (hf n).differentiable (by simp)) hd
    (summable_values f v hv hb (0 : Space)) x]
  exact coordinateTrace.map_tsum hsd

/-- The solenoidal condition is preserved by the series. -/
theorem divergence_free_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∀ x, divergence (fun y => ∑' n, f n y) x = 0 := by
  intro x
  rw [divergence_sum f v hf hv hb x]
  simp [hdiv]

/-- The common-support smooth limit belongs to every `L^p`, in particular to `L²`. -/
theorem memLp_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (p : ℝ≥0∞) : MemLp (fun x => ∑' n, f n x) p volume :=
  (contDiff_sum f v hf hv hb).continuous.memLp_of_hasCompactSupport
    (compactSupport_sum f K hK hsupp)

/-- Every derivative of the limit is also in every `L^p`. -/
theorem memLp_iterated_derivative_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (k : ℕ) (p : ℝ≥0∞) :
    MemLp (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) p volume := by
  have hc : Continuous (iteratedFDeriv ℝ k (fun x => ∑' n, f n x)) :=
    ContDiff.continuous_iteratedFDeriv (by simp) (contDiff_sum f v hf hv hb)
  exact hc.memLp_of_hasCompactSupport ((compactSupport_sum f K hK hsupp).iteratedFDeriv k)

/-- Finite kinetic energy is obtained as integrability of the squared Euclidean norm. -/
theorem finite_energy_sum (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K) :
    Integrable (fun x => ‖∑' n, f n x‖ ^ 2) volume :=
  (memLp_sum f v hf hv hb K hK hsupp 2).integrable_norm_pow (by norm_num)

/-- Odd parity also passes to the pointwise series. -/
theorem odd_sum (f : ℕ → Space → Space) (hodd : ∀ n x, f n (-x) = -f n x) :
    ∀ x, (∑' n, f n (-x)) = -(∑' n, f n x) := by
  intro x
  simp [hodd, tsum_neg]

/--
Constructs the limit initial velocity with all required qualitative properties.
The pointwise `HasSum` and uniform-convergence conclusions ensure the result is
the actual series, and every derivative order is shown to commute with that sum.
-/
theorem smooth_compact_solenoidal_limit (f : ℕ → Space → Space) (v : ℕ → ℕ → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hv : ∀ k, Summable (v k))
    (hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n)
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∃ u : Space → Space,
      (∀ x, HasSum (fun n => f n x) (u x)) ∧
      TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x) u atTop ∧
      ContDiff ℝ ∞ u ∧ tsupport u ⊆ K ∧ HasCompactSupport u ∧
      MemLp u 2 volume ∧ Integrable (fun x => ‖u x‖ ^ 2) volume ∧
      (∀ x, divergence u x = 0) ∧
      (∀ k x, iteratedFDeriv ℝ k u x = ∑' n, iteratedFDeriv ℝ k (f n) x) := by
  refine ⟨fun x => ∑' n, f n x, ?_⟩
  exact ⟨fun x => (summable_values f v hv hb x).hasSum,
    uniform_convergence f v hv hb,
    contDiff_sum f v hf hv hb,
    tsupport_sum_subset f K hK.isClosed hsupp,
    compactSupport_sum f K hK hsupp,
    memLp_sum f v hf hv hb K hK hsupp 2,
    finite_energy_sum f v hf hv hb K hK hsupp,
    divergence_free_sum f v hf hv hb hdiv,
    iterated_derivative_sum f v hf hv hb⟩

end EulerSmoothLimit

end

section

/-!
Actual Fourier Sobolev estimates on Euclidean spaces. The Sobolev norm below is
the L² norm of `(1 + |ξ|²)^(s/2) 𝓕f(ξ)`, so its relation to the represented
function is explicit. All estimates are proved from inversion and Hölder.
-/

namespace EulerSobolev

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

/-- The real Euclidean domain of dimension `d`. -/
abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Fourier weight defining the inhomogeneous Sobolev order `s`. -/
noncomputable def besselWeight (d : ℕ) (s : ℝ) (ξ : Domain d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselWeight_temperate (d : ℕ) (s : ℝ) :
    (besselWeight d s).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Domain d) (s / 2)

theorem besselWeight_pos (d : ℕ) (s : ℝ) (ξ : Domain d) : 0 < besselWeight d s ξ := by
  unfold besselWeight
  positivity

theorem besselWeight_neg_mul (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d (-s) ξ * besselWeight d s ξ = 1 := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  have he : -s / 2 + s / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem besselWeight_add (d : ℕ) (s t : ℝ) (ξ : Domain d) :
    besselWeight d (s + t) ξ = besselWeight d s ξ * besselWeight d t ξ := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- One derivative factor is absorbed by one Sobolev order. -/
theorem besselWeight_mul_norm_le (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d s ξ * ‖ξ‖ ≤ besselWeight d (s + 1) ξ := by
  have hn : ‖ξ‖ ≤ besselWeight d 1 ξ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    calc
      ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ξ)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [besselWeight_add]
  exact mul_le_mul_of_nonneg_left hn (besselWeight_pos d s ξ).le

/-- The reciprocal Bessel weight is in L² exactly in the range needed here. -/
theorem reciprocal_weight_memLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    MemLp (besselWeight d (-s)) 2 (volume : Measure (Domain d)) := by
  have hm : AEStronglyMeasurable (besselWeight d (-s)) (volume : Measure (Domain d)) :=
    (besselWeight_temperate d (-s)).1.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have hi : Integrable (fun ξ : Domain d => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa [Domain] using hs)
  apply hi.congr
  filter_upwards with ξ
  dsimp only [besselWeight]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- The reciprocal Fourier weight represented as a genuine `L²` element. -/
noncomputable def reciprocalWeightLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (reciprocal_weight_memLp d s hs).toLp (besselWeight d (-s))

/-- A finite Sobolev embedding constant: the `L²` norm of the reciprocal weight. -/
noncomputable def embeddingConstant (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) : ℝ :=
  ‖reciprocalWeightLp d s hs‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fourier transform multiplied by the Sobolev weight. -/
noncomputable def weightedFourier (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) :=
  SchwartzMap.smulLeftCLM F (besselWeight d s) (𝓕 f)

omit [CompleteSpace F] in
theorem weightedFourier_apply (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    weightedFourier d s f ξ = besselWeight d s ξ • 𝓕 f ξ := by
  simp [weightedFourier, SchwartzMap.smulLeftCLM_apply_apply (besselWeight_temperate d s)]

/-- The inhomogeneous Fourier `Hˢ` norm of a Schwartz function. -/
noncomputable def sobolevNorm (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) : ℝ :=
  ‖(weightedFourier d s f).toLp 2‖

/-- Fourier inversion bounds a Schwartz function pointwise by the L¹ norm of its transform. -/
theorem norm_apply_le_fourier_L1 (d : ℕ) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖ := by
  have h := SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
  have he : ‖f x‖ = ‖𝓕 (𝓕 f) (-x)‖ := by
    change ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖
    rw [fourierInv_fourier_eq]
  exact he ▸ h

omit [CompleteSpace F] in
/-- Hölder with the reciprocal weight converts the Fourier L¹ norm into the Hˢ norm. -/
theorem fourier_L1_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) :
    ‖(𝓕 f).toLp 1‖ ≤ embeddingConstant d s hs * sobolevNorm d s f := by
  have hid : (besselWeight d (-s) • (weightedFourier d s f : Domain d → F)) =
      ((𝓕 f : 𝓢(Domain d, F)) : Domain d → F) := by
    ext ξ
    simp only [Pi.smul_apply', weightedFourier_apply, smul_smul, besselWeight_neg_mul, one_smul]
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    ((weightedFourier d s f).memLp 2 volume).1 (reciprocal_weight_memLp d s hs).1
  rw [hid] at hh
  have hfin : eLpNorm (besselWeight d (-s)) 2 volume *
      eLpNorm (weightedFourier d s f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (reciprocal_weight_memLp d s hs).eLpNorm_ne_top
      ((weightedFourier d s f).memLp 2 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin hh
  simpa only [SchwartzMap.norm_toLp, embeddingConstant, reciprocalWeightLp,
    Lp.norm_toLp, sobolevNorm, ENNReal.toReal_mul] using h

/-- A genuine pointwise Sobolev embedding for every `s > d/2`. -/
theorem norm_apply_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ embeddingConstant d s hs * sobolevNorm d s f :=
  (norm_apply_le_fourier_L1 d f x).trans (fourier_L1_le_sobolevNorm d s hs f)

open scoped LineDeriv

omit [CompleteSpace F] in
/-- The actual Fourier multiplier formula bounds each directional derivative. -/
theorem fourier_lineDeriv_norm_le (d : ℕ) (f : 𝓢(Domain d, F)) (m ξ : Domain d) :
    ‖𝓕 (∂_{m} f) ξ‖ ≤ (2 * Real.pi) * ‖ξ‖ * ‖m‖ * ‖𝓕 f ξ‖ := by
  have ht : (fun ξ : Domain d => inner ℝ ξ m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have he : 𝓕 (∂_{m} f) ξ = (2 * Real.pi * Complex.I) • ((inner ℝ ξ m) • 𝓕 f ξ) := by
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    simp [SchwartzMap.smulLeftCLM_apply_apply ht]
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [he, norm_smul, norm_smul, hc]
  have hi := norm_inner_le_norm (𝕜 := ℝ) ξ m
  nlinarith [mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hi (norm_nonneg (𝓕 f ξ))) (show 0 ≤ 2 * Real.pi by positivity)]

omit [CompleteSpace F] in
theorem weightedFourier_lineDeriv_norm_le (d : ℕ) (s : ℝ)
    (f : 𝓢(Domain d, F)) (m ξ : Domain d) :
    ‖weightedFourier d s (∂_{m} f) ξ‖ ≤
      (2 * Real.pi * ‖m‖) * ‖weightedFourier d (s + 1) f ξ‖ := by
  rw [weightedFourier_apply, weightedFourier_apply, norm_smul, norm_smul,
    Real.norm_of_nonneg (besselWeight_pos d s ξ).le,
    Real.norm_of_nonneg (besselWeight_pos d (s + 1) ξ).le]
  calc
    _ ≤ besselWeight d s ξ * ((2 * Real.pi) * ‖ξ‖ * ‖m‖ * ‖𝓕 f ξ‖) :=
      mul_le_mul_of_nonneg_left (fourier_lineDeriv_norm_le d f m ξ) (besselWeight_pos d s ξ).le
    _ = (2 * Real.pi * ‖m‖) * (besselWeight d s ξ * ‖ξ‖) * ‖𝓕 f ξ‖ := by ring
    _ ≤ (2 * Real.pi * ‖m‖) * besselWeight d (s + 1) ξ * ‖𝓕 f ξ‖ := by
      gcongr
      exact besselWeight_mul_norm_le d s ξ
    _ = _ := by ring

omit [CompleteSpace F] in
/-- A directional derivative maps H^(s+1) to H^s with its explicit Fourier factor. -/
theorem sobolevNorm_lineDeriv_le (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (m : Domain d) :
    sobolevNorm d s (∂_{m} f) ≤ (2 * Real.pi * ‖m‖) * sobolevNorm d (s + 1) f := by
  unfold sobolevNorm
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(weightedFourier d s (∂_{m} f)).coeFn_toLp 2,
    (weightedFourier d (s + 1) f).coeFn_toLp 2] with ξ hd hf
  rw [hd, hf]
  exact weightedFourier_lineDeriv_norm_le d s f m ξ

omit [CompleteSpace F] in
/-- Iterating the Fourier multiplier estimate loses exactly one Sobolev order per derivative. -/
theorem sobolevNorm_iteratedLineDeriv_le (d k : ℕ) (s : ℝ)
    (f : 𝓢(Domain d, F)) (m : Fin k → Domain d) :
    sobolevNorm d s (∂^{m} f) ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * sobolevNorm d (s + k) f := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    calc
      _ ≤ (2 * Real.pi * ‖m 0‖) * sobolevNorm d (s + 1) (∂^{Fin.tail m} f) :=
        sobolevNorm_lineDeriv_le d s (∂^{Fin.tail m} f) (m 0)
      _ ≤ (2 * Real.pi * ‖m 0‖) *
          ((2 * Real.pi) ^ k * (∏ i, ‖Fin.tail m i‖) *
            sobolevNorm d ((s + 1) + k) f) := by
        gcongr
        exact ih (s + 1) (Fin.tail m)
      _ = _ := by
        rw [Fin.prod_univ_succ, pow_succ]
        have he : (s + 1) + (k : ℝ) = s + (↑(k + 1) : ℝ) := by push_cast; ring
        rw [he]
        simp only [Fin.tail]
        ring

/-- Sobolev embedding controls the operator norm of every actual Fréchet derivative. -/
theorem iteratedFDeriv_norm_le_sobolevNorm (d k : ℕ) (s : ℝ)
    (hs : (d : ℝ) < 2 * s) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant d s hs * (2 * Real.pi) ^ k * sobolevNorm d (s + k) f := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by
    unfold embeddingConstant sobolevNorm
    positivity)
  intro m
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  calc
    _ ≤ embeddingConstant d s hs * sobolevNorm d s (∂^{m} f) :=
      norm_apply_le_sobolevNorm d s hs (∂^{m} f) x
    _ ≤ embeddingConstant d s hs *
        ((2 * Real.pi) ^ k * (∏ i, ‖m i‖) * sobolevNorm d (s + k) f) :=
      mul_le_mul_of_nonneg_left (sobolevNorm_iteratedLineDeriv_le d k s f m) (norm_nonneg _)
    _ = _ := by ring

/-- Coordinatewise complexification is an actual linear isometry of Euclidean spaces. -/
noncomputable def complexify (q : ℕ) :
    Domain q →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin q) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

/-- Coordinatewise isometric complexification of a real Schwartz vector field. -/
noncomputable def complexifySchwartz (d q : ℕ) (f : 𝓢(Domain d, Domain q)) :
    𝓢(Domain d, EuclideanSpace ℂ (Fin q)) :=
  SchwartzMap.postcompCLM (complexify q).toContinuousLinearMap f

/-- The usual Fourier Hˢ norm of a real vector field, via isometric complexification. -/
noncomputable def realSobolevNorm (d q : ℕ) (s : ℝ) (f : 𝓢(Domain d, Domain q)) : ℝ :=
  sobolevNorm d s (complexifySchwartz d q f)

theorem complexifySchwartz_iteratedFDeriv_norm (d q k : ℕ)
    (f : 𝓢(Domain d, Domain q)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k (complexifySchwartz d q f) x‖ = ‖iteratedFDeriv ℝ k f x‖ := by
  change ‖iteratedFDeriv ℝ k ((complexify q) ∘ f) x‖ = _
  exact (complexify q).norm_iteratedFDeriv_comp_left f.smooth'.contDiffAt (by simp)

/-- Sobolev embedding for genuine real Euclidean vector fields and all derivative orders. -/
theorem real_iteratedFDeriv_norm_le_sobolevNorm (d q k : ℕ) (s : ℝ)
    (hs : (d : ℝ) < 2 * s) (f : 𝓢(Domain d, Domain q)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant d s hs * (2 * Real.pi) ^ k * realSobolevNorm d q (s + k) f := by
  rw [← complexifySchwartz_iteratedFDeriv_norm d q k f x]
  exact iteratedFDeriv_norm_le_sobolevNorm d k s hs (complexifySchwartz d q f) x

/-- On ℝ³, `H^(k+2)` controls every derivative of order `k`. In particular, `H³ → C¹`. -/
theorem real_three_dimensional_sobolev (q k : ℕ)
    (f : 𝓢(Domain 3, Domain q)) (x : Domain 3) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
        realSobolevNorm 3 q (2 + k) f :=
  real_iteratedFDeriv_norm_le_sobolevNorm 3 q k 2 (by norm_num) f x

/-- On ℝ⁴, `H^(k+3)` controls every derivative of order `k`. -/
theorem real_four_dimensional_sobolev (q k : ℕ)
    (f : 𝓢(Domain 4, Domain q)) (x : Domain 4) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 4 3 (by norm_num) * (2 * Real.pi) ^ k *
        realSobolevNorm 4 q (3 + k) f :=
  real_iteratedFDeriv_norm_le_sobolevNorm 4 q k 3 (by norm_num) f x

/-- The same concrete Fourier norm, now for an unbundled smooth compactly supported field. -/
noncomputable def compactSobolevNorm (d q : ℕ) (s : ℝ) (f : Domain d → Domain q)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℝ :=
  realSobolevNorm d q s (hc.toSchwartzMap hf)

theorem compact_iteratedFDeriv_norm_le (q k : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
        compactSobolevNorm 3 q (2 + k) f hf hc :=
  real_three_dimensional_sobolev q k (hc.toSchwartzMap hf) x

open Filter EulerSmoothLimit

/--
The all-order Sobolev estimates construct the actual smooth, compactly supported,
finite-energy solenoidal limit. Uniform derivative bounds are derived by Fourier
analysis inside the proof, rather than supplied as an additional hypothesis.
-/
theorem smooth_compact_solenoidal_limit_of_sobolev
    (f : ℕ → Space → Space) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hc : ∀ n, HasCompactSupport (f n))
    (hSob : ∀ k : ℕ, Summable (fun n =>
      compactSobolevNorm 3 3 (2 + k) (f n) (hf n) (hc n)))
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∃ u : Space → Space,
      (∀ x, HasSum (fun n => f n x) (u x)) ∧
      TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x) u atTop ∧
      ContDiff ℝ ∞ u ∧ tsupport u ⊆ K ∧ HasCompactSupport u ∧
      MemLp u 2 volume ∧ Integrable (fun x => ‖u x‖ ^ 2) volume ∧
      (∀ x, divergence u x = 0) ∧
      (∀ k x, iteratedFDeriv ℝ k u x = ∑' n, iteratedFDeriv ℝ k (f n) x) := by
  let v : ℕ → ℕ → ℝ := fun k n =>
    embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
      compactSobolevNorm 3 3 (2 + k) (f n) (hf n) (hc n)
  have hv : ∀ k, Summable (v k) := fun k => (hSob k).mul_left _
  have hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n :=
    fun k n x => compact_iteratedFDeriv_norm_le 3 k (f n) (hf n) (hc n) x
  exact EulerSmoothLimit.smooth_compact_solenoidal_limit f v hf hv hb K hK hsupp hdiv

end EulerSobolev

end

section

namespace EulerSobolevProducts

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal ContDiff LineDeriv Convolution

theorem sobolevNorm_zero (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 0 f = ‖f.toLp 2‖ := by
  have he : weightedFourier d 0 f = 𝓕 f := by
    ext ξ
    simp [weightedFourier_apply, besselWeight]
  simp [sobolevNorm, he]

theorem besselWeight_mono (d : ℕ) {s t : ℝ} (hst : s ≤ t) (ξ : Domain d) :
    besselWeight d s ξ ≤ besselWeight d t ξ := by
  apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖])
  exact div_le_div_of_nonneg_right hst (by norm_num)

theorem sobolevNorm_mono (d : ℕ) {s t : ℝ} (hst : s ≤ t) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d s f ≤ sobolevNorm d t f := by
  unfold sobolevNorm
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(weightedFourier d s f).coeFn_toLp 2,
    (weightedFourier d t f).coeFn_toLp 2] with ξ hs ht
  rw [hs, ht, weightedFourier_apply, weightedFourier_apply, norm_smul, norm_smul,
    Real.norm_of_nonneg (besselWeight_pos d s ξ).le,
    Real.norm_of_nonneg (besselWeight_pos d t ξ).le]
  exact mul_le_mul_of_nonneg_right (besselWeight_mono d hst ξ) (norm_nonneg _)

/-- Repeated differentiation in one fixed direction, as a Schwartz function. -/
noncomputable def directional (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) := ∂^{fun _ : Fin n => v} f

theorem directional_eq_iteratedDeriv (d n : ℕ) (v x : Domain d)
    (f : 𝓢(Domain d, ℂ)) :
    directional d n v f x = iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 := by
  rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] Domain d := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hC : ContDiff ℝ ∞ (fun z => f (x + z)) := f.smooth'.comp (contDiff_const.add contDiff_id)
  have he := L.iteratedFDeriv_comp_right hC (0 : ℝ) (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change iteratedFDeriv ℝ n f x (fun _ => v) = _
  change _ = iteratedFDeriv ℝ n ((fun z => f (x + z)) ∘ L) 0 (fun _ => 1)
  rw [he]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]

/-- Pointwise multiplication of two complex Schwartz functions. -/
noncomputable def product (d : ℕ) (f g : 𝓢(Domain d, ℂ)) : 𝓢(Domain d, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem product_apply (d : ℕ) (f g : 𝓢(Domain d, ℂ)) (x : Domain d) :
    product d f g x = f x * g x := rfl

theorem directional_product (d n : ℕ) (v : Domain d) (f g : 𝓢(Domain d, ℂ)) :
    directional d n v (product d f g) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) •
        product d (directional d j v f) (directional d (n-j) v g) := by
  ext x
  simp only [directional_eq_iteratedDeriv, product_apply, sum_apply,
    smul_apply, smul_eq_mul]
  have hf : ContDiff ℝ ∞ (fun t : ℝ => f (x + t • v)) :=
    f.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg : ContDiff ℝ ∞ (fun t : ℝ => g (x + t • v)) :=
    g.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  simpa only [Pi.mul_apply, mul_assoc] using iteratedDeriv_fun_mul
    (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt

theorem directional_L2_le (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d n v f).toLp 2‖ ≤
      (2 * Real.pi) ^ n * ‖v‖ ^ n * sobolevNorm d n f := by
  rw [← sobolevNorm_zero]
  simpa [directional] using sobolevNorm_iteratedLineDeriv_le d n 0 f (fun _ => v)

theorem besselWeight_six_le_pure_six (d : ℕ) (ξ : Domain d) :
    besselWeight d 6 ξ ≤ ((d : ℝ) + 1) ^ 2 * (1 + ∑ i, ‖ξ i‖ ^ 6) := by
  let a : Option (Fin d) → ℝ := fun i => match i with
    | none => 1
    | some i => ‖ξ i‖ ^ 2
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ a i := by
    intro i _
    cases i <;> simp only [a] <;> positivity
  have h := pow_sum_le_card_mul_sum_pow ha 2
  have he : besselWeight d 6 ξ = (1 + ∑ i, ‖ξ i‖ ^ 2) ^ 3 := by
    norm_num [besselWeight, EuclideanSpace.norm_sq_eq]
  rw [he]
  have hp (i : Fin d) : ‖ξ i‖ ^ 6 = (ξ i) ^ 6 := by
    exact (by decide : Even 6).pow_abs (ξ i)
  simp only [hp]
  simpa [a, Fintype.sum_option, ← pow_mul, Nat.mul_comm] using h

theorem fourier_directional_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, ℂ)) (ξ : Domain d) :
    ‖𝓕 (directional d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [directional]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : directional d (n+1) v f = ∂_{v} (directional d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, ℂ))
    (g : ι → 𝓢(Domain d, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]

theorem sobolevNorm_six_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 6 f ≤ ((d : ℝ) + 1) ^ 2 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-6 : ℤ) *
        ∑ i : Fin d, ‖(directional d 6 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, ℂ) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-6 : ℤ) : ℝ) •
        𝓕 (directional d 6 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 6 f ξ‖ ≤ ((d : ℝ) + 1) ^ 2 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 6 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 6) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ)),
        fourier_directional_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-6 : ℤ) * (2 * Real.pi) ^ (6 : ℕ) = 1 := by
        rw [show (-6 : ℤ) = -(6 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (besselWeight_six_le_pure_six d ξ) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 6 f) g (((d : ℝ) + 1) ^ 2)
    (sq_nonneg _) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-6 : ℤ) * ∑ i : Fin d,
        ‖(directional d 6 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (((2 * Real.pi) ^ (-6 : ℤ)) •
        𝓕 (directional d 6 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

theorem product_L2_le_of_sup (d : ℕ) (f g : 𝓢(Domain d, ℂ)) (A : ℝ)
    (hA : ∀ x, ‖f x‖ ≤ A) : ‖(product d f g).toLp 2‖ ≤ A * ‖g.toLp 2‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(product d f g).coeFn_toLp 2, g.coeFn_toLp 2] with x hp hg
  rw [hp, hg, product_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

theorem directional_sup_le_H6 (d j : ℕ) (hd : (d : ℝ) < 2 * 3) (hj : j ≤ 3)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f : 𝓢(Domain d, ℂ)) (x : Domain d) :
    ‖directional d j v f x‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 6 f := by
  have hC : 0 ≤ embeddingConstant d 3 hd := norm_nonneg _
  have hS : 0 ≤ sobolevNorm d (3+j) f := norm_nonneg _
  have hb := sobolevNorm_iteratedLineDeriv_le d j 3 f (fun _ : Fin j => v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hs : sobolevNorm d (3 + j) f ≤ sobolevNorm d 6 f :=
    sobolevNorm_mono d (by exact_mod_cast (show 3 + j ≤ 6 by omega)) f
  calc
    _ ≤ embeddingConstant d 3 hd * sobolevNorm d 3 (directional d j v f) :=
      norm_apply_le_sobolevNorm d 3 hd _ x
    _ ≤ embeddingConstant d 3 hd *
        ((2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d (3 + j) f) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ embeddingConstant d 3 hd * ((2 * Real.pi) ^ j * 1 * sobolevNorm d 6 f) := by
      gcongr
    _ = _ := by ring

theorem directional_L2_le_H6 (d j : ℕ) (hj : j ≤ 6) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d j v f).toLp 2‖ ≤ (2 * Real.pi) ^ j * sobolevNorm d 6 f := by
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hS : 0 ≤ sobolevNorm d j f := norm_nonneg _
  have hmono : sobolevNorm d j f ≤ sobolevNorm d 6 f :=
    sobolevNorm_mono d (s := (j : ℝ)) (t := 6) (by exact_mod_cast hj) f
  calc
    _ ≤ (2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d j f := directional_L2_le d j v f
    _ ≤ (2 * Real.pi) ^ j * 1 * sobolevNorm d 6 f := by
      gcongr
    _ = _ := by ring

attribute [local irreducible] sobolevNorm embeddingConstant

theorem product_directional_L2_le_left (d j k : ℕ) (hd : (d : ℝ) < 2 * 3)
    (hj : j ≤ 3) (hk : k ≤ 6) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  have hC : 0 ≤ embeddingConstant d 3 hd := by unfold embeddingConstant; exact norm_nonneg _
  have hS : 0 ≤ sobolevNorm d 6 f := by unfold sobolevNorm; exact norm_nonneg _
  have hA := product_L2_le_of_sup d (directional d j v f) (directional d k v g)
    (embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 6 f)
    (directional_sup_le_H6 d j hd hj v hv f)
  have hB := mul_le_mul_of_nonneg_left (directional_L2_le_H6 d k hk v hv g)
    (mul_nonneg (mul_nonneg hC (by positivity : 0 ≤ (2 * Real.pi) ^ j)) hS)
  have harith (A B C p : ℝ) : (C * p ^ j * A) * (p ^ k * B) =
      C * p ^ (j+k) * A * B := by rw [pow_add]; ring
  exact hA.trans (hB.trans_eq (harith _ _ _ _))

theorem product_directional_L2_le (d j k : ℕ) (hd : (d : ℝ) < 2 * 3) (hjk : j+k ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  by_cases hj : j ≤ 3
  · exact product_directional_L2_le_left d j k hd hj (by omega) v hv f g
  · have he : product d (directional d j v f) (directional d k v g) =
        product d (directional d k v g) (directional d j v f) := by
      ext x
      simp [mul_comm]
    rw [he]
    have h := product_directional_L2_le_left d k j hd (by omega) (by omega) v hv g f
    rw [Nat.add_comm k j] at h
    convert h using 1; ring

theorem directional_product_L2_le (d n : ℕ) (hd : (d : ℝ) < 2 * 3) (hn : n ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(directional d n v (product d f g)).toLp 2‖ ≤
      2 ^ n * (embeddingConstant d 3 hd * (2 * Real.pi) ^ n *
        sobolevNorm d 6 f * sobolevNorm d 6 g) := by
  rw [directional_product]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
      product d (directional d j v f) (directional d (n-j) v g))‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1),
        ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume ((n.choose j : ℂ) •
          product d (directional d j v f) (directional d (n-j) v g))‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ‖(product d (directional d j v f) (directional d (n-j) v g)).toLp 2‖ := by
      simp only [map_smul, norm_smul, Complex.norm_natCast, SchwartzMap.toLpCLM_apply]
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        (embeddingConstant d 3 hd * (2 * Real.pi) ^ n *
          sobolevNorm d 6 f * sobolevNorm d 6 g) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa using (Finset.mem_range.1 hj)
      have h := product_directional_L2_le d j (n-j) hd (by omega) v hv f g
      rw [Nat.add_sub_of_le hjn] at h
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n

/-- A concrete algebra constant, obtained by Leibniz, Plancherel and the Sobolev embedding. -/
theorem sobolevNorm_six_product (d : ℕ) (hd : (d : ℝ) < 2 * 3) (f g : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 6 (product d f g) ≤
      (((d : ℝ) + 1) ^ 2 * (1 + 64 * d) * embeddingConstant d 3 hd) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  have hzero : ‖(product d f g).toLp 2‖ ≤
      embeddingConstant d 3 hd * sobolevNorm d 6 f * sobolevNorm d 6 g := by
    simpa only [directional, LineDeriv.iteratedLineDerivOp_fin_zero, pow_zero, one_mul,
      mul_one] using directional_product_L2_le d 0 hd (by omega)
      0 (by simp) f g
  have hsix (i : Fin d) :
      ‖(directional d 6 (EuclideanSpace.single i 1) (product d f g)).toLp 2‖ ≤
        64 * (embeddingConstant d 3 hd * (2 * Real.pi) ^ 6 *
          sobolevNorm d 6 f * sobolevNorm d 6 g) := by
    have h := directional_product_L2_le d 6 hd (by omega)
      (EuclideanSpace.single i 1) (by simp) f g
    rw [show (2 : ℝ) ^ 6 = 64 by norm_num] at h
    exact h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hsix i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hp : (2 * Real.pi) ^ (-6 : ℤ) * (2 * Real.pi) ^ (6 : ℕ) = 1 := by
    rw [show (-6 : ℤ) = -(6 : ℤ) from rfl, zpow_neg]
    exact inv_mul_cancel₀ (by positivity)
  have harith (D C A B p r : ℝ) (hpr : r * p = 1) :
      (D + 1) ^ 2 * (C*A*B + r*(D*(64*(C*p*A*B)))) =
      ((D + 1) ^ 2 * (1 + 64*D) * C) * A * B := by
    linear_combination ((D + 1) ^ 2 * (64*D) * C * A * B) * hpr
  have hA := sobolevNorm_six_le_pure_derivatives d (product d f g)
  have hB := mul_le_mul_of_nonneg_left
    (add_le_add hzero (mul_le_mul_of_nonneg_left hsum
      (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ))))
    (sq_nonneg ((d : ℝ) + 1))
  exact hA.trans (hB.trans_eq (harith _ _ _ _ _ _ hp))

/-- The fixed four-dimensional `H⁶` algebra estimate used in the packet energy argument. -/
theorem four_dimensional_H6_algebra (f g : 𝓢(Domain 4, ℂ)) :
    sobolevNorm 4 6 (product 4 f g) ≤
      (6425 * embeddingConstant 4 3 (by norm_num)) *
        sobolevNorm 4 6 f * sobolevNorm 4 6 g := by
  convert sobolevNorm_six_product 4 (by norm_num) f g using 1; norm_num

end EulerSobolevProducts

end

-- Component: SobolevTransport.lean

section

/-!
The fixed-order transport commutator estimate.
-/

namespace EulerSobolevTransport

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv


theorem directional_sup_le_H5 (d j : ℕ) (hd : (d : ℝ) < 2 * 3) (hj : j ≤ 2)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f : 𝓢(Domain d, ℂ)) (x : Domain d) :
    ‖directional d j v f x‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 5 f := by
  have hC : 0 ≤ embeddingConstant d 3 hd := norm_nonneg _
  have hS : 0 ≤ sobolevNorm d (3+j) f := norm_nonneg _
  have hb := sobolevNorm_iteratedLineDeriv_le d j 3 f (fun _ : Fin j => v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hs : sobolevNorm d (3 + j) f ≤ sobolevNorm d 5 f :=
    sobolevNorm_mono d (by exact_mod_cast (show 3 + j ≤ 5 by omega)) f
  calc
    _ ≤ embeddingConstant d 3 hd * sobolevNorm d 3 (directional d j v f) :=
      norm_apply_le_sobolevNorm d 3 hd _ x
    _ ≤ embeddingConstant d 3 hd *
        ((2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d (3 + j) f) :=
      mul_le_mul_of_nonneg_left hb hC
    _ ≤ embeddingConstant d 3 hd * ((2 * Real.pi) ^ j * 1 * sobolevNorm d 5 f) := by
      gcongr
    _ = _ := by ring

theorem directional_L2_le_H5 (d j : ℕ) (hj : j ≤ 5) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d j v f).toLp 2‖ ≤ (2 * Real.pi) ^ j * sobolevNorm d 5 f := by
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hS : 0 ≤ sobolevNorm d j f := norm_nonneg _
  have hmono : sobolevNorm d j f ≤ sobolevNorm d 5 f :=
    sobolevNorm_mono d (s := (j : ℝ)) (t := 5) (by exact_mod_cast hj) f
  calc
    _ ≤ (2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d j f := directional_L2_le d j v f
    _ ≤ (2 * Real.pi) ^ j * 1 * sobolevNorm d 5 f := by gcongr
    _ = _ := by ring

attribute [local irreducible] sobolevNorm embeddingConstant

theorem product_directional_L2_H5_left (d j k : ℕ) (hd : (d : ℝ) < 2 * 3)
    (hj : j ≤ 2) (hk : k ≤ 5) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 5 f * sobolevNorm d 5 g := by
  have hC : 0 ≤ embeddingConstant d 3 hd := by unfold embeddingConstant; exact norm_nonneg _
  have hS : 0 ≤ sobolevNorm d 5 f := by unfold sobolevNorm; exact norm_nonneg _
  have hA := product_L2_le_of_sup d (directional d j v f) (directional d k v g)
    (embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 5 f)
    (directional_sup_le_H5 d j hd hj v hv f)
  have hB := mul_le_mul_of_nonneg_left (directional_L2_le_H5 d k hk v hv g)
    (mul_nonneg (mul_nonneg hC (by positivity : 0 ≤ (2 * Real.pi) ^ j)) hS)
  have harith (A B C p : ℝ) : (C * p ^ j * A) * (p ^ k * B) =
      C * p ^ (j+k) * A * B := by rw [pow_add]; ring
  exact hA.trans (hB.trans_eq (harith _ _ _ _))

theorem product_directional_L2_H5 (d j k : ℕ) (hd : (d : ℝ) < 2 * 3) (hjk : j+k ≤ 5)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 5 f * sobolevNorm d 5 g := by
  by_cases hj : j ≤ 2
  · exact product_directional_L2_H5_left d j k hd hj (by omega) v hv f g
  · have he : product d (directional d j v f) (directional d k v g) =
        product d (directional d k v g) (directional d j v f) := by
      ext x
      simp [mul_comm]
    rw [he]
    have h := product_directional_L2_H5_left d k j hd (by omega) (by omega) v hv g f
    rw [Nat.add_comm k j] at h
    convert h using 1; ring

/-- The actual commutator of an iterated directional derivative with multiplication. -/
noncomputable def commutator (d n : ℕ) (v : Domain d) (b h : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) :=
  directional d n v (product d b h) - product d b (directional d n v h)

theorem directional_succ_right (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    directional d (n+1) v f = directional d n v (directional d 1 v f) := by
  simp [directional, LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_def]

theorem commutator_expansion (d n : ℕ) (v : Domain d) (b h : 𝓢(Domain d, ℂ)) :
    commutator d n v b h = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      product d (directional d j v (directional d 1 v b)) (directional d (n-(j+1)) v h) := by
  unfold commutator
  rw [directional_product, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, directional,
    LineDeriv.iteratedLineDerivOp_fin_zero, Nat.sub_zero, one_smul, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact directional_succ_right d j v b

theorem sum_choose_successors_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ)) ≤ 2 ^ n := by
  have h : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Nat.cast_one] at h
  linarith

/--
No derivative is lost in the fixed-order transport commutator: after removing
the top term, one derivative falls on `b`, leaving a total of at most five.
-/
theorem transport_commutator_L2 (d n : ℕ) (hd : (d : ℝ) < 2 * 3) (hn : n ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (b h : 𝓢(Domain d, ℂ)) :
    ‖(commutator d n v b h).toLp 2‖ ≤
      2 ^ n * (embeddingConstant d 3 hd * (2 * Real.pi) ^ (n-1) *
        sobolevNorm d 5 (directional d 1 v b) * sobolevNorm d 5 h) := by
  rw [commutator_expansion]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      product d (directional d j v (directional d 1 v b)) (directional d (n-(j+1)) v h))‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume ((n.choose (j+1) : ℂ) •
          product d (directional d j v (directional d 1 v b))
            (directional d (n-(j+1)) v h))‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
        ‖(product d (directional d j v (directional d 1 v b))
          (directional d (n-(j+1)) v h)).toLp 2‖ := by
      simp only [map_smul, norm_smul, Complex.norm_natCast, SchwartzMap.toLpCLM_apply]
    _ ≤ ∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
        (embeddingConstant d 3 hd * (2 * Real.pi) ^ (n-1) *
          sobolevNorm d 5 (directional d 1 v b) * sobolevNorm d 5 h) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.1 hj
      have he : j + (n-(j+1)) = n-1 := by omega
      have hbound := product_directional_L2_H5 d j (n-(j+1)) hd (by omega) v hv
        (directional d 1 v b) h
      rw [he] at hbound
      exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right (sum_choose_successors_le n)
      unfold embeddingConstant sobolevNorm
      positivity

end EulerSobolevTransport

end

section

/-! The Fourier H³ norm is controlled by genuine third directional derivatives in L². -/

namespace EulerSobolevDerivativeNorm

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv


theorem norm_le_sum_coordinates (d : ℕ) (ξ : Domain d) : ‖ξ‖ ≤ ∑ i, ‖ξ i‖ := by
  have he : (∑ i : Fin d, EuclideanSpace.single i (ξ i)) = ξ := by
    ext j
    simp
  calc
    ‖ξ‖ = ‖∑ i : Fin d, EuclideanSpace.single i (ξ i)‖ := by rw [he]
    _ ≤ ∑ i : Fin d, ‖EuclideanSpace.single i (ξ i)‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The operator norm of a derivative tensor is bounded by the sum of its coordinate entries. -/
theorem multilinear_norm_le_coordinate_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d n : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain d) F) :
    ‖T‖ ≤ ∑ w : Fin n → Fin d,
      ‖T (fun j => EuclideanSpace.single (w j) 1)‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  have hm (j : Fin n) : (∑ i : Fin d, (m j i) • EuclideanSpace.single i (1 : ℝ)) = m j := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hexpand : T m = ∑ w : Fin n → Fin d,
      T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ)) := by
    change T.toMultilinearMap m = ∑ w : Fin n → Fin d,
      T.toMultilinearMap (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))
    have h := T.toMultilinearMap.map_sum
      (fun (j : Fin n) (i : Fin d) => (m j i) • EuclideanSpace.single i (1 : ℝ))
    simpa only [hm] using h
  rw [hexpand]
  calc
    _ ≤ ∑ w : Fin n → Fin d,
        ‖T (fun j => (m j (w j)) • EuclideanSpace.single (w j) (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ w : Fin n → Fin d, (∏ j, ‖m j (w j)‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [T.map_smul_univ, norm_smul, norm_prod]
    _ ≤ ∑ w : Fin n → Fin d, (∏ j, ‖m j‖) *
        ‖T (fun j => EuclideanSpace.single (w j) (1 : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => PiLp.norm_apply_le (m j) (w j))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem besselWeight_one_le_coordinate_sum (d : ℕ) (ξ : Domain d) :
    besselWeight d 1 ξ ≤ 1 + ∑ i, ‖ξ i‖ := by
  have h : besselWeight d 1 ξ ≤ 1 + ‖ξ‖ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [norm_nonneg ξ]
  exact h.trans (by linarith [norm_le_sum_coordinates d ξ])

theorem besselWeight_three_le_pure_three (d : ℕ) (ξ : Domain d) :
    besselWeight d 3 ξ ≤ ((d : ℝ) + 1) ^ 2 * (1 + ∑ i, ‖ξ i‖ ^ 3) := by
  let a : Option (Fin d) → ℝ := fun i => match i with
    | none => 1
    | some i => ‖ξ i‖
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ a i := by
    intro i _
    cases i <;> simp only [a] <;> positivity
  have h := pow_sum_le_card_mul_sum_pow ha 2
  have he : besselWeight d 3 ξ = (besselWeight d 1 ξ) ^ 3 := by
    unfold besselWeight
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    norm_num
  rw [he]
  apply (pow_le_pow_left₀ (besselWeight_pos d 1 ξ).le
    (besselWeight_one_le_coordinate_sum d ξ) 3).trans
  simpa [a, Fintype.sum_option] using h

theorem sobolevNorm_three_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 3 f ≤ ((d : ℝ) + 1) ^ 2 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin d, ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, ℂ) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-3 : ℤ) : ℝ) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 3 f ξ‖ ≤ ((d : ℝ) + 1) ^ 2 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 3 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 3) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
        fourier_directional_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-3 : ℤ) * (2 * Real.pi) ^ (3 : ℕ) = 1 := by
        rw [show (-3 : ℤ) = -(3 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (besselWeight_three_le_pure_three d ξ) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 3 f) g (((d : ℝ) + 1) ^ 2)
    (sq_nonneg _) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-3 : ℤ) * ∑ i : Fin d,
        ‖(directional d 3 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (((2 * Real.pi) ^ (-3 : ℤ)) •
        𝓕 (directional d 3 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-3 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- Four-dimensional Sobolev embedding stated solely with actual L² derivative norms. -/
theorem pointwise_le_L2_third_derivatives (f : 𝓢(Domain 4, ℂ)) (x : Domain 4) :
    ‖f x‖ ≤ embeddingConstant 4 3 (by norm_num) * 25 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-3 : ℤ) *
        ∑ i : Fin 4, ‖(directional 4 3 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 4 3 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_three_le_pure_derivatives 4 f)
    (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _)
  refine hA.trans (hB.trans_eq ?_)
  norm_num
  ring

end EulerSobolevDerivativeNorm

end

section

/-! Measure-preserving Euclidean coordinates and the actual L² bridge to the cylinder. -/

namespace EulerCylinderCoordinates

open MeasureTheory EulerSobolev EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal NNReal Topology SchwartzMap


/-- Euclidean coordinate zero is the angle; coordinates one through three are spatial. -/
noncomputable def coordinateLinearEquiv : Domain 4 ≃ₗ[ℝ] LiftTangent where
  toFun z := (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0)
  invFun p := WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i))
  left_inv z := by
    ext i
    cases i using Fin.cases <;> simp
  right_inv p := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_add' z w := by
    apply Prod.ext
    · ext i
      simp
    · simp
  map_smul' c z := by
    apply Prod.ext
    · ext i
      simp
    · simp

/-- The coordinate isomorphism, continuous in both directions. -/
noncomputable def coordinateEquiv : Domain 4 ≃L[ℝ] LiftTangent :=
  coordinateLinearEquiv.toContinuousLinearEquiv

@[simp] theorem coordinateEquiv_apply (z : Domain 4) :
    coordinateEquiv z = (WithLp.toLp 2 (fun i : Fin 3 => z i.succ), z 0) := rfl

@[simp] theorem coordinateEquiv_symm_apply (p : LiftTangent) :
    coordinateEquiv.symm p = WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i)) := rfl

/-- The coordinate change preserves the genuine product Lebesgue measure exactly. -/
theorem coordinateEquiv_measurePreserving :
    MeasurePreserving coordinateEquiv (volume : Measure (Domain 4))
      ((volume : Measure Vector3).prod (volume : Measure ℝ)) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin 4)
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have h₃ : MeasurePreserving (Prod.swap : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ) :=
    Measure.measurePreserving_swap
  have h₄ := (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id (μ := volume (α := ℝ)))
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert! h using 1

variable (period : ℝ) [Fact (0 < period)]

/-- A fundamental strip in the real covering space. -/
noncomputable def fundamentalMeasure (a : ℝ) : Measure LiftTangent :=
  (volume : Measure Vector3).prod (volume.restrict (Set.Ioc a (a + period)))

/-- Covering coordinates restricted to one period preserve the cylinder's measure. -/
theorem covering_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (coveringMap period) (fundamentalMeasure period a) (liftMeasure period) :=
  (MeasurePreserving.id (μ := (volume : Measure Vector3))).prod (AddCircle.measurePreserving_mk period a)

/-- Euclidean coordinates for the actual quotient covering map. -/
noncomputable def euclideanCover : Domain 4 → LiftDomain period :=
  coveringMap period ∘ coordinateEquiv

/-- Euclidean measure restricted to one fundamental angular strip. -/
noncomputable def stripMeasure (a : ℝ) : Measure (Domain 4) :=
  volume.restrict {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)}

omit [Fact (0 < period)] in
theorem coordinateEquiv_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving coordinateEquiv (stripMeasure period a) (fundamentalMeasure period a) := by
  have hm : MeasurableSet ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have h := coordinateEquiv_measurePreserving.restrict_preimage hm
  have he : coordinateEquiv ⁻¹' ((Set.univ : Set Vector3) ×ˢ Set.Ioc a (a + period)) =
      {z : Domain 4 | z 0 ∈ Set.Ioc a (a + period)} := by
    ext z
    simp
  rw [he] at h
  simpa only [stripMeasure, fundamentalMeasure, ← Measure.prod_restrict,
    Measure.restrict_univ] using h

theorem euclideanCover_fundamental_measurePreserving (a : ℝ) :
    MeasurePreserving (euclideanCover period) (stripMeasure period a) (liftMeasure period) :=
  (covering_fundamental_measurePreserving period a).comp
    (coordinateEquiv_fundamental_measurePreserving period a)

/-- The fundamental-strip Lᵖ seminorm is exactly the Lᵖ seminorm on the cylinder. -/
theorem eLpNorm_cover {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period))
    (a : ℝ) (p : ℝ≥0∞) :
    eLpNorm (f ∘ euclideanCover period) p (stripMeasure period a) =
      eLpNorm f p (liftMeasure period) :=
  eLpNorm_comp_measurePreserving hf (euclideanCover_fundamental_measurePreserving period a)

/-- Square integrability of actual fields transfers to their Euclidean periodic lifts. -/
theorem memLp_cover {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) (a : ℝ) :
    MemLp (f ∘ euclideanCover period) 2 (stripMeasure period a) :=
  hf.comp_measurePreserving (euclideanCover_fundamental_measurePreserving period a)


/-- Six consecutive fundamental strips, retaining the actual Euclidean measures. -/
noncomputable def chartMeasure : Measure (Domain 4) :=
  Measure.sum (fun i : Fin 6 => stripMeasure period (((i : ℝ) - 3) * period))

theorem chartSupport_cover : ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) ⊆
    ⋃ i : Fin 6, {z : Domain 4 | z 0 ∈
      Set.Ioc (((i : ℝ)-3)*period) ((((i : ℝ)-3)*period)+period)} := by
  intro z hz
  have hT : 0 < period := Fact.out
  have hz' := abs_le.1 (show |z 0| ≤ 2 * period from hz)
  by_cases h₀ : z 0 ≤ -2 * period
  · apply Set.mem_iUnion.2 ⟨0, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₁ : z 0 ≤ -period
  · apply Set.mem_iUnion.2 ⟨1, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₂ : z 0 ≤ 0
  · apply Set.mem_iUnion.2 ⟨2, ?_⟩
    norm_num
    constructor <;> linarith
  by_cases h₃ : z 0 ≤ period
  · apply Set.mem_iUnion.2 ⟨3, ?_⟩
    norm_num
    constructor <;> linarith
  · apply Set.mem_iUnion.2 ⟨4, ?_⟩
    norm_num
    constructor <;> linarith

theorem chartSupport_measure_le :
    volume.restrict (({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period})) ≤ chartMeasure period :=
  (Measure.restrict_mono_set volume (chartSupport_cover period)).trans Measure.restrict_iUnion_le

/-- The finite chart cover has exactly six times the cylinder measure. -/
theorem euclideanCover_chart_measurePreserving :
    MeasurePreserving (euclideanCover period) (chartMeasure period)
      ((6 : ℝ≥0∞) • liftMeasure period) := by
  have hm := (euclideanCover_fundamental_measurePreserving period 0).measurable
  refine ⟨hm, ?_⟩
  rw [chartMeasure, Measure.sum_fintype, Measure.map_finset_sum' hm.aemeasurable]
  simp only [(euclideanCover_fundamental_measurePreserving period _).map_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ≥0∞ 6 (liftMeasure period)).symm

theorem eLpNorm_cover_chart {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period)) :
    eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) =
      (6 : ℝ≥0∞) ^ (1/2 : ℝ) * eLpNorm f 2 (liftMeasure period) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _)
    (euclideanCover_chart_measurePreserving period)]
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
  norm_num

/-- A localized lift is controlled by the genuine cylinder norm, with explicit chart multiplicity. -/
theorem eLpNorm_localized_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : LiftDomain period → F) (hf : AEStronglyMeasurable f (liftMeasure period))
    (g : Domain 4 → G) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    eLpNorm g 2 volume ≤ (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  calc
    _ ≤ eLpNorm g 2 (chartMeasure period) := eLpNorm_mono_measure g (chartSupport_measure_le period)
    _ ≤ (B : ℝ≥0∞) * eLpNorm (f ∘ euclideanCover period) 2 (chartMeasure period) :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall hb) 2
    _ = _ := by rw [eLpNorm_cover_chart period f hf, mul_assoc]

/-- The localized-lift estimate as an inequality between ordinary real L² norms. -/
theorem localized_L2_le {F : Type*} [NormedAddCommGroup F]
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period))
    (g : 𝓢(Domain 4, ℂ)) (hsupp : Function.support g ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}))
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖ ≤ B * ‖f (euclideanCover period z)‖) :
    ‖g.toLp 2‖ ≤ (B : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * ‖hf.toLp f‖ := by
  have h := eLpNorm_localized_le period f hf.1 g hsupp B hb
  have hfin : (B : ℝ≥0∞) * (6 : ℝ≥0∞) ^ (1/2 : ℝ) *
      eLpNorm f 2 (liftMeasure period) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfin h
  simpa only [SchwartzMap.norm_toLp, Lp.norm_toLp, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] using hreal

end EulerCylinderCoordinates

end

section

/-! Actual derivative-word Sobolev norms on R³ × T and compact localizations. -/

namespace EulerCylinderSobolev

open MeasureTheory EulerSobolev EulerSobolevProducts EulerSobolevDerivativeNorm
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open EulerCylinderCoordinates
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv


/-- The four coordinate directions, with angle first and the spatial coordinates following. -/
noncomputable def standardDirection (i : Fin 4) : LiftTangent :=
  coordinateEquiv (EuclideanSpace.single i 1)

@[simp] theorem standardDirection_zero : standardDirection 0 = (0,1) := by
  apply Prod.ext
  · ext i
    simp [standardDirection]
  · simp [standardDirection]

@[simp] theorem standardDirection_succ (i : Fin 3) :
    standardDirection i.succ = (EuclideanSpace.single i 1, 0) := by
  apply Prod.ext
  · ext j
    simp [standardDirection]
  · simp [standardDirection]

variable (period : ℝ)

section Fields

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordered actual derivatives on the cylinder; the head is differentiated last. -/
noncomputable def iteratedFieldDerivative : {n : ℕ} → (Fin n → Fin 4) →
    (LiftDomain period → F) → LiftDomain period → F
  | 0, _, f => f
  | _n+1, w, f => fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative (Fin.tail w) f)

@[simp] theorem iteratedFieldDerivative_zero (w : Fin 0 → Fin 4) (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = f := rfl

@[simp] theorem iteratedFieldDerivative_succ {n : ℕ} (w : Fin (n+1) → Fin 4)
    (f : LiftDomain period → F) :
    iteratedFieldDerivative period w f = fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) := rfl

/-- A concrete norm: the sum of L² norms of all ordered coordinate derivatives up to order `s`. -/
noncomputable def liftSobolevNorm (s : ℕ) (f : LiftDomain period → F)
    [Fact (0 < period)] : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => ∑ w : Fin n → Fin 4,
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal)

theorem iteratedFieldDerivative_smooth {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (iteratedFieldDerivative period w f) x) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact fieldDerivative_smooth period _ _ (ih (Fin.tail w))

/-- The actual field lifted to Euclidean coordinates centered at a cylinder point. -/
noncomputable def euclideanLift (f : LiftDomain period → F) (x : LiftDomain period) : Domain 4 → F :=
  localFieldLift period f x ∘ coordinateEquiv

theorem euclideanLift_smooth (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (euclideanLift period f x) := (hf x).comp coordinateEquiv.contDiff

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_zero (f : LiftDomain period → F) (x : LiftDomain period) :
    euclideanLift period f x 0 = f x := by
  change localFieldLift period f x (coordinateEquiv 0) = _
  rw [map_zero]
  simp [localFieldLift]

theorem euclideanLift_fieldDerivative (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (v z : Domain 4)
    (x : LiftDomain period) :
    euclideanLift period (fieldDerivative period (coordinateEquiv v) f) x z =
      fderiv ℝ (euclideanLift period f x) z v := by
  have hchain := ((hf x).differentiable (by simp) (coordinateEquiv z)).hasFDerivAt.comp z
    coordinateEquiv.hasFDerivAt
  rw [euclideanLift, localFieldLift_fieldDerivative]
  change fderiv ℝ (localFieldLift period f x) (coordinateEquiv z) (coordinateEquiv v) = _
  rw [show fderiv ℝ (euclideanLift period f x) z =
      (fderiv ℝ (localFieldLift period f x) (coordinateEquiv z)).comp
        coordinateEquiv.toContinuousLinearMap from hchain.fderiv]
  rfl

/-- The word derivative is exactly the corresponding coordinate entry of the Fréchet tensor. -/
theorem euclideanLift_iteratedFieldDerivative {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period (iteratedFieldDerivative period w f) x z =
      iteratedFDeriv ℝ n (euclideanLift period f x) z
        (fun j => EuclideanSpace.single (w j) 1) := by
  induction n generalizing z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, standardDirection,
      euclideanLift_fieldDerivative _ _ (iteratedFieldDerivative_smooth period (Fin.tail w) f hf),
      iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply]
    · congr 2
      funext y
      exact ih (Fin.tail w) y
    · exact (euclideanLift_smooth period f hf x).differentiable_iteratedFDeriv
        (show (n : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top n) z

/-- Tensor operator norms are controlled by the actual coordinate-word derivatives. -/
theorem euclideanLift_tensor_norm_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) z‖ ≤
      ∑ w : Fin n → Fin 4, ‖euclideanLift period (iteratedFieldDerivative period w f) x z‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 n (iteratedFDeriv ℝ n (euclideanLift period f x) z)
  simpa only [euclideanLift_iteratedFieldDerivative period _ f hf] using h

/-- Sum of the norms of all coordinate words of one fixed order. -/
noncomputable def wordMagnitude (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  ∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative period w f x‖

theorem wordMagnitude_nonneg (n : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ wordMagnitude period n f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The sum of all coordinate derivative magnitudes through a given order. -/
noncomputable def totalMagnitude (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun n => wordMagnitude period n f x)

theorem totalMagnitude_nonneg (s : ℕ) (f : LiftDomain period → F) (x : LiftDomain period) :
    0 ≤ totalMagnitude period s f x :=
  Finset.sum_nonneg (fun n _ => wordMagnitude_nonneg period n f x)

theorem wordMagnitude_le_total (s n : ℕ) (hn : n ≤ s) (f : LiftDomain period → F)
    (x : LiftDomain period) : wordMagnitude period n f x ≤ totalMagnitude period s f x :=
  Finset.single_le_sum (fun j _ => wordMagnitude_nonneg period j f x)
    (Finset.mem_range.2 (by omega))

end Fields

section Translations

variable [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F]

/-- Translation of an actual cylinder function. -/
noncomputable def translated (f : LiftDomain period → F) (x : LiftDomain period) :
    LiftDomain period → F := fun y => f (y + x)

theorem eLpNorm_translated (f : LiftDomain period → F)
    (hf : AEStronglyMeasurable f (liftMeasure period)) (x : LiftDomain period) :
    eLpNorm (translated period f x) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_translation period x)

theorem memLp_translated (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) (x : LiftDomain period) :
    MemLp (translated period f x) 2 (liftMeasure period) :=
  hf.comp_measurePreserving (measurePreserving_translation period x)

variable [NormedSpace ℝ F]

omit [Fact (0 < period)] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem euclideanLift_eq_translated_cover (f : LiftDomain period → F)
    (x : LiftDomain period) (z : Domain 4) :
    euclideanLift period f x z = translated period f x (euclideanCover period z) := by
  change f (x.1 + (coordinateEquiv z).1, x.2 + ((coordinateEquiv z).2 : AddCircle period)) =
    f ((coveringMap period (coordinateEquiv z)) + x)
  congr 1
  ext <;> simp [coveringMap, add_comm]

theorem wordMagnitude_memLp (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (wordMagnitude period n f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun w _ => (hf w).norm)

theorem eLpNorm_wordMagnitude_le (n : ℕ) (f : LiftDomain period → F)
    (hf : ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) ≤
      ∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
  have he : wordMagnitude period n f = ∑ w : Fin n → Fin 4,
      (fun x => ‖iteratedFieldDerivative period w f x‖) := by
    funext x
    simp [wordMagnitude]
  rw [he]
  simpa only [eLpNorm_norm] using eLpNorm_sum_le
    (fun w (_ : w ∈ (Finset.univ : Finset (Fin n → Fin 4))) => (hf w).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem totalMagnitude_memLp (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    MemLp (totalMagnitude period s f) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun n hn => wordMagnitude_memLp period n f (hf n (by simpa using Finset.mem_range.1 hn)))

theorem totalMagnitude_L2_le (s : ℕ) (f : LiftDomain period → F)
    (hf : ∀ n ≤ s, ∀ w : Fin n → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    ‖(totalMagnitude_memLp period s f hf).toLp (totalMagnitude period s f)‖ ≤
      liftSobolevNorm period s f := by
  have he : totalMagnitude period s f = ∑ n ∈ Finset.range (s+1), wordMagnitude period n f := by
    funext x
    simp [totalMagnitude]
  have hA : eLpNorm (totalMagnitude period s f) 2 (liftMeasure period) ≤
      ∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period) := by
    rw [he]
    exact eLpNorm_sum_le (fun n hn =>
      (wordMagnitude_memLp period n f (hf n (by simpa using Finset.mem_range.1 hn))).1) (by norm_num)
  have hB : (∑ n ∈ Finset.range (s+1), eLpNorm (wordMagnitude period n f) 2 (liftMeasure period)) ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4,
        eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period) := by
    exact Finset.sum_le_sum (fun n hn => eLpNorm_wordMagnitude_le period n f
      (hf n (by simpa using Finset.mem_range.1 hn)))
  have hfin (n : ℕ) (hn : n ∈ Finset.range (s+1)) :
      (∑ w : Fin n → Fin 4, eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun w _ => (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)
  have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) (hA.trans hB)
  rw [Lp.norm_toLp]
  convert hreal using 1
  rw [ENNReal.toReal_sum hfin]
  apply Finset.sum_congr rfl
  intro n hn
  exact (ENNReal.toReal_sum (fun w _ =>
    (hf n (by simpa using Finset.mem_range.1 hn) w).eLpNorm_ne_top)).symm

end Translations

variable [Fact (0 < period)]

/-- A fixed compact smooth localizer, supported in the chart neighborhood and equal to one at zero. -/
noncomputable def localBump : ContDiffBump (0 : Domain 4) where
  rIn := period
  rOut := 2 * period
  rIn_pos := Fact.out
  rIn_lt_rOut := by have h : 0 < period := Fact.out; linarith

theorem localBump_smooth : ContDiff ℝ ∞ (localBump period) := (localBump period).contDiff

theorem localBump_zero : localBump period 0 = 1 :=
  (localBump period).one_of_mem_closedBall
    (by simpa [localBump] using (show 0 ≤ period from (Fact.out : 0 < period).le))

theorem localBump_support : tsupport (localBump period) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) := by
  rw [(localBump period).tsupport_eq]
  intro z hz
  have hnorm : ‖z‖ ≤ 2 * period := by simpa [localBump] using hz
  exact (PiLp.norm_apply_le z 0).trans hnorm

/-- The local bump regarded as a real Schwartz function. -/
noncomputable def bumpSchwartz : 𝓢(Domain 4, ℝ) :=
  (localBump period).hasCompactSupport.toSchwartzMap (localBump_smooth period)

/-- A finite, explicitly defined bound for each derivative of the fixed local bump. -/
noncomputable def bumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j (bumpSchwartz period), apply_nonneg _ _⟩

theorem localBump_derivative_bound (j : ℕ) (z : Domain 4) :
    ‖iteratedFDeriv ℝ j (localBump period) z‖ ≤ bumpBound period j :=
  SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (bumpSchwartz period) j z

/-- Finite Leibniz coefficient controlling localization at derivative order `n`. -/
noncomputable def bumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * bumpBound period j)

/-- An actual compactly supported localization of an arbitrary smooth cylinder field. -/
noncomputable def localized (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) : 𝓢(Domain 4, ℂ) :=
  ((localBump period).hasCompactSupport.smul_right (f' := euclideanLift period f x)).toSchwartzMap
    ((localBump_smooth period).smul (euclideanLift_smooth period f hf x))

@[simp] theorem localized_apply (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    localized period f hf x z = localBump period z • euclideanLift period f x z := rfl

theorem localized_zero (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    localized period f hf x 0 = f x := by
  rw [localized_apply, localBump_zero, one_smul, euclideanLift_zero]

theorem localized_tsupport (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    tsupport (localized period f hf x) ⊆ ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) :=
  (tsupport_smul_subset_left (localBump period) (euclideanLift period f x)).trans
    (localBump_support period)

/-- The actual Leibniz rule controls every localized derivative by cylinder derivative words. -/
theorem localized_tensor_norm_le (n : ℕ) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ n (localized period f hf x) z‖ ≤
      bumpCoefficient period n * translated period (totalMagnitude period n f) x
        (euclideanCover period z) := by
  have hA := norm_iteratedFDeriv_smul_le (localBump_smooth period)
    (euclideanLift_smooth period f hf x) z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  change (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
    ‖iteratedFDeriv ℝ j (localBump period) z‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖) ≤ _
  have hB (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period f x) z‖ ≤
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
    have hT := euclideanLift_tensor_norm_le period (n-j) f hf x z
    simp only [euclideanLift_eq_translated_cover, translated] at hT
    exact hT.trans (wordMagnitude_le_total period n (n-j) (by omega) f _)
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * bumpBound period j) *
        translated period (totalMagnitude period n f) x (euclideanCover period z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (localBump_derivative_bound period j z) (Nat.cast_nonneg _))
        (hB j hj) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (bumpBound period j).coe_nonneg)
    _ = _ := by simp only [bumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast,
      Finset.sum_mul]

/-- Each pure directional derivative of the localization has the same chart support. -/
theorem directional_localized_support (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    Function.support (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)) ⊆
      ({z : EulerSobolev.Domain 4 | |z 0| ≤ 2 * period}) := by
  have he : (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) :
      Domain 4 → ℂ) = (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Domain 4) ℂ =>
        T (fun _ => EuclideanSpace.single i 1)) ∘ iteratedFDeriv ℝ n (localized period f hf x) := by
    funext z
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
  rw [he]
  exact subset_closure.trans ((tsupport_comp_subset (by simp) _).trans
    ((tsupport_iteratedFDeriv_subset n).trans (localized_tsupport period f hf x)))

/-- Every localized pure derivative is controlled by the actual cylinder derivative L² sum. -/
theorem localized_directional_L2_le (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ n, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖(directional 4 n (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖ ≤
      (bumpCoefficient period n : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period n f := by
  let q := totalMagnitude period n f
  have hq : MemLp q 2 (liftMeasure period) := totalMagnitude_memLp period n f hfL2
  have hqt := memLp_translated period q hq x
  have hb (z : Domain 4) :
      ‖directional 4 n (EuclideanSpace.single i 1) (localized period f hf x) z‖ ≤
        (bumpCoefficient period n : ℝ) * ‖translated period q x (euclideanCover period z)‖ := by
    rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    have hA := (iteratedFDeriv ℝ n (localized period f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    have hB := localized_tensor_norm_le period n f hf x z
    change _ ≤ (bumpCoefficient period n : ℝ) * ‖totalMagnitude period n f (_ + x)‖
    rw [Real.norm_of_nonneg (totalMagnitude_nonneg period n f _)]
    exact hA.trans hB
  have hA := localized_L2_le period (translated period q x) hqt
    (directional 4 n (EuclideanSpace.single i 1) (localized period f hf x))
    (directional_localized_support period n i f hf x) (bumpCoefficient period n) hb
  have hnorm : ‖hqt.toLp (translated period q x)‖ = ‖hq.toLp q‖ := by
    simp only [Lp.norm_toLp, eLpNorm_translated period q hq.1]
  rw [hnorm] at hA
  exact hA.trans (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period n f hfL2)
    (mul_nonneg (bumpCoefficient period n).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))

theorem liftSobolevNorm_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : ℕ) (f : LiftDomain period → F) : 0 ≤ liftSobolevNorm period s f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))

theorem liftSobolevNorm_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s t : ℕ} (hst : s ≤ t) (f : LiftDomain period → F) :
    liftSobolevNorm period s f ≤ liftSobolevNorm period t f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro n _ _
  exact Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

/-- A concrete finite embedding constant depending only on the circle period. -/
noncomputable def cylinderEmbeddingConstant : ℝ :=
  embeddingConstant 4 3 (by norm_num) * 25 * (6 : ℝ) ^ (1/2 : ℝ) *
    ((bumpCoefficient period 0 : ℝ) + (2 * Real.pi) ^ (-3 : ℤ) * 4 * bumpCoefficient period 3)

theorem cylinderEmbeddingConstant_nonneg : 0 ≤ cylinderEmbeddingConstant period := by
  unfold cylinderEmbeddingConstant
  have hc : 0 ≤ embeddingConstant 4 3 (by norm_num) := norm_nonneg _
  positivity

/-- Genuine H³ to L∞ embedding on R³ × T for arbitrary smooth fields with square-integrable derivatives. -/
theorem cylinder_pointwise_le_H3 (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have hbase := localized_directional_L2_le period 0 0 f hf
    (fun j hj => hfL2 j (by omega)) x
  have he : directional 4 0 (EuclideanSpace.single 0 1) (localized period f hf x) =
      localized period f hf x := by ext z; simp [directional]
  rw [he] at hbase
  have hbase' := hbase.trans (mul_le_mul_of_nonneg_left
    (liftSobolevNorm_mono period (show 0 ≤ 3 by omega) f)
    (mul_nonneg (bumpCoefficient period 0).coe_nonneg (Real.rpow_nonneg (by norm_num) _)))
  have hthird : (∑ i : Fin 4,
      ‖(directional 4 3 (EuclideanSpace.single i 1) (localized period f hf x)).toLp 2‖) ≤
        4 * ((bumpCoefficient period 3 : ℝ) * (6 : ℝ) ^ (1/2 : ℝ) * liftSobolevNorm period 3 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      localized_directional_L2_le period 3 i f hf hfL2 x)
  have hA := pointwise_le_L2_third_derivatives (localized period f hf x) 0
  rw [localized_zero] at hA
  have hB := add_le_add hbase' (mul_le_mul_of_nonneg_left hthird
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (-3 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB
    (mul_nonneg (show 0 ≤ embeddingConstant 4 3 (by norm_num) from norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 25))
  refine hA.trans (hC.trans_eq ?_)
  unfold cylinderEmbeddingConstant
  ring

section WordComposition
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
/-- Composing two actual derivative words gives a word of the combined length. -/
theorem iteratedFieldDerivative_comp_exists {m n : ℕ} (v : Fin n → Fin 4)
    (w : Fin m → Fin 4) (f : LiftDomain period → F) :
    ∃ u : Fin (m+n) → Fin 4, iteratedFieldDerivative period v
      (iteratedFieldDerivative period w f) = iteratedFieldDerivative period u f := by
  induction n with
  | zero => exact ⟨w, rfl⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih (Fin.tail v)
    refine ⟨Fin.cons (v 0) u, ?_⟩
    simp only [iteratedFieldDerivative_succ, Fin.cons_zero, Fin.tail_cons, hu]

theorem word_L2_le_liftSobolevNorm {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      liftSobolevNorm period s f := by
  have hA : (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ v : Fin n → Fin 4, (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal :=
    Finset.single_le_sum (f := fun v : Fin n → Fin 4 =>
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ w)
  have hB : (∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal) ≤
        liftSobolevNorm period s f :=
    Finset.single_le_sum (s := Finset.range (s+1)) (a := n)
      (f := fun j => ∑ v : Fin j → Fin 4,
        (eLpNorm (iteratedFieldDerivative period v f) 2 (liftMeasure period)).toReal)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg))
      (Finset.mem_range.2 (by omega))
  exact hA.trans hB

theorem word_memLp {s m n : ℕ} (h : m+n ≤ s) (v : Fin n → Fin 4) (w : Fin m → Fin 4)
    (f : LiftDomain period → F)
    (hfL2 : ∀ j ≤ s, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
      (liftMeasure period) := by
  obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
  rw [hu]
  exact hfL2 (m+n) h u

theorem word_H3_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → F) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period 6 f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period 6 f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

end WordComposition

/-- Uniform control of any derivative word of order at most three by the H⁶ norm. -/
theorem cylinder_word_pointwise_le_H6 {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      cylinderEmbeddingConstant period * (85 * liftSobolevNorm period 6 f) := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (cylinderEmbeddingConstant_nonneg period))

end EulerCylinderSobolev

end

section

/-! Actual H⁶ multiplication on the three-dimensional cylinder. -/

namespace EulerCylinderAlgebra

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The low-order tensor bound furnished by the cylinder embedding. -/
noncomputable def lowDerivativeConstant : ℝ := 64 * 85 * cylinderEmbeddingConstant period

theorem lowDerivativeConstant_nonneg : 0 ≤ lowDerivativeConstant period :=
  mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)

theorem tensor_low_le_H6 {m : ℕ} (hm : m ≤ 3) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) 0‖ ≤
      lowDerivativeConstant period * liftSobolevNorm period 6 f := by
  have hA := euclideanLift_tensor_norm_le period m f hf x 0
  simp only [euclideanLift_zero] at hA
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin m → Fin 4))) =>
    cylinder_word_pointwise_le_H6 period hm w f hf hfL2 x)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ) ^ m ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hm
    norm_num at h ⊢
    exact h
  have hC := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (cylinderEmbeddingConstant_nonneg period) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (liftSobolevNorm_nonneg period 6 f)))
  have he (C A : ℝ) : 64 * (C * (85 * A)) = (64 * 85 * C) * A := by ring
  exact hA.trans (hB.trans (hC.trans_eq (he _ _)))

omit [Fact (0 < period)] in
theorem tensor_le_totalMagnitude {n : ℕ} (hn : n ≤ 6) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ n (euclideanLift period f x) 0‖ ≤ totalMagnitude period 6 f x := by
  have hA := euclideanLift_tensor_norm_le period n f hf x 0
  simp only [euclideanLift_zero] at hA
  exact hA.trans (wordMagnitude_le_total period 6 n hn f x)

/-- The real-valued envelope arising from the low/high derivative split. -/
noncomputable def productEnvelope (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period 6 f • totalMagnitude period 6 g +
    liftSobolevNorm period 6 g • totalMagnitude period 6 f

theorem productEnvelope_nonneg (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ productEnvelope period f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period 6 f) (totalMagnitude_nonneg period 6 g x))
    (mul_nonneg (liftSobolevNorm_nonneg period 6 g) (totalMagnitude_nonneg period 6 f x))

omit [Fact (0 < period)] in
theorem product_smooth (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (f*g) x) := fun x => (hf x).mul (hg x)

theorem product_tensor_term_le {n j : ℕ} (hn : n ≤ 6) (hj : j ≤ n)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖ ≤
        lowDerivativeConstant period * productEnvelope period f g x := by
  by_cases hj3 : j ≤ 3
  · have hA := mul_le_mul (tensor_low_le_H6 period hj3 f hf hfL2 x)
      (tensor_le_totalMagnitude period (by omega : n-j ≤ 6) g hg x) (norm_nonneg _)
      (mul_nonneg (lowDerivativeConstant_nonneg period) (liftSobolevNorm_nonneg period 6 f))
    have hB : liftSobolevNorm period 6 f * totalMagnitude period 6 g x ≤ productEnvelope period f g x := by
      exact le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 6 g)
        (totalMagnitude_nonneg period 6 f x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    rw [mul_assoc] at hA
    exact hA.trans hC
  · have hA := mul_le_mul (tensor_le_totalMagnitude period (by omega : j ≤ 6) f hf x)
      (tensor_low_le_H6 period (by omega : n-j ≤ 3) g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period 6 f x)
    have hB : liftSobolevNorm period 6 g * totalMagnitude period 6 f x ≤ productEnvelope period f g x := by
      exact le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 6 f)
        (totalMagnitude_nonneg period 6 g x))
    have hC := mul_le_mul_of_nonneg_left hB (lowDerivativeConstant_nonneg period)
    have he (A B C : ℝ) : A * (B*C) = B*(C*A) := by ring
    exact hA.trans ((he _ _ _).trans_le hC)

/-- Actual Leibniz derivatives of a product have a square-integrable low/high envelope. -/
theorem product_word_pointwise_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      64 * lowDerivativeConstant period * productEnvelope period f g x := by
  have he := euclideanLift_iteratedFieldDerivative period w (f*g) (product_smooth period f g hf hg) x 0
  rw [euclideanLift_zero] at he
  rw [he]
  have hA := (iteratedFDeriv ℝ n (euclideanLift period (f*g) x) 0).le_opNorm
    (fun j => EuclideanSpace.single (w j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period g hg x) 0 (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (n-j) (euclideanLift period g x) 0‖) ≤
        2^n * (lowDerivativeConstant period * productEnvelope period f g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
          (lowDerivativeConstant period * productEnvelope period f g x) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (product_tensor_term_le period hn
          (by simpa using Finset.mem_range.1 hj) f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hp : (2 : ℝ)^n ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (lowDerivativeConstant_nonneg period) (productEnvelope_nonneg period f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))

theorem productEnvelope_memLp (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (productEnvelope period f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 6 g hgL2).const_smul (liftSobolevNorm period 6 f)).add
    ((totalMagnitude_memLp period 6 f hfL2).const_smul (liftSobolevNorm period 6 g))

theorem productEnvelope_L2_le (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    ‖(productEnvelope_memLp period f g hfL2 hgL2).toLp (productEnvelope period f g)‖ ≤
      2 * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  change ‖liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp _ +
    liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period 6 f • (totalMagnitude_memLp period 6 g hgL2).toLp (totalMagnitude period 6 g))
    (liftSobolevNorm period 6 g • (totalMagnitude_memLp period 6 f hfL2).toLp (totalMagnitude period 6 f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 6 g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 g hgL2) (liftSobolevNorm_nonneg period 6 f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 6 f hfL2) (liftSobolevNorm_nonneg period 6 g))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

/-- Every derivative word through order six of the product is genuinely square-integrable. -/
theorem product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  apply (productEnvelope_memLp period f g hfL2 hgL2).of_le_mul
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (product_smooth period f g hf hg))).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
  exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x

/-- An explicit bound for each actual product derivative in L². -/
theorem product_word_L2_le {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period)).toReal ≤
      128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hq := productEnvelope_memLp period f g hfL2 hgL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖iteratedFieldDerivative period w (f*g) x‖ ≤
      (64 * lowDerivativeConstant period) * ‖productEnvelope period f g x‖ by
        rw [Real.norm_of_nonneg (productEnvelope_nonneg period f g x)]
        exact product_word_pointwise_le period hn w f g hf hg hfL2 hgL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 64 * lowDerivativeConstant period := mul_nonneg (by norm_num) (lowDerivativeConstant_nonneg period)
  have hfin : ENNReal.ofReal (64 * lowDerivativeConstant period) *
      eLpNorm (productEnvelope period f g) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (productEnvelope_L2_le period f g hfL2 hgL2) hc
  rw [Lp.norm_toLp] at hC
  have he (L A B : ℝ) : (64*L)*(2*A*B) = 128*L*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

/-- The H⁶ algebra estimate on the actual cylinder, with a finite explicit constant. -/
theorem cylinder_H6_algebra (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 6, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤
      (5461 * 128 * lowDerivativeConstant period) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hA : liftSobolevNorm period 6 (f*g) ≤
      ∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4,
        128 * lowDerivativeConstant period * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact product_word_L2_le period (by have := Finset.mem_range.1 hn; omega) w f g hf hg hfL2 hgL2
  have hcard (A : ℝ) : (∑ n ∈ Finset.range 7, ∑ _w : Fin n → Fin 4, A) = 5461*A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Finset.sum_range_succ]
    ring
  rw [hcard] at hA
  have he (L A B : ℝ) : 5461*(128*L*A*B) = (5461*128*L)*A*B := by ring
  exact hA.trans_eq (he _ _ _)

end EulerCylinderAlgebra

end

section

/-! Real-valued forms of the cylinder Sobolev and multiplication estimates. -/

namespace EulerRealCylinder

open MeasureTheory EulerCylinderSobolev EulerCylinderAlgebra
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ)

section LinearMaps
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fieldDerivative_postcomp (L : F →L[ℝ] G) (a : LiftTangent)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    fieldDerivative period a (L ∘ f) = L ∘ fieldDerivative period a f := by
  funext x
  have h := L.hasFDerivAt.comp 0 (((hf x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] G => A a) h.fderiv

theorem iteratedFieldDerivative_postcomp {n : ℕ} (L : F →L[ℝ] G) (w : Fin n → Fin 4)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (L ∘ f) = L ∘ iteratedFieldDerivative period w f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w), fieldDerivative_postcomp period L _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)]
    rfl

end LinearMaps

/-- Isometric complexification of a real scalar cylinder field. -/
noncomputable def complexField (f : LiftDomain period → ℝ) : LiftDomain period → ℂ :=
  Complex.ofRealCLM ∘ f

theorem complexField_smooth (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (complexField period f) x) :=
  fun x => Complex.ofRealCLM.contDiff.comp (hf x)

theorem complexField_word {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    iteratedFieldDerivative period w (complexField period f) =
      complexField period (iteratedFieldDerivative period w f) :=
  iteratedFieldDerivative_postcomp period Complex.ofRealCLM w f hf

variable [Fact (0 < period)]

theorem complexField_eLpNorm (f : LiftDomain period → ℝ) :
    eLpNorm (complexField period f) 2 (liftMeasure period) = eLpNorm f 2 (liftMeasure period) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards [] with x
  exact Complex.norm_real _

theorem complexField_memLp (f : LiftDomain period → ℝ) (hf : MemLp f 2 (liftMeasure period)) :
    MemLp (complexField period f) 2 (liftMeasure period) :=
  Complex.ofRealCLM.comp_memLp' hf

theorem complexField_sobolevNorm (s : ℕ) (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    liftSobolevNorm period s (complexField period f) = liftSobolevNorm period s f := by
  unfold liftSobolevNorm
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro w _
  rw [complexField_word period w f hf, complexField_eLpNorm]

/-- The actual real H³ to L∞ embedding on the cylinder. -/
theorem real_cylinder_pointwise_le_H3 (f : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
  have h := cylinder_pointwise_le_H3 period (complexField period f) (complexField_smooth period f hf)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w)) x
  rw [complexField_sobolevNorm period 3 f hf] at h
  simpa only [complexField, Function.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real] using h

/-- The real H⁶ algebra estimate on the actual cylinder. -/
theorem real_cylinder_H6_algebra (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (f*g) ≤ (5461 * 128 * lowDerivativeConstant period) *
      liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have h := cylinder_H6_algebra period (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj w => by rw [complexField_word period w f hf]; exact complexField_memLp period _ (hfL2 j hj w))
    (fun j hj w => by rw [complexField_word period w g hg]; exact complexField_memLp period _ (hgL2 j hj w))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_sobolevNorm period 6 (f*g) (fun x => (hf x).mul (hg x)),
    complexField_sobolevNorm period 6 f hf, complexField_sobolevNorm period 6 g hg] at h
  exact h

end EulerRealCylinder

end

section

/-! Real Euclidean vector wrappers for the actual cylinder Sobolev estimates. -/

namespace EulerVectorCylinder

open MeasureTheory EulerSobolev EulerSobolevDerivativeNorm EulerRealCylinder
open EulerCylinderSobolev EulerCylinderAlgebra EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

section Postcomposition
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [Fact (0 < period)] in
theorem postcomp_smooth (L : F →L[ℝ] G) (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (L ∘ f) x) := fun x => L.contDiff.comp (hf x)

theorem postcomp_word_memLp {s n : ℕ} (hn : n ≤ s) (L : F →L[ℝ] G)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (w : Fin n → Fin 4) :
    MemLp (iteratedFieldDerivative period w (L ∘ f)) 2 (liftMeasure period) := by
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  exact L.comp_memLp' (hfL2 n hn w)

theorem postcomp_sobolevNorm_le (s : ℕ) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    (f : LiftDomain period → F) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ s, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) :
    liftSobolevNorm period s (L ∘ f) ≤ liftSobolevNorm period s f := by
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro w _
  rw [iteratedFieldDerivative_postcomp period L w f hf]
  apply ENNReal.toReal_mono (hfL2 n (by have := Finset.mem_range.1 hn; omega) w).eLpNorm_ne_top
  apply eLpNorm_mono
  intro x
  have h := L.le_opNorm (iteratedFieldDerivative period w f x)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

end Postcomposition

/-- A coordinate projection on a real Euclidean target, of operator norm at most one. -/
noncomputable def coordinate (q : ℕ) (i : Fin q) : Domain q →L[ℝ] ℝ := EuclideanSpace.proj i

theorem coordinate_norm_le (q : ℕ) (i : Fin q) : ‖coordinate q i‖ ≤ 1 := by
  apply (coordinate q i).opNorm_le_bound (by norm_num)
  intro x
  change ‖x i‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using PiLp.norm_apply_le x i

/-- H³ controls the pointwise norm of a genuine real Euclidean cylinder field. -/
theorem vector_cylinder_pointwise_le_H3 (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 3, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖f x‖ ≤ ((q : ℝ) * cylinderEmbeddingConstant period) * liftSobolevNorm period 3 f := by
  have hA := norm_le_sum_coordinates q (f x)
  have hB (i : Fin q) : ‖f x i‖ ≤ cylinderEmbeddingConstant period * liftSobolevNorm period 3 f := by
    have h := real_cylinder_pointwise_le_H3 period (coordinate q i ∘ f)
      (postcomp_smooth period _ f hf) (fun j hj w => postcomp_word_memLp period hj _ f hf hfL2 w) x
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 3 _ (coordinate_norm_le q i) f hf hfL2)
      (cylinderEmbeddingConstant_nonneg period))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  exact hA.trans (hC.trans_eq (mul_assoc _ _ _).symm)

omit [Fact (0 < period)] in
/-- The coordinate of a classical derivative is the derivative of the coordinate. -/
theorem coordinate_word {n : ℕ} (q : ℕ) (i : Fin q) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    iteratedFieldDerivative period w (coordinate q i ∘ f) x = iteratedFieldDerivative period w f x i := by
  rw [iteratedFieldDerivative_postcomp period _ w f hf]
  rfl

theorem vector_eLpNorm_le_sum_coordinates (q : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ i : Fin q, MemLp (fun x => f x i) 2 (liftMeasure period)) :
    eLpNorm f 2 (liftMeasure period) ≤ ∑ i : Fin q, eLpNorm (fun x => f x i) 2 (liftMeasure period) := by
  have hA : eLpNorm f 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin q, ‖f x i‖) 2 (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact norm_le_sum_coordinates q (f x)
  have he : (fun x => ∑ i : Fin q, ‖f x i‖) = ∑ i : Fin q, (fun x => ‖f x i‖) := by
    funext x
    simp
  rw [he] at hA
  have hB := eLpNorm_sum_le
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => (hf i).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [eLpNorm_norm] using hA.trans hB

theorem vector_word_L2_le_sum_coordinates {s n : ℕ} (hn : n ≤ s) (q : ℕ) (w : Fin n → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal ≤
      ∑ i : Fin q, (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
  have hc (i : Fin q) : MemLp (fun x => iteratedFieldDerivative period w f x i) 2 (liftMeasure period) := by
    have h := hfL2 i n hn w
    rw [iteratedFieldDerivative_postcomp period _ w f hf] at h
    exact h
  have hA := vector_eLpNorm_le_sum_coordinates period q (iteratedFieldDerivative period w f) hc
  have hfin : (∑ i : Fin q, eLpNorm (fun x => iteratedFieldDerivative period w f x i) 2 (liftMeasure period)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => (hc i).eLpNorm_ne_top)
  have hB := ENNReal.toReal_mono hfin hA
  rw [ENNReal.toReal_sum (fun i _ => (hc i).eLpNorm_ne_top)] at hB
  have he (i : Fin q) : (fun x => iteratedFieldDerivative period w f x i) =
      iteratedFieldDerivative period w (coordinate q i ∘ f) := by
    funext x
    exact (coordinate_word period q i w f hf x).symm
  simp_rw [he] at hB
  exact hB

/-- A vector Sobolev norm is controlled by the sum of its scalar coordinate norms. -/
theorem vector_sobolevNorm_le_sum_coordinates (q s : ℕ) (f : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ i : Fin q, ∀ j ≤ s, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ f)) 2 (liftMeasure period)) :
    liftSobolevNorm period s f ≤ ∑ i : Fin q, liftSobolevNorm period s (coordinate q i ∘ f) := by
  have hA : liftSobolevNorm period s f ≤
      ∑ n ∈ Finset.range (s+1), ∑ w : Fin n → Fin 4, ∑ i : Fin q,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro w _
    exact vector_word_L2_le_sum_coordinates period (by have := Finset.mem_range.1 hn; omega) q w f hf hfL2
  apply hA.trans_eq
  calc
    _ = ∑ n ∈ Finset.range (s+1), ∑ i : Fin q, ∑ w : Fin n → Fin 4,
        (eLpNorm (iteratedFieldDerivative period w (coordinate q i ∘ f)) 2 (liftMeasure period)).toReal := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem real_product_word_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (f*g)) 2 (liftMeasure period) := by
  have h := product_word_memLp period hn w (complexField period f) (complexField period g)
    (complexField_smooth period f hf) (complexField_smooth period g hg)
    (fun j hj v => by rw [complexField_word period v f hf]; exact complexField_memLp period _ (hfL2 j hj v))
    (fun j hj v => by rw [complexField_word period v g hg]; exact complexField_memLp period _ (hgL2 j hj v))
  have he : complexField period f * complexField period g = complexField period (f*g) := by
    ext x
    exact (Complex.ofReal_mul _ _).symm
  rw [he, complexField_word period w (f*g) (fun x => (hf x).mul (hg x))] at h
  apply h.of_le
    ((smoothField_continuous period _ (iteratedFieldDerivative_smooth period w (f*g)
      (fun x => (hf x).mul (hg x)))).aestronglyMeasurable)
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

omit [Fact (0 < period)] in
theorem coordinate_smul (q : ℕ) (i : Fin q) (f : LiftDomain period → ℝ) (g : LiftDomain period → Domain q) :
    coordinate q i ∘ (fun x => f x • g x) = f * (coordinate q i ∘ g) := by
  funext x
  simp [Function.comp_def, map_smul, smul_eq_mul]

/-- Multiplication of an actual vector field by a scalar field is bounded in H⁶. -/
theorem cylinder_H6_scalar_vector_product (q : ℕ) (f : LiftDomain period → ℝ)
    (g : LiftDomain period → Domain q)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    liftSobolevNorm period 6 (fun x => f x • g x) ≤
      ((q : ℝ) * (5461 * 128 * lowDerivativeConstant period)) *
        liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun x => f x • g x) x) :=
    fun x => (hf x).smul (hg x)
  have hcomp (i : Fin q) : ∀ j ≤ 6, ∀ v : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period v (coordinate q i ∘ g)) 2 (liftMeasure period) :=
    fun j hj v => postcomp_word_memLp period hj _ g hg hgL2 v
  have hA := vector_sobolevNorm_le_sum_coordinates period q 6 (fun x => f x • g x) hs
    (fun i j hj v => by
      rw [coordinate_smul]
      exact real_product_word_memLp period hj v f (coordinate q i ∘ g) hf
        (postcomp_smooth period _ g hg) hfL2 (hcomp i))
  have hB (i : Fin q) : liftSobolevNorm period 6 (coordinate q i ∘ (fun x => f x • g x)) ≤
      (5461 * 128 * lowDerivativeConstant period) * liftSobolevNorm period 6 f * liftSobolevNorm period 6 g := by
    rw [coordinate_smul]
    have h := real_cylinder_H6_algebra period f (coordinate q i ∘ g) hf (postcomp_smooth period _ g hg) hfL2 (hcomp i)
    exact h.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 6 _ (coordinate_norm_le q i) g hg hgL2)
      (mul_nonneg (mul_nonneg (by norm_num) (lowDerivativeConstant_nonneg period)) (liftSobolevNorm_nonneg period 6 f)))
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (q C A B : ℝ) : q*(C*A*B) = (q*C)*A*B := by ring
  exact hA.trans (hC.trans_eq (he _ _ _ _))

end EulerVectorCylinder

end

section

/-! A genuine coordinate transport commutator on R³ × T without derivative loss. -/

namespace EulerCylinderTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ)

/-- Repeated differentiation in one of the four actual cylinder coordinate directions. -/
noncomputable def pureFieldDerivative (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :=
  iteratedFieldDerivative period (fun _ : Fin n => i) f

@[simp] theorem pureFieldDerivative_zero (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period 0 i f = f := rfl

@[simp] theorem pureFieldDerivative_succ (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period (n+1) i f =
      fieldDerivative period (standardDirection i) (pureFieldDerivative period n i f) := rfl

theorem pureFieldDerivative_succ_right (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ) :
    pureFieldDerivative period (n+1) i f =
      pureFieldDerivative period n i (pureFieldDerivative period 1 i f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pureFieldDerivative_succ, ih, pureFieldDerivative_succ]
    rfl

theorem pureFieldDerivative_eq_iteratedDeriv (n : ℕ) (i : Fin 4) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    pureFieldDerivative period n i f x = iteratedDeriv n
      (fun t : ℝ => euclideanLift period f x (t • EuclideanSpace.single i 1)) 0 := by
  have hA := euclideanLift_iteratedFieldDerivative period (fun _ : Fin n => i) f hf x 0
  rw [euclideanLift_zero] at hA
  rw [pureFieldDerivative, hA, iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] Domain 4 := (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i 1)
  have hB := L.iteratedFDeriv_comp_right (euclideanLift_smooth period f hf x)
    (0 : ℝ) (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change _ = iteratedFDeriv ℝ n (euclideanLift period f x ∘ L) 0 (fun _ => 1)
  rw [hB]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem pureFieldDerivative_product (n : ℕ) (i : Fin 4) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    pureFieldDerivative period n i (f*g) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
        (pureFieldDerivative period j i f * pureFieldDerivative period (n-j) i g) := by
  funext x
  rw [pureFieldDerivative_eq_iteratedDeriv period n i (f*g) (product_smooth period f g hf hg)]
  have hline : ContDiff ℝ ∞ (fun t : ℝ => t • (EuclideanSpace.single i 1 : Domain 4)) :=
    contDiff_id.smul contDiff_const
  have hF := ((euclideanLift_smooth period f hf x).comp hline).of_le
    (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hG := ((euclideanLift_smooth period g hg x).comp hline).of_le
    (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have h := iteratedDeriv_mul (x := (0 : ℝ)) hF.contDiffAt hG.contDiffAt
  have he : (fun t : ℝ => euclideanLift period (f*g) x (t • EuclideanSpace.single i 1)) =
      (euclideanLift period f x ∘ (fun t : ℝ => t • EuclideanSpace.single i 1)) *
      (euclideanLift period g x ∘ (fun t : ℝ => t • EuclideanSpace.single i 1)) := rfl
  rw [he]
  simpa only [Function.comp_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
    pureFieldDerivative_eq_iteratedDeriv period _ i f hf,
    pureFieldDerivative_eq_iteratedDeriv period _ i g hg, mul_assoc] using h


/-- The actual commutator of pure coordinate differentiation with multiplication. -/
noncomputable def coordinateCommutator (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ) :=
  pureFieldDerivative period n i (b*h) - b * pureFieldDerivative period n i h

theorem coordinateCommutator_expansion (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    coordinateCommutator period n i b h = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      (pureFieldDerivative period j i (pureFieldDerivative period 1 i b) *
        pureFieldDerivative period (n-(j+1)) i h) := by
  unfold coordinateCommutator
  rw [pureFieldDerivative_product period n i b h hb hh, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pureFieldDerivative_zero, Nat.sub_zero,
    one_smul, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [pureFieldDerivative_succ_right]

variable [Fact (0 < period)]

theorem word_H3_le_H5 {m : ℕ} (hm : m ≤ 2) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period 5 f := by
  have hA : liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      ∑ n ∈ Finset.range 4, ∑ _v : Fin n → Fin 4, liftSobolevNorm period 5 f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  have he (A : ℝ) : (∑ n ∈ Finset.range 4, ∑ _v : Fin n → Fin 4, A) = 85*A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    norm_num [Finset.sum_range_succ]
    ring
  exact hA.trans_eq (he _)

theorem pureFieldDerivative_le_H5 {m : ℕ} (hm : m ≤ 2) (i : Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 5, ∀ w : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖pureFieldDerivative period m i f x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
  have hA := cylinder_pointwise_le_H3 period (pureFieldDerivative period m i f)
    (iteratedFieldDerivative_smooth period _ f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 5) v (fun _ => i) f hfL2) x
  have hB := mul_le_mul_of_nonneg_left (word_H3_le_H5 period hm (fun _ => i) f)
    (cylinderEmbeddingConstant_nonneg period)
  have he (C A : ℝ) : C*(85*A) = (85*C)*A := by ring
  exact hA.trans (hB.trans_eq (he _ _))

/-- An L² envelope depending only on five derivatives of each argument. -/
noncomputable def commutatorEnvelope (f g : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  liftSobolevNorm period 5 f • totalMagnitude period 5 g +
    liftSobolevNorm period 5 g • totalMagnitude period 5 f

theorem commutatorEnvelope_nonneg (f g : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ commutatorEnvelope period f g x :=
  add_nonneg (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg period 5 g x))
    (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg period 5 f x))

omit [Fact (0 < period)] in
theorem pureFieldDerivative_le_total {n : ℕ} (hn : n ≤ 5) (i : Fin 4)
    (f : LiftDomain period → ℂ) (x : LiftDomain period) :
    ‖pureFieldDerivative period n i f x‖ ≤ totalMagnitude period 5 f x := by
  have hA : ‖pureFieldDerivative period n i f x‖ ≤ wordMagnitude period n f x :=
    Finset.single_le_sum (f := fun w : Fin n → Fin 4 => ‖iteratedFieldDerivative period w f x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (fun _ => i))
  exact hA.trans (wordMagnitude_le_total period 5 n hn f x)

theorem pure_product_le_envelope {j k : ℕ} (hjk : j+k ≤ 5) (i : Fin 4)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ n ≤ 5, ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ n ≤ 5, ∀ w : Fin n → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖pureFieldDerivative period j i f x * pureFieldDerivative period k i g x‖ ≤
      (85 * cylinderEmbeddingConstant period) * commutatorEnvelope period f g x := by
  rw [norm_mul]
  have hc : 0 ≤ 85 * cylinderEmbeddingConstant period :=
    mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)
  by_cases hj : j ≤ 2
  · have hA := mul_le_mul (pureFieldDerivative_le_H5 period hj i f hf hfL2 x)
      (pureFieldDerivative_le_total period (by omega : k ≤ 5) i g x) (norm_nonneg _)
      (mul_nonneg hc (liftSobolevNorm_nonneg period 5 f))
    have hB : liftSobolevNorm period 5 f * totalMagnitude period 5 g x ≤ commutatorEnvelope period f g x :=
      le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg period 5 f x))
    rw [mul_assoc] at hA
    exact hA.trans (mul_le_mul_of_nonneg_left hB hc)
  · have hA := mul_le_mul (pureFieldDerivative_le_total period (by omega : j ≤ 5) i f x)
      (pureFieldDerivative_le_H5 period (by omega : k ≤ 2) i g hg hgL2 x) (norm_nonneg _)
      (totalMagnitude_nonneg period 5 f x)
    have hB : liftSobolevNorm period 5 g * totalMagnitude period 5 f x ≤ commutatorEnvelope period f g x :=
      le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg period 5 g x))
    have he (A B C : ℝ) : A*(B*C)=B*(C*A) := by ring
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hc))

theorem coordinateCommutator_pointwise_le {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖coordinateCommutator period n i b h x‖ ≤
      (64 * (85 * cylinderEmbeddingConstant period)) *
        commutatorEnvelope period (pureFieldDerivative period 1 i b) h x := by
  rw [coordinateCommutator_expansion period n i b h hb hh]
  have hA := norm_sum_le (Finset.range n) (fun j => (n.choose (j+1) : ℂ) •
    (pureFieldDerivative period j i (pureFieldDerivative period 1 i b) x *
      pureFieldDerivative period (n-(j+1)) i h x))
  simp only [norm_smul, Complex.norm_natCast] at hA
  have hB : (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
      ‖pureFieldDerivative period j i (pureFieldDerivative period 1 i b) x *
        pureFieldDerivative period (n-(j+1)) i h x‖) ≤
      (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ)) *
        ((85 * cylinderEmbeddingConstant period) *
          commutatorEnvelope period (pureFieldDerivative period 1 i b) h x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (pure_product_le_envelope period
      (by have := Finset.mem_range.1 hj; omega : j+(n-(j+1)) ≤ 5) i
      (pureFieldDerivative period 1 i b) h (iteratedFieldDerivative_smooth period _ b hb)
      hh hbL2 hhL2 x) (Nat.cast_nonneg _)
  have hchoose := EulerSobolevTransport.sum_choose_successors_le n
  have hp : (2 : ℝ)^n ≤ 64 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at h ⊢
    exact h
  have hc : 0 ≤ (85 * cylinderEmbeddingConstant period) *
      commutatorEnvelope period (pureFieldDerivative period 1 i b) h x :=
    mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
      (commutatorEnvelope_nonneg period _ _ x)
  have hC := mul_le_mul_of_nonneg_right (hchoose.trans hp) hc
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply] using
    hA.trans (hB.trans (hC.trans_eq (mul_assoc _ _ _).symm))

theorem commutatorEnvelope_memLp (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    MemLp (commutatorEnvelope period f g) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 5 g hgL2).const_smul (liftSobolevNorm period 5 f)).add
    ((totalMagnitude_memLp period 5 f hfL2).const_smul (liftSobolevNorm period 5 g))

theorem commutatorEnvelope_L2_le (f g : LiftDomain period → ℂ)
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (hgL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period v g) 2 (liftMeasure period)) :
    ‖(commutatorEnvelope_memLp period f g hfL2 hgL2).toLp (commutatorEnvelope period f g)‖ ≤
      2 * liftSobolevNorm period 5 f * liftSobolevNorm period 5 g := by
  change ‖liftSobolevNorm period 5 f • (totalMagnitude_memLp period 5 g hgL2).toLp _ +
    liftSobolevNorm period 5 g • (totalMagnitude_memLp period 5 f hfL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (liftSobolevNorm period 5 f • (totalMagnitude_memLp period 5 g hgL2).toLp (totalMagnitude period 5 g))
    (liftSobolevNorm period 5 g • (totalMagnitude_memLp period 5 f hfL2).toLp (totalMagnitude period 5 f))
  simp only [norm_smul, Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 f),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 g)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 g hgL2) (liftSobolevNorm_nonneg period 5 f))
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 f hfL2) (liftSobolevNorm_nonneg period 5 g))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

omit [Fact (0 < period)] in
theorem coordinateCommutator_smooth (n : ℕ) (i : Fin 4) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (coordinateCommutator period n i b h) x) := by
  intro x
  exact (iteratedFieldDerivative_smooth period _ (b*h) (product_smooth period b h hb hh) x).sub
    ((hb x).mul (iteratedFieldDerivative_smooth period _ h hh x))

/-- The commutator is in L²; neither factor needs compact support or decay assumptions beyond H⁵. -/
theorem coordinateCommutator_memLp {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    MemLp (coordinateCommutator period n i b h) 2 (liftMeasure period) := by
  apply (commutatorEnvelope_memLp period (pureFieldDerivative period 1 i b) h hbL2 hhL2).of_le_mul
    ((smoothField_continuous period _ (coordinateCommutator_smooth period n i b h hb hh)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (commutatorEnvelope_nonneg period _ _ x)]
  exact coordinateCommutator_pointwise_le period hn i b h hb hh hbL2 hhL2 x

/-- No derivative is lost: `[D_i^n,b]h` is controlled by H⁵ of `D_i b` and H⁵ of `h`. -/
theorem cylinder_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (i : Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w (pureFieldDerivative period 1 i b)) 2 (liftMeasure period))
    (hhL2 : ∀ k ≤ 5, ∀ w : Fin k → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    (eLpNorm (coordinateCommutator period n i b h) 2 (liftMeasure period)).toReal ≤
      (128 * 85 * cylinderEmbeddingConstant period) *
        liftSobolevNorm period 5 (pureFieldDerivative period 1 i b) * liftSobolevNorm period 5 h := by
  have hq := commutatorEnvelope_memLp period (pureFieldDerivative period 1 i b) h hbL2 hhL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖coordinateCommutator period n i b h x‖ ≤
      (64 * (85 * cylinderEmbeddingConstant period)) *
        ‖commutatorEnvelope period (pureFieldDerivative period 1 i b) h x‖ by
        rw [Real.norm_of_nonneg (commutatorEnvelope_nonneg period _ _ x)]
        exact coordinateCommutator_pointwise_le period hn i b h hb hh hbL2 hhL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 64 * (85 * cylinderEmbeddingConstant period) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period))
  have hfin : ENNReal.ofReal (64 * (85 * cylinderEmbeddingConstant period)) *
      eLpNorm (commutatorEnvelope period (pureFieldDerivative period 1 i b) h) 2 (liftMeasure period) ≠ ⊤ := by
    finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left
    (commutatorEnvelope_L2_le period (pureFieldDerivative period 1 i b) h hbL2 hhL2) hc
  rw [Lp.norm_toLp] at hC
  have he (C A B : ℝ) : (64*(85*C))*(2*A*B) = (128*85*C)*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

end EulerCylinderTransport

end

section

/-! Smooth compact cylinder fields realize the strong-translation Sobolev jets. -/

namespace EulerCompactSmoothJet

open MeasureTheory EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerSpatialSobolevInverse EulerPressureSpatialRegularity
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem iteratedFieldDerivative_compact {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f) :
    HasCompactSupport (iteratedFieldDerivative period w f) := by
  induction n with
  | zero => exact hfc
  | succ n ih => exact fieldDerivative_compact period _ _ (ih (Fin.tail w))

omit [Fact (0 < period)] in
/-- Splitting off the last direction agrees with the jet's derivative-word convention. -/
theorem iteratedFieldDerivative_init_last {n : ℕ} (w : Fin (n+1) → Fin 4)
    (f : LiftDomain period → Vector3) :
    iteratedFieldDerivative period w f = iteratedFieldDerivative period (Fin.init w)
      (fieldDerivative period (standardDirection (w (Fin.last n))) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fieldDerivative period (standardDirection (w 0))
      (iteratedFieldDerivative period (Fin.tail w) f) =
      fieldDerivative period (standardDirection (w 0))
        (iteratedFieldDerivative period (Fin.tail (Fin.init w))
          (fieldDerivative period (standardDirection (w (Fin.last (n+1)))) f))
    rw [ih (Fin.tail w)]
    rfl

theorem translation_hasDerivAt_smoothFieldLp (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    HasDerivAt (fun t => translation period (translationPath period a t)
      (smoothFieldLp period f hfc hf))
      (smoothFieldLp period (fieldDerivative period a f)
        (fieldDerivative_compact period a f hfc) (fieldDerivative_smooth period a f hf)) 0 :=
  smoothFieldLp_translation_hasDerivAt period a f hfc hf

/-- The actual strong L² translation jet of a smooth compact field. -/
noncomputable def compactSmoothJet (n : ℕ) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    SpatialJet period standardDirection n (smoothFieldLp period f hfc hf) :=
  match n with
  | 0 => .zero _
  | n+1 => .succ (fun i => smoothFieldLp period (fieldDerivative period (standardDirection i) f)
      (fieldDerivative_compact period _ f hfc) (fieldDerivative_smooth period _ f hf))
      (fun i => compactSmoothJet n (fieldDerivative period (standardDirection i) f)
        (fieldDerivative_compact period _ f hfc) (fieldDerivative_smooth period _ f hf))
      (fun i => translation_hasDerivAt_smoothFieldLp period (standardDirection i) f hfc hf)

theorem smoothFieldLp_congr (f g : LiftDomain period → Vector3) (he : f = g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    smoothFieldLp period f hfc hf = smoothFieldLp period g hgc hg := by
  subst g
  rfl

/-- Every word in the strong jet is represented by the corresponding actual smooth derivative. -/
theorem compactSmoothJet_word {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (compactSmoothJet period s f hfc hf).word w =
      smoothFieldLp period (iteratedFieldDerivative period w f)
        (iteratedFieldDerivative_compact period w f hfc) (iteratedFieldDerivative_smooth period w f hf) := by
  induction n generalizing s f with
  | zero => simp only [SpatialJet.word_zero, iteratedFieldDerivative_zero]
  | succ n ih =>
    cases s with
    | zero => omega
    | succ s =>
      rw [compactSmoothJet, SpatialJet.word_succ]
      rw [ih (by omega : n ≤ s)]
      exact smoothFieldLp_congr period _ _ (iteratedFieldDerivative_init_last period w f).symm _ _ _ _

/-- The L² norm of each jet word is exactly the norm of the actual classical derivative. -/
theorem compactSmoothJet_word_norm {s n : ℕ} (hn : n ≤ s) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hfc : HasCompactSupport f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ‖(compactSmoothJet period s f hfc hf).word w‖ =
      (eLpNorm (iteratedFieldDerivative period w f) 2 (liftMeasure period)).toReal := by
  rw [compactSmoothJet_word period hn w f hfc hf]
  rw [smoothFieldLp, Lp.norm_toLp]

/-- The strong Sobolev jet norm is exactly the actual derivative-word Sobolev norm. -/
theorem compactSmoothJet_sobolevNorm (s : ℕ) (f : LiftDomain period → Vector3)
    (hfc : HasCompactSupport f) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (compactSmoothJet period s f hfc hf).sobolevNorm = liftSobolevNorm period s f := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  exact compactSmoothJet_word_norm period (by have := Finset.mem_range.1 hn; omega) w f hfc hf

end EulerCompactSmoothJet

end

section

/-! Sobolev embedding for general smooth fields on R³, without Schwartz assumptions. -/

namespace EulerSmoothSobolev

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Repeated directional derivatives of a vector-valued Schwartz function. -/
noncomputable def pureDerivative (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) := ∂^{fun _ : Fin n => v} f

omit [CompleteSpace F] in
theorem fourier_pureDerivative_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    ‖𝓕 (pureDerivative d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [pureDerivative]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : pureDerivative d (n+1) v f = ∂_{v} (pureDerivative d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

omit [CompleteSpace F] in
theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

omit [CompleteSpace F] in
theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

omit [CompleteSpace F] in
theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, F))
    (g : ι → 𝓢(Domain d, F)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]

theorem sobolevNorm_two_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, F)) :
    sobolevNorm d 2 f ≤ 1 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin d, ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, F) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-2 : ℤ) : ℝ) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 2 f ξ‖ ≤ 1 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 2 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 2) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
        fourier_pureDerivative_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-2 : ℤ) * (2 * Real.pi) ^ (2 : ℕ) = 1 := by
        rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (le_of_eq (show besselWeight d 2 ξ = 1 + ∑ i, ‖ξ i‖ ^ 2 by norm_num [besselWeight, EuclideanSpace.norm_sq_eq])) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 2 f) g 1
    (by norm_num) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-2 : ℤ) * ∑ i : Fin d,
        ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ F 2 volume (((2 * Real.pi) ^ (-2 : ℤ)) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- The sharp three-dimensional H² pointwise bound in terms of actual second derivatives. -/
theorem pointwise_le_L2_second_derivatives (f : 𝓢(Domain 3, F)) (x : Domain 3) :
    ‖f x‖ ≤ embeddingConstant 3 2 (by norm_num) *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 3 2 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_two_le_pure_derivatives 3 f)
    (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  simpa only [one_mul] using hA.trans hB

/-- The sum of the actual L² norms of Fréchet derivatives through order `s`. -/
noncomputable def tensorSobolevNorm (s : ℕ) (f : Domain 3 → F) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_nonneg (s : ℕ) (f : Domain 3 → F) : 0 ≤ tensorSobolevNorm s f :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_mono {s t : ℕ} (hst : s ≤ t) (f : Domain 3 → F) :
    tensorSobolevNorm s f ≤ tensorSobolevNorm t f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => ENNReal.toReal_nonneg)

/-- Sum of the pointwise norms of all derivatives through a fixed order. -/
noncomputable def derivativeMagnitude (s : ℕ) (f : Domain 3 → F) (x : Domain 3) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => ‖iteratedFDeriv ℝ j f x‖)

omit [CompleteSpace F] in
theorem derivativeMagnitude_nonneg (s : ℕ) (f : Domain 3 → F) (x : Domain 3) :
    0 ≤ derivativeMagnitude s f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace F] in
theorem derivativeMagnitude_memLp (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (derivativeMagnitude s f) 2 volume :=
  memLp_finsetSum _ (fun j hj => (hfL2 j (by have := Finset.mem_range.1 hj; omega)).norm)

omit [CompleteSpace F] in
theorem derivativeMagnitude_L2_le (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    ‖(derivativeMagnitude_memLp s f hfL2).toLp (derivativeMagnitude s f)‖ ≤ tensorSobolevNorm s f := by
  have he : derivativeMagnitude s f = ∑ j ∈ Finset.range (s+1), fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    funext x
    simp [derivativeMagnitude]
  have hA : eLpNorm (derivativeMagnitude s f) 2 volume ≤
      ∑ j ∈ Finset.range (s+1), eLpNorm (iteratedFDeriv ℝ j f) 2 volume := by
    rw [he]
    simpa only [eLpNorm_norm] using eLpNorm_sum_le (fun j hj =>
      (hfL2 j (by have := Finset.mem_range.1 hj; omega)).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin (j : ℕ) (hj : j ∈ Finset.range (s+1)) : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≠ ⊤ :=
    (hfL2 j (by have := Finset.mem_range.1 hj; omega)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  exact hB

/-- A fixed bump equal to one near zero, independent of the function being estimated. -/
noncomputable def unitBump : ContDiffBump (0 : Domain 3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The same fixed bump as a Schwartz function. -/
noncomputable def unitBumpSchwartz : 𝓢(Domain 3, ℝ) :=
  unitBump.hasCompactSupport.toSchwartzMap unitBump.contDiff

/-- A finite derivative bound for the fixed bump. -/
noncomputable def unitBumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j unitBumpSchwartz, apply_nonneg _ _⟩

/-- The finite Leibniz coefficient for localizing an order `n` derivative. -/
noncomputable def unitBumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * unitBumpBound j)

/-- An actual smooth compact localization of an arbitrary smooth function about `x`. -/
noncomputable def localize (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) : 𝓢(Domain 3, F) :=
  (unitBump.hasCompactSupport.smul_right (f' := fun z => f (x+z))).toSchwartzMap
    (unitBump.contDiff.smul (hf.comp (contDiff_const.add contDiff_id)))

omit [CompleteSpace F] in
@[simp] theorem localize_apply (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    localize f hf x z = unitBump z • f (x+z) := rfl

omit [CompleteSpace F] in
theorem localize_zero (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    localize f hf x 0 = f x := by
  rw [localize_apply, unitBump.one_of_mem_closedBall (by simp [unitBump]), one_smul, add_zero]

omit [CompleteSpace F] in
/-- Localization obeys the actual tensor Leibniz estimate. -/
theorem localize_tensor_bound (n : ℕ) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    ‖iteratedFDeriv ℝ n (localize f hf x) z‖ ≤
      (unitBumpCoefficient n : ℝ) * derivativeMagnitude n f (x+z) := by
  have hshift : ContDiff ℝ ∞ (fun z => f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  have hA := norm_iteratedFDeriv_smul_le unitBump.contDiff
    hshift z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  have hb (j : ℕ) : ‖iteratedFDeriv ℝ j unitBump z‖ ≤ unitBumpBound j :=
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ unitBumpSchwartz j z
  have hd (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (fun z => f (x+z)) z‖ ≤ derivativeMagnitude n f (x+z) := by
    rw [iteratedFDeriv_comp_add_left]
    exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k f (x+z)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * unitBumpBound j) * derivativeMagnitude n f (x+z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)) (hd j hj)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (unitBumpBound j).coe_nonneg)
    _ = _ := by simp only [unitBumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast, Finset.sum_mul]

omit [CompleteSpace F] in
/-- Each localized pure derivative is controlled by the global physical Sobolev norm. -/
theorem localize_pureDerivative_L2_le (n : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ n, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖(pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖ ≤
      (unitBumpCoefficient n : ℝ) * tensorSobolevNorm n f := by
  have hq := derivativeMagnitude_memLp n f hfL2
  have htrans := measurePreserving_add_left (volume : Measure (Domain 3)) x
  have hqt : MemLp (fun z => derivativeMagnitude n f (x+z)) 2 volume := hq.comp_measurePreserving htrans
  have hb (z : Domain 3) :
      ‖pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x) z‖ ≤
        (unitBumpCoefficient n : ℝ) * ‖derivativeMagnitude n f (x+z)‖ := by
    rw [pureDerivative, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      Real.norm_of_nonneg (derivativeMagnitude_nonneg n f (x+z))]
    have hA := (iteratedFDeriv ℝ n (localize f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    exact hA.trans (localize_tensor_bound n f hf x z)
  have hA := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Domain 3)))
    (Filter.Eventually.of_forall hb) 2
  have hfin : (unitBumpCoefficient n : ℝ≥0∞) *
      eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  have he : eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume =
      eLpNorm (derivativeMagnitude n f) 2 volume := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hq.1 htrans
  rw [he] at hB
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hB
  rw [SchwartzMap.norm_toLp]
  have hC := mul_le_mul_of_nonneg_left (derivativeMagnitude_L2_le n f hfL2) (unitBumpCoefficient n).coe_nonneg
  rw [Lp.norm_toLp] at hC
  exact hB.trans hC

/-- A fixed finite three-dimensional H² embedding constant. -/
noncomputable def smoothEmbeddingConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    ((unitBumpCoefficient 0 : ℝ) + (2 * Real.pi)^(-2 : ℤ) * 3 * unitBumpCoefficient 2)

theorem smoothEmbeddingConstant_nonneg : 0 ≤ smoothEmbeddingConstant := by
  have h : 0 ≤ embeddingConstant 3 2 (by norm_num) := norm_nonneg _
  unfold smoothEmbeddingConstant
  positivity

/-- Genuine H² to L∞ embedding for every smooth Hilbert-valued function on R³. -/
theorem smooth_pointwise_le_H2 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖f x‖ ≤ smoothEmbeddingConstant * tensorSobolevNorm 2 f := by
  have hzero := localize_pureDerivative_L2_le 0 0 f hf (fun j hj => hfL2 j (by omega)) x
  have he : pureDerivative 3 0 (EuclideanSpace.single 0 1) (localize f hf x) = localize f hf x := by
    ext z
    simp [pureDerivative]
  rw [he] at hzero
  have hzero' := hzero.trans (mul_le_mul_of_nonneg_left (tensorSobolevNorm_mono (show 0 ≤ 2 by omega) f)
    (unitBumpCoefficient 0).coe_nonneg)
  have htwo : (∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖) ≤
      3 * ((unitBumpCoefficient 2 : ℝ) * tensorSobolevNorm 2 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localize_pureDerivative_L2_le 2 i f hf hfL2 x)
  have hA := pointwise_le_L2_second_derivatives (localize f hf x) 0
  rw [localize_zero] at hA
  have hB := add_le_add hzero' (mul_le_mul_of_nonneg_left htwo
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi) (-2 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  have harith (C A B p S : ℝ) : C * (A*S+p*(3*(B*S))) = (C*(A+p*3*B))*S := by ring
  exact hA.trans (hC.trans_eq (harith _ _ _ _ _))

/-- The actual derivative in one Euclidean coordinate direction. -/
noncomputable def coordinateDerivative (i : Fin 3) (f : Domain 3 → F) : Domain 3 → F :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

omit [CompleteSpace F] in
theorem coordinateDerivative_smooth (i : Fin 3) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateDerivative i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_bound (j : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  let L : (Domain 3 →L[ℝ] F) →L[ℝ] F :=
    ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i 1)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro A
    simpa only [L, ContinuousLinearMap.apply_apply, PiLp.norm_single, norm_one, one_mul, mul_one] using
      A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  have hA := L.norm_iteratedFDeriv_comp_left (x := x)
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).contDiffAt
    (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ _ at hA
  have hB := mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ j (fderiv ℝ f) x))
  rw [one_mul, norm_iteratedFDeriv_fderiv] at hB
  rw [norm_iteratedFDeriv_fderiv] at hA
  exact hA.trans hB

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_memLp {j : ℕ} (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ (j+1) f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (coordinateDerivative i f)) 2 volume :=
  hfL2.of_le ((coordinateDerivative_smooth i f hf).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    (Filter.Eventually.of_forall (coordinateDerivative_tensor_bound j i f hf))

omit [CompleteSpace F] in
theorem coordinateDerivative_H2_le_H3 (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    tensorSobolevNorm 2 (coordinateDerivative i f) ≤ 3 * tensorSobolevNorm 3 f := by
  have hA : tensorSobolevNorm 2 (coordinateDerivative i f) ≤
      ∑ _j ∈ Finset.range 3, tensorSobolevNorm 3 f := by
    apply Finset.sum_le_sum
    intro j hj
    have hj3 : j+1 ≤ 3 := by have := Finset.mem_range.1 hj; omega
    have hB := ENNReal.toReal_mono (hfL2 (j+1) hj3).eLpNorm_ne_top
      (eLpNorm_mono (coordinateDerivative_tensor_bound j i f hf))
    have hC : (eLpNorm (iteratedFDeriv ℝ (j+1) f) 2 volume).toReal ≤ tensorSobolevNorm 3 f :=
      Finset.single_le_sum (f := fun k => (eLpNorm (iteratedFDeriv ℝ k f) 2 volume).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (by omega))
    exact hB.trans hC
  simpa using hA

omit [CompleteSpace F] in
/-- A linear map is controlled by the sum of its values on the coordinate basis. -/
theorem linear_norm_le_coordinate_sum (A : Domain 3 →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx : (∑ i : Fin 3, (x i) • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hA : A x = ∑ i : Fin 3, (x i) • A (EuclideanSpace.single i (1 : ℝ)) := by
    simp_rw [← map_smul]
    rw [← map_sum, hx]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 3, ‖(x i) • A (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exact regularity needed in the limiting Euler contradiction: H³ controls the C¹ derivative. -/
theorem smooth_fderiv_le_H3 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * tensorSobolevNorm 3 f := by
  have hA := linear_norm_le_coordinate_sum (fderiv ℝ f x)
  have hB (i : Fin 3) : ‖coordinateDerivative i f x‖ ≤
      smoothEmbeddingConstant * (3 * tensorSobolevNorm 3 f) := by
    have hC := smooth_pointwise_le_H2 (coordinateDerivative i f) (coordinateDerivative_smooth i f hf)
      (fun j hj => coordinateDerivative_tensor_memLp i f hf (hfL2 (j+1) (by omega))) x
    exact hC.trans (mul_le_mul_of_nonneg_left (coordinateDerivative_H2_le_H3 i f hf hfL2)
      smoothEmbeddingConstant_nonneg)
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (C A : ℝ) : (3 : ℝ)*(C*(3*A)) = (9*C)*A := by ring
  exact hA.trans (hC.trans_eq (he _ _))

/-- The physical tensor Sobolev norm for real Euclidean vector fields. -/
noncomputable def realTensorSobolevNorm (q s : ℕ) (f : Domain 3 → Domain q) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

theorem complexification_tensor_norm (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (complexify q ∘ f) x‖ = ‖iteratedFDeriv ℝ j f x‖ :=
  (complexify q).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)

theorem complexification_tensor_memLp (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (complexify q ∘ f)) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ j (complexify q ∘ f)) :=
    ((complexify q).contDiff.comp hf).continuous_iteratedFDeriv (by simp)
  apply hfL2.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  exact (complexification_tensor_norm q j f hf x).le

theorem complexification_sobolevNorm (q s : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) :
    tensorSobolevNorm s (complexify q ∘ f) = realTensorSobolevNorm q s f := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (complexification_tensor_norm q j f hf))

/-- Real vector-valued H³ to C¹ on R³, for general smooth functions with actual L² derivatives. -/
theorem real_smooth_fderiv_le_H3 (q : ℕ) (f : Domain 3 → Domain q) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * realTensorSobolevNorm q 3 f := by
  have h := smooth_fderiv_le_H3 (complexify q ∘ f) ((complexify q).contDiff.comp hf)
    (fun j hj => complexification_tensor_memLp q j f hf (hfL2 j hj)) x
  have he : ‖fderiv ℝ (complexify q ∘ f) x‖ = ‖fderiv ℝ f x‖ := by
    simpa only [norm_iteratedFDeriv_one] using complexification_tensor_norm q 1 f hf x
  rw [he, complexification_sobolevNorm q 3 f hf] at h
  exact h

end EulerSmoothSobolev

end

section

/-! Strong L² derivatives of smooth representatives are their actual classical derivatives. -/

namespace EulerStrongSmoothJet

open MeasureTheory Filter EulerCylinderSobolev EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerLiftedWeakDerivative EulerSpatialSobolevInverse EulerPressureSpatialRegularity
open scoped ContDiff ENNReal Topology

section General
variable {X F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strong L² derivative agrees almost everywhere with a pointwise derivative.
The proof extracts an almost-everywhere convergent subsequence of the difference quotients. -/
theorem lp_derivative_ae (U : ℝ → Lp F 2 μ) (V : Lp F 2 μ)
    (u : ℝ → X → F) (v : X → F) (hrep : ∀ t, (U t : X → F) =ᵐ[μ] u t)
    (hU : HasDerivAt U V 0) (hu : ∀ x, HasDerivAt (fun t => u t x) (v x) 0) :
    (V : X → F) =ᵐ[μ] v := by
  have hQ (t : ℝ) : (slope U 0 t : X → F) =ᵐ[μ] (fun x => slope (fun r => u r x) 0 t) := by
    filter_upwards [Lp.coeFn_smul (t-0)⁻¹ (U t-U 0), Lp.coeFn_sub (U t) (U 0), hrep t, hrep 0]
      with x hsm hsub ht hzero
    simp only [Pi.smul_apply, Pi.sub_apply] at hsm hsub
    simp only [slope, vsub_eq_sub]
    rw [hsm, hsub, ht, hzero]
  obtain ⟨ts, hts, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hU.tendsto_slope).exists_seq_tendsto_ae'
  have hrepseq : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (slope U 0 (ts n)) x = slope (fun r => u r x) 0 (ts n) :=
    ae_all_iff.mpr (fun n => hQ (ts n))
  filter_upwards [hlim, hrepseq] with x hx hqx
  have hpoint := (hu x).tendsto_slope.comp hts
  have he : (fun n => (slope U 0 (ts n)) x) = (fun n => slope (fun r => u r x) 0 (ts n)) :=
    funext hqx
  rw [he] at hx
  exact tendsto_nhds_unique hx hpoint

end General

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- The pointwise translation orbit of a smooth cylinder field has its actual directional derivative. -/
theorem pointwise_translation_hasDerivAt (a : LiftTangent)
    (f : LiftDomain period → Vector3) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : LiftDomain period) :
    HasDerivAt (fun t => f (x + translationPath period a t)) (fieldDerivative period a f x) 0 := by
  have hF := (((hf x).differentiable (by simp)) ((0 : ℝ) • a)).hasFDerivAt
  have h := hF.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const a)
  convert! h using 1
  simp [fieldDerivative]

/-- Any strong translation derivative of a smooth representative is its classical derivative,
without compactness or a priori integrability of that classical derivative. -/
theorem translation_derivative_ae (a : LiftTangent) (U V : LiftL2 period)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : HasDerivAt (fun t => translation period (translationPath period a t) U) V 0) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] fieldDerivative period a f := by
  apply lp_derivative_ae (liftMeasure period)
    (fun t => translation period (translationPath period a t) U) V
    (fun t x => f (x + translationPath period a t)) (fieldDerivative period a f)
    ?_ hD (pointwise_translation_hasDerivAt period a f hf)
  intro t
  filter_upwards [translation_ae period (translationPath period a t) U,
    (measurePreserving_translation period (translationPath period a t)).quasiMeasurePreserving.ae hrep]
    with x htrans hx
  exact htrans.trans hx

/-- Every word of a strong Sobolev jet agrees with the actual classical word of a smooth representative. -/
theorem jet_word_ae {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] iteratedFieldDerivative period w f := by
  induction n with
  | zero => simpa only [SpatialJet.word_zero, iteratedFieldDerivative_zero] using hrep
  | succ n ih =>
    have hbase := ih (by omega : n ≤ s) (Fin.tail w)
    have hD := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have h := translation_derivative_ae period (standardDirection (w 0)) (J.word (Fin.tail w))
      (J.word (Fin.cons (w 0) (Fin.tail w))) (iteratedFieldDerivative period (Fin.tail w) f)
      hbase (iteratedFieldDerivative_smooth period (Fin.tail w) f hf) hD
    simpa only [Fin.cons_self_tail, iteratedFieldDerivative_succ] using h

/-- Strong jets force all actual classical derivatives through the corresponding order to lie in L². -/
theorem jet_classical_memLp {s n : ℕ} (hn : n ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (w : Fin n → Fin 4)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period) :=
  (Lp.memLp (J.word w)).ae_eq (jet_word_ae period hn U J w f hrep hf)

/-- The strong Sobolev jet norm is exactly the classical derivative Sobolev norm for any smooth representative. -/
theorem jet_sobolevNorm_eq {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U)
    (f : LiftDomain period → Vector3) (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    J.sobolevNorm = liftSobolevNorm period s f := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w _
  have h := eLpNorm_congr_ae (p := (2 : ℝ≥0∞))
    (jet_word_ae period (by have := Finset.mem_range.1 hn; omega) U J w f hrep hf)
  simpa only [Lp.norm_def] using congrArg ENNReal.toReal h

end EulerStrongSmoothJet

end

section

/-! Mixed coordinate transport commutators on the genuine cylinder. -/

namespace EulerMixedCylinderTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra EulerCylinderTransport
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal NNReal ContDiff Topology

variable (period : ℝ)

/-- Ordered cylinder differentiation indexed by a list. -/
noncomputable def listDerivative : List (Fin 4) → (LiftDomain period → ℂ) → LiftDomain period → ℂ
  | [], f => f
  | i::l, f => fieldDerivative period (standardDirection i) (listDerivative l f)

/-- The same list as a finite derivative word. -/
def listWord : (l : List (Fin 4)) → Fin l.length → Fin 4
  | [], i => Fin.elim0 i
  | i::l, j => Fin.cases i (listWord l) j

@[simp] theorem listDerivative_nil (f : LiftDomain period → ℂ) : listDerivative period [] f = f := rfl
@[simp] theorem listDerivative_cons (i : Fin 4) (l : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period (i::l) f = fieldDerivative period (standardDirection i) (listDerivative period l f) := rfl

theorem listDerivative_eq_word (l : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period l f = iteratedFieldDerivative period (listWord l) f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih]
    rfl

theorem listDerivative_smooth (l : List (Fin 4)) (f : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (listDerivative period l f) x) := by
  rw [listDerivative_eq_word]
  exact iteratedFieldDerivative_smooth period _ f hf

theorem listDerivative_append (l m : List (Fin 4)) (f : LiftDomain period → ℂ) :
    listDerivative period (l++m) f = listDerivative period l (listDerivative period m f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, listDerivative_cons, ih]

theorem fieldDerivative_add (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f+g) = fieldDerivative period a f + fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.add
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv

theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f-g) = fieldDerivative period a f - fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.sub
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  exact congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv

theorem fieldDerivative_mul (a : LiftTangent) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    fieldDerivative period a (f*g) = fieldDerivative period a f * g + f * fieldDerivative period a g := by
  funext x
  have h := (((hf x).differentiable (by simp)) 0).hasFDerivAt.mul
    (((hg x).differentiable (by simp)) 0).hasFDerivAt
  have he := congrArg (fun A : LiftTangent →L[ℝ] ℂ => A a) h.fderiv
  have hfg : localFieldLift period (f*g) x = localFieldLift period f x * localFieldLift period g x := rfl
  change fderiv ℝ (localFieldLift period (f*g) x) 0 a = _
  rw [hfg]
  have hzf : localFieldLift period f x 0 = f x := by simp [localFieldLift]
  have hzg : localFieldLift period g x 0 = g x := by simp [localFieldLift]
  rw [hzf, hzg] at he
  simpa [fieldDerivative, add_comm, mul_comm] using he

theorem listDerivative_add (l : List (Fin 4)) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    listDerivative period l (f+g) = listDerivative period l f + listDerivative period l g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih, fieldDerivative_add period _ _ _
      (listDerivative_smooth period l f hf) (listDerivative_smooth period l g hg)]
    rfl

theorem listDerivative_zero (l : List (Fin 4)) : listDerivative period l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [listDerivative_cons, ih]
    ext x
    change fderiv ℝ (fun _ : LiftTangent => (0 : ℂ)) 0 (standardDirection i) = 0
    simp

/-- The commutator of an arbitrary coordinate word and multiplication. -/
noncomputable def mixedCommutator (l : List (Fin 4)) (b h : LiftDomain period → ℂ) :=
  listDerivative period l (b*h) - b * listDerivative period l h

theorem mixedCommutator_smooth (l : List (Fin 4)) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (mixedCommutator period l b h) x) :=
  fun x => (listDerivative_smooth period l (b*h) (product_smooth period b h hb hh) x).sub
    ((hb x).mul (listDerivative_smooth period l h hh x))

/-- Exact telescoping step; the top derivative on the transported field cancels. -/
theorem mixedCommutator_cons (i : Fin 4) (l : List (Fin 4)) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    mixedCommutator period (i::l) b h =
      fieldDerivative period (standardDirection i) b * listDerivative period l h +
      fieldDerivative period (standardDirection i) (mixedCommutator period l b h) := by
  unfold mixedCommutator
  rw [fieldDerivative_sub period _ _ _
    (listDerivative_smooth period l (b*h) (product_smooth period b h hb hh))
    (product_smooth period b _ hb (listDerivative_smooth period l h hh)),
    fieldDerivative_mul period _ _ _ hb (listDerivative_smooth period l h hh)]
  simp only [listDerivative_cons]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

variable [Fact (0 < period)]

theorem word_pointwise_le_H5 {m : ℕ} (hm : m ≤ 2) (w : Fin m → Fin 4)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 5, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
  have hA := cylinder_pointwise_le_H3 period (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 5) v w f hfL2) x
  have hB := mul_le_mul_of_nonneg_left (word_H3_le_H5 period hm w f) (cylinderEmbeddingConstant_nonneg period)
  have he (C A : ℝ) : C*(85*A) = (85*C)*A := by ring
  exact hA.trans (hB.trans_eq (he _ _))

omit [Fact (0 < period)] in
theorem tensor_list_le_total {j : ℕ} (l : List (Fin 4)) (hjl : l.length+j ≤ 5)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ ≤
      1024 * totalMagnitude period 5 f x := by
  have hA := euclideanLift_tensor_norm_le period j (listDerivative period l f)
    (listDerivative_smooth period l f hf) x 0
  simp only [euclideanLift_zero] at hA
  have hB : (∑ w : Fin j → Fin 4, ‖iteratedFieldDerivative period w (listDerivative period l f) x‖) ≤
      (4 : ℝ)^j * totalMagnitude period 5 f x := by
    have hb (w : Fin j → Fin 4) : ‖iteratedFieldDerivative period w (listDerivative period l f) x‖ ≤
        totalMagnitude period 5 f x := by
      rw [listDerivative_eq_word]
      obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period w (listWord l) f
      rw [hu]
      exact (Finset.single_le_sum (f := fun v : Fin (l.length+j) → Fin 4 => ‖iteratedFieldDerivative period v f x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ u)).trans
          (wordMagnitude_le_total period 5 (l.length+j) hjl f x)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin j → Fin 4))) => hb w)
  have hp : (4 : ℝ)^j ≤ 1024 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show j ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  exact hA.trans (hB.trans (mul_le_mul_of_nonneg_right hp (totalMagnitude_nonneg period 5 f x)))

theorem tensor_list_low_le_H5 {j : ℕ} (l : List (Fin 4)) (hjl : l.length+j ≤ 2)
    (f : LiftDomain period → ℂ) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ k ≤ 5, ∀ v : Fin k → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ ≤
      1024 * ((85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f) := by
  have hA := euclideanLift_tensor_norm_le period j (listDerivative period l f)
    (listDerivative_smooth period l f hf) x 0
  simp only [euclideanLift_zero] at hA
  have hb (w : Fin j → Fin 4) : ‖iteratedFieldDerivative period w (listDerivative period l f) x‖ ≤
      (85 * cylinderEmbeddingConstant period) * liftSobolevNorm period 5 f := by
    rw [listDerivative_eq_word]
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period w (listWord l) f
    rw [hu]
    exact word_pointwise_le_H5 period hjl u f hf hfL2 x
  have hB := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin j → Fin 4))) => hb w)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hB
  have hp : (4 : ℝ)^j ≤ 1024 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show j ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  exact hA.trans (hB.trans (mul_le_mul_of_nonneg_right hp
    (mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)) (liftSobolevNorm_nonneg period 5 f))))

/-- A fixed finite constant for differentiated products of total order at most five. -/
noncomputable def mixedProductConstant : ℝ :=
  32 * (1024 * 1024 * (85 * cylinderEmbeddingConstant period))

theorem mixedProductConstant_nonneg : 0 ≤ mixedProductConstant period := by
  unfold mixedProductConstant
  exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))

theorem tensor_list_product_term_le (l m : List (Fin 4)) {j k : ℕ}
    (horder : (l.length+j)+(m.length+k) ≤ 5) (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖iteratedFDeriv ℝ j (euclideanLift period (listDerivative period l f) x) 0‖ *
      ‖iteratedFDeriv ℝ k (euclideanLift period (listDerivative period m g) x) 0‖ ≤
        (1024 * 1024 * (85 * cylinderEmbeddingConstant period)) * commutatorEnvelope period f g x := by
  have hc : 0 ≤ 85 * cylinderEmbeddingConstant period :=
    mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)
  have hK : 0 ≤ 1024 * 1024 * (85 * cylinderEmbeddingConstant period) := mul_nonneg (by norm_num) hc
  by_cases hl : l.length+j ≤ 2
  · have hA := mul_le_mul (tensor_list_low_le_H5 period l hl f hf hfL2 x)
      (tensor_list_le_total period m (by omega : m.length+k ≤ 5) g hg x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg hc (liftSobolevNorm_nonneg period 5 f)))
    have he (C A M : ℝ) : (1024*(C*A))*(1024*M) = (1024*1024*C)*(A*M) := by ring
    have hB : liftSobolevNorm period 5 f * totalMagnitude period 5 g x ≤ commutatorEnvelope period f g x :=
      le_add_of_nonneg_right (mul_nonneg (liftSobolevNorm_nonneg period 5 g) (totalMagnitude_nonneg period 5 f x))
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hK))
  · have hA := mul_le_mul (tensor_list_le_total period l (by omega : l.length+j ≤ 5) f hf x)
      (tensor_list_low_le_H5 period m (by omega : m.length+k ≤ 2) g hg hgL2 x) (norm_nonneg _)
      (mul_nonneg (by norm_num) (totalMagnitude_nonneg period 5 f x))
    have he (C A M : ℝ) : (1024*M)*(1024*(C*A)) = (1024*1024*C)*(A*M) := by ring
    have hB : liftSobolevNorm period 5 g * totalMagnitude period 5 f x ≤ commutatorEnvelope period f g x :=
      le_add_of_nonneg_left (mul_nonneg (liftSobolevNorm_nonneg period 5 f) (totalMagnitude_nonneg period 5 g x))
    exact hA.trans ((he _ _ _).trans_le (mul_le_mul_of_nonneg_left hB hK))

/-- Every prefixed product occurring in the telescoping commutator has a uniform H⁵ envelope. -/
theorem list_product_pointwise_le (l m : List (Fin 4)) (horder : l.length+m.length ≤ 5)
    (f g : LiftDomain period → ℂ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure period))
    (hgL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖listDerivative period l (f * listDerivative period m g) x‖ ≤
      mixedProductConstant period * commutatorEnvelope period f g x := by
  have hmg := listDerivative_smooth period m g hg
  have hprod := product_smooth period f (listDerivative period m g) hf hmg
  have he := euclideanLift_iteratedFieldDerivative period (listWord l) (f * listDerivative period m g) hprod x 0
  rw [euclideanLift_zero] at he
  rw [listDerivative_eq_word, he]
  have hA := (iteratedFDeriv ℝ l.length (euclideanLift period (f * listDerivative period m g) x) 0).le_opNorm
    (fun j => EuclideanSpace.single (listWord l j) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
  have hB := norm_iteratedFDeriv_mul_le (euclideanLift_smooth period f hf x)
    (euclideanLift_smooth period (listDerivative period m g) hmg x) 0
    (by simp : (l.length : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  have hC : (∑ j ∈ Finset.range (l.length+1), (l.length.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (euclideanLift period f x) 0‖ *
      ‖iteratedFDeriv ℝ (l.length-j) (euclideanLift period (listDerivative period m g) x) 0‖) ≤
      2^l.length * ((1024*1024*(85*cylinderEmbeddingConstant period)) * commutatorEnvelope period f g x) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (l.length+1), (l.length.choose j : ℝ) *
          ((1024*1024*(85*cylinderEmbeddingConstant period)) * commutatorEnvelope period f g x) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (tensor_list_product_term_le period [] m
          (by have := Finset.mem_range.1 hj; omega : (0+j)+(m.length+(l.length-j)) ≤ 5)
          f g hf hg hfL2 hgL2 x) (Nat.cast_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose l.length
  have hp : (2 : ℝ)^l.length ≤ 32 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show l.length ≤ 5 by omega)
    norm_num at h ⊢
    exact h
  have hD := mul_le_mul_of_nonneg_right hp (mul_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024*1024)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 85) (cylinderEmbeddingConstant_nonneg period)))
    (commutatorEnvelope_nonneg period f g x))
  exact hA.trans (hB.trans (hC.trans (hD.trans_eq (mul_assoc _ _ _).symm)))

/-- Sum of the H⁵ norms of all four actual first derivatives of the coefficient. -/
noncomputable def gradientSobolevNorm (b : LiftDomain period → ℂ) : ℝ :=
  ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b)

/-- Pointwise sum of all words of order at most five applied to the first coefficient derivatives. -/
noncomputable def gradientMagnitude (b : LiftDomain period → ℂ) (x : LiftDomain period) : ℝ :=
  ∑ i : Fin 4, totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) x

theorem gradientSobolevNorm_nonneg (b : LiftDomain period → ℂ) : 0 ≤ gradientSobolevNorm period b :=
  Finset.sum_nonneg (fun _ _ => liftSobolevNorm_nonneg period 5 _)

omit [Fact (0 < period)] in
theorem gradientMagnitude_nonneg (b : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ gradientMagnitude period b x := Finset.sum_nonneg (fun _ _ => totalMagnitude_nonneg period 5 _ x)

/-- One square-integrable envelope controls every mixed transport commutator through order six. -/
noncomputable def mixedEnvelope (b h : LiftDomain period → ℂ) : LiftDomain period → ℝ :=
  gradientSobolevNorm period b • totalMagnitude period 5 h + liftSobolevNorm period 5 h • gradientMagnitude period b

theorem mixedEnvelope_nonneg (b h : LiftDomain period → ℂ) (x : LiftDomain period) :
    0 ≤ mixedEnvelope period b h x :=
  add_nonneg (mul_nonneg (gradientSobolevNorm_nonneg period b) (totalMagnitude_nonneg period 5 h x))
    (mul_nonneg (liftSobolevNorm_nonneg period 5 h) (gradientMagnitude_nonneg period b x))

theorem commutatorEnvelope_le_mixed (i : Fin 4) (b h : LiftDomain period → ℂ) (x : LiftDomain period) :
    commutatorEnvelope period (fieldDerivative period (standardDirection i) b) h x ≤ mixedEnvelope period b h x := by
  have hS : liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b) ≤ gradientSobolevNorm period b :=
    Finset.single_le_sum (f := fun i : Fin 4 => liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b))
      (fun _ _ => liftSobolevNorm_nonneg period 5 _) (Finset.mem_univ i)
  have hM : totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) x ≤ gradientMagnitude period b x :=
    Finset.single_le_sum (f := fun i : Fin 4 => totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) x)
      (fun _ _ => totalMagnitude_nonneg period 5 _ x) (Finset.mem_univ i)
  exact add_le_add (mul_le_mul_of_nonneg_right hS (totalMagnitude_nonneg period 5 h x))
    (mul_le_mul_of_nonneg_left hM (liftSobolevNorm_nonneg period 5 h))

/-- The telescoping estimate remains valid under an arbitrary derivative prefix. -/
theorem prefixed_commutator_pointwise_le (outer inner : List (Fin 4))
    (horder : outer.length+inner.length ≤ 6) (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) (x : LiftDomain period) :
    ‖listDerivative period outer (mixedCommutator period inner b h) x‖ ≤
      (inner.length : ℝ) * mixedProductConstant period * mixedEnvelope period b h x := by
  induction inner generalizing outer with
  | nil =>
    have he : mixedCommutator period [] b h = 0 := by simp [mixedCommutator]
    rw [he, listDerivative_zero]
    simp
  | cons i inner ih =>
    rw [mixedCommutator_cons period i inner b h hb hh,
      listDerivative_add period outer _ _
        (product_smooth period _ _ (fieldDerivative_smooth period _ b hb) (listDerivative_smooth period inner h hh))
        (fieldDerivative_smooth period _ _ (mixedCommutator_smooth period inner b h hb hh))]
    have hA := norm_add_le
      (listDerivative period outer (fieldDerivative period (standardDirection i) b * listDerivative period inner h) x)
      (listDerivative period outer (fieldDerivative period (standardDirection i) (mixedCommutator period inner b h)) x)
    have hfirst := list_product_pointwise_le period outer inner
      (by simp only [List.length_cons] at horder; omega)
      (fieldDerivative period (standardDirection i) b) h (fieldDerivative_smooth period _ b hb) hh (hbL2 i) hhL2 x
    have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_left (commutatorEnvelope_le_mixed period i b h x)
      (mixedProductConstant_nonneg period))
    have hsecond := ih (outer ++ [i]) (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
    rw [listDerivative_append] at hsecond
    have hB := add_le_add hfirst' hsecond
    have he (n B Q : ℝ) : B*Q+n*B*Q=(n+1)*B*Q := by ring
    have hC := hA.trans (hB.trans_eq (he _ _ _))
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, Pi.add_apply] using hC

theorem gradientMagnitude_memLp (b : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period)) :
    MemLp (gradientMagnitude period b) 2 (liftMeasure period) :=
  memLp_finsetSum _ (fun i _ => totalMagnitude_memLp period 5 _ (hbL2 i))

theorem gradientMagnitude_L2_le (b : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period)) :
    ‖(gradientMagnitude_memLp period b hbL2).toLp (gradientMagnitude period b)‖ ≤ gradientSobolevNorm period b := by
  have he : gradientMagnitude period b = ∑ i : Fin 4,
      totalMagnitude period 5 (fieldDerivative period (standardDirection i) b) := by
    funext x
    simp [gradientMagnitude]
  have hA : eLpNorm (gradientMagnitude period b) 2 (liftMeasure period) ≤
      ∑ i : Fin 4, eLpNorm (totalMagnitude period 5 (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period) := by
    rw [he]
    exact eLpNorm_sum_le (fun i _ => (totalMagnitude_memLp period 5 _ (hbL2 i)).1) (by norm_num)
  have hfin (i : Fin 4) (_hi : i ∈ (Finset.univ : Finset (Fin 4))) :
      eLpNorm (totalMagnitude period 5 (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period) ≠ ⊤ :=
    (totalMagnitude_memLp period 5 _ (hbL2 i)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  apply hB.trans
  apply Finset.sum_le_sum
  intro i _
  have h := totalMagnitude_L2_le period 5 (fieldDerivative period (standardDirection i) b) (hbL2 i)
  rw [Lp.norm_toLp] at h
  exact h

theorem mixedEnvelope_memLp (b h : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    MemLp (mixedEnvelope period b h) 2 (liftMeasure period) :=
  ((totalMagnitude_memLp period 5 h hhL2).const_smul (gradientSobolevNorm period b)).add
    ((gradientMagnitude_memLp period b hbL2).const_smul (liftSobolevNorm period 5 h))

theorem mixedEnvelope_L2_le (b h : LiftDomain period → ℂ)
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    ‖(mixedEnvelope_memLp period b h hbL2 hhL2).toLp (mixedEnvelope period b h)‖ ≤
      2 * gradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  change ‖gradientSobolevNorm period b • (totalMagnitude_memLp period 5 h hhL2).toLp _ +
    liftSobolevNorm period 5 h • (gradientMagnitude_memLp period b hbL2).toLp _‖ ≤ _
  have hA := norm_add_le
    (gradientSobolevNorm period b • (totalMagnitude_memLp period 5 h hhL2).toLp (totalMagnitude period 5 h))
    (liftSobolevNorm period 5 h • (gradientMagnitude_memLp period b hbL2).toLp (gradientMagnitude period b))
  simp only [norm_smul, Real.norm_of_nonneg (gradientSobolevNorm_nonneg period b),
    Real.norm_of_nonneg (liftSobolevNorm_nonneg period 5 h)] at hA
  have hB := add_le_add
    (mul_le_mul_of_nonneg_left (totalMagnitude_L2_le period 5 h hhL2) (gradientSobolevNorm_nonneg period b))
    (mul_le_mul_of_nonneg_left (gradientMagnitude_L2_le period b hbL2) (liftSobolevNorm_nonneg period 5 h))
  have he (A B : ℝ) : A*B+B*A = 2*A*B := by ring
  exact hA.trans (hB.trans_eq (he _ _))

theorem mixedCommutator_pointwise_le (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖mixedCommutator period l b h x‖ ≤ (6 * mixedProductConstant period) * mixedEnvelope period b h x := by
  have hA := prefixed_commutator_pointwise_le period [] l (by simpa using hl) b h hb hh hbL2 hhL2 x
  have hB := mul_le_mul_of_nonneg_right (show (l.length : ℝ) ≤ 6 by exact_mod_cast hl)
    (mul_nonneg (mixedProductConstant_nonneg period) (mixedEnvelope_nonneg period b h x))
  rw [← mul_assoc, ← mul_assoc] at hB
  exact hA.trans hB

/-- Every mixed commutator through order six is a genuine L² function. -/
theorem mixedCommutator_memLp (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    MemLp (mixedCommutator period l b h) 2 (liftMeasure period) := by
  apply (mixedEnvelope_memLp period b h hbL2 hhL2).of_le_mul
    ((smoothField_continuous period _ (mixedCommutator_smooth period l b h hb hh)).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (mixedEnvelope_nonneg period b h x)]
  exact mixedCommutator_pointwise_le period l hl b h hb hh hbL2 hhL2 x

/-- The full mixed coordinate commutator bound, with no derivative loss. -/
theorem mixed_transport_commutator_L2 (l : List (Fin 4)) (hl : l.length ≤ 6)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ w : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period w (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ w : Fin r → Fin 4, MemLp (iteratedFieldDerivative period w h) 2 (liftMeasure period)) :
    (eLpNorm (mixedCommutator period l b h) 2 (liftMeasure period)).toReal ≤
      (12 * mixedProductConstant period) * gradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  have hq := mixedEnvelope_memLp period b h hbL2 hhL2
  have hA := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := liftMeasure period)
    (Filter.Eventually.of_forall (fun x => show ‖mixedCommutator period l b h x‖ ≤
      (6 * mixedProductConstant period) * ‖mixedEnvelope period b h x‖ by
      rw [Real.norm_of_nonneg (mixedEnvelope_nonneg period b h x)]
      exact mixedCommutator_pointwise_le period l hl b h hb hh hbL2 hhL2 x)) (2 : ℝ≥0∞)
  have hc : 0 ≤ 6 * mixedProductConstant period := mul_nonneg (by norm_num) (mixedProductConstant_nonneg period)
  have hfin : ENNReal.ofReal (6 * mixedProductConstant period) *
      eLpNorm (mixedEnvelope period b h) 2 (liftMeasure period) ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hB
  have hC := mul_le_mul_of_nonneg_left (mixedEnvelope_L2_le period b h hbL2 hhL2) hc
  rw [Lp.norm_toLp] at hC
  have he (C A B : ℝ) : (6*C)*(2*A*B)=(12*C)*A*B := by ring
  exact hB.trans (hC.trans_eq (he _ _ _))

omit [Fact (0 < period)] in
theorem listDerivative_ofFn {n : ℕ} (w : Fin n → Fin 4) (f : LiftDomain period → ℂ) :
    listDerivative period (List.ofFn w) f = iteratedFieldDerivative period w f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, listDerivative_cons, ih]
    rfl

/-- The same no-loss estimate in the finite-word convention used by the Sobolev jets. -/
theorem word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℂ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w (b*h) - b*iteratedFieldDerivative period w h) 2 (liftMeasure period)).toReal ≤
      (12 * mixedProductConstant period) * gradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  have hA := mixed_transport_commutator_L2 period (List.ofFn w) (by simpa using hn) b h hb hh hbL2 hhL2
  simpa only [mixedCommutator, listDerivative_ofFn] using hA

end EulerMixedCylinderTransport

end

section

/-! Actual full cylinder gradients from the coordinate derivative Sobolev norms. -/

namespace EulerCylinderGradient

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
open EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- All low-order real vector derivative words are bounded by the actual H⁶ norm. -/
theorem vector_word_pointwise_le_H6 (q : ℕ) {m : ℕ} (hm : m ≤ 3) (w : Fin m → Fin 4)
    (f : LiftDomain period → Domain q) (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : ∀ j ≤ 6, ∀ v : Fin j → Fin 4, MemLp (iteratedFieldDerivative period v f) 2 (liftMeasure period))
    (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      ((q : ℝ) * cylinderEmbeddingConstant period) * (85 * liftSobolevNorm period 6 f) := by
  have hA := vector_cylinder_pointwise_le_H3 period q (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ 6) v w f hfL2) x
  exact hA.trans (mul_le_mul_of_nonneg_left (word_H3_le_H6 period hm w f)
    (mul_nonneg (Nat.cast_nonneg _) (cylinderEmbeddingConstant_nonneg period)))

section General
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Fact (0 < period)] in
theorem tangent_coordinate_norm_le (v : LiftTangent) (i : Fin 4) :
    ‖coordinateEquiv.symm v i‖ ≤ ‖v‖ := by
  cases i using Fin.cases with
  | zero => simpa using norm_snd_le v
  | succ i => exact (PiLp.norm_apply_le v.1 i).trans (norm_fst_le v)

omit [Fact (0 < period)] in
/-- The full product-tangent operator norm is bounded by its four coordinate values. -/
theorem linear_norm_le_standard_sum (A : LiftTangent →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 4, ‖A (standardDirection i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  have he : (∑ i : Fin 4, (coordinateEquiv.symm v i) • EuclideanSpace.single i (1 : ℝ)) = coordinateEquiv.symm v := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hv : (∑ i : Fin 4, (coordinateEquiv.symm v i) • standardDirection i) = v := by
    change (∑ i : Fin 4, (coordinateEquiv.symm v i) • coordinateEquiv (EuclideanSpace.single i (1 : ℝ))) = v
    simp_rw [← map_smul]
    rw [← map_sum, he, ContinuousLinearEquiv.apply_symm_apply]
  have hA : A v = ∑ i : Fin 4, (coordinateEquiv.symm v i) • A (standardDirection i) := by
    simp_rw [← map_smul]
    rw [← map_sum, hv]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 4, ‖(coordinateEquiv.symm v i) • A (standardDirection i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖coordinateEquiv.symm v i‖ * ‖A (standardDirection i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 4, ‖v‖ * ‖A (standardDirection i)‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (tangent_coordinate_norm_le v i) (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

omit [Fact (0 < period)] in
theorem fieldFDeriv_norm_le_standard_sum (f : LiftDomain period → F) (x : LiftDomain period) :
    ‖fieldFDeriv period f x‖ ≤ ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖ :=
  linear_norm_le_standard_sum (fieldFDeriv period f x)

/-- Actual full gradient integrability follows from the four genuine coordinate derivatives. -/
theorem fieldFDeriv_memLp_of_coordinates (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure period)) :
    MemLp (fieldFDeriv period f) 2 (liftMeasure period) := by
  have hsum : MemLp (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2 (liftMeasure period) :=
    memLp_finsetSum _ (fun i _ => (hD i).norm)
  have hc : Continuous (fieldFDeriv period f) := smoothField_continuous period _ (fieldFDeriv_smooth period f hf)
  apply hsum.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact fieldFDeriv_norm_le_standard_sum period f x

/-- The full-gradient L² norm is quantitatively bounded by the coordinate-gradient L² sum. -/
theorem fieldFDeriv_L2_le_coordinate_sum (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hD : ∀ i : Fin 4, MemLp (fieldDerivative period (standardDirection i) f) 2 (liftMeasure period)) :
    ‖(fieldFDeriv_memLp_of_coordinates period f hf hD).toLp (fieldFDeriv period f)‖ ≤
      ∑ i : Fin 4, (eLpNorm (fieldDerivative period (standardDirection i) f) 2 (liftMeasure period)).toReal := by
  have hA : eLpNorm (fieldFDeriv period f) 2 (liftMeasure period) ≤
      eLpNorm (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) 2 (liftMeasure period) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact fieldFDeriv_norm_le_standard_sum period f x
  have he : (fun x => ∑ i : Fin 4, ‖fieldDerivative period (standardDirection i) f x‖) =
      ∑ i : Fin 4, (fun x => ‖fieldDerivative period (standardDirection i) f x‖) := by funext x; simp
  rw [he] at hA
  have hB := eLpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => (hD i).1.norm)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simp only [eLpNorm_norm] at hB
  have hC := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => (hD i).eLpNorm_ne_top)) (hA.trans hB)
  rw [ENNReal.toReal_sum (fun i _ => (hD i).eLpNorm_ne_top)] at hC
  rw [Lp.norm_toLp]
  exact hC

end General
end EulerCylinderGradient

end

section

/-! Real scalar and vector forms of the full mixed cylinder commutator estimate. -/

namespace EulerRealMixedTransport

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra EulerMixedCylinderTransport
open EulerRealCylinder EulerVectorCylinder EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open scoped ENNReal ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- The sum of H⁵ norms of the four real coordinate derivatives of a scalar coefficient. -/
noncomputable def realGradientSobolevNorm (b : LiftDomain period → ℝ) : ℝ :=
  ∑ i : Fin 4, liftSobolevNorm period 5 (fieldDerivative period (standardDirection i) b)

theorem realGradientSobolevNorm_nonneg (b : LiftDomain period → ℝ) : 0 ≤ realGradientSobolevNorm period b :=
  Finset.sum_nonneg (fun _ _ => liftSobolevNorm_nonneg period 5 _)

omit [Fact (0 < period)] in
theorem complexField_fieldDerivative (i : Fin 4) (b : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x)) :
    fieldDerivative period (standardDirection i) (complexField period b) =
      complexField period (fieldDerivative period (standardDirection i) b) :=
  fieldDerivative_postcomp period Complex.ofRealCLM (standardDirection i) b hb

theorem complexField_gradientSobolevNorm (b : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x)) :
    gradientSobolevNorm period (complexField period b) = realGradientSobolevNorm period b := by
  apply Finset.sum_congr rfl
  intro i _
  rw [complexField_fieldDerivative period i b hb,
    complexField_sobolevNorm period 5 _ (fieldDerivative_smooth period _ b hb)]

omit [Fact (0 < period)] in
theorem complexField_mul (f g : LiftDomain period → ℝ) :
    complexField period f * complexField period g = complexField period (f*g) := by
  funext x
  exact (Complex.ofReal_mul _ _).symm

omit [Fact (0 < period)] in
theorem complexField_sub (f g : LiftDomain period → ℝ) :
    complexField period f - complexField period g = complexField period (f-g) := by
  funext x
  exact (Complex.ofReal_sub _ _).symm

omit [Fact (0 < period)] in
theorem complexField_commutator {n : ℕ} (w : Fin n → Fin 4) (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    iteratedFieldDerivative period w (complexField period b * complexField period h) -
      complexField period b * iteratedFieldDerivative period w (complexField period h) =
        complexField period (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) := by
  rw [complexField_mul, complexField_word period w (b*h) (fun x => (hb x).mul (hh x)),
    complexField_word period w h hh, complexField_mul, complexField_sub]

/-- The full real scalar mixed-word transport commutator bound. -/
theorem real_word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure period)) :
    (eLpNorm (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) 2 (liftMeasure period)).toReal ≤
      (12*mixedProductConstant period) * realGradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  have hbC : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) (complexField period b)))
        2 (liftMeasure period) := by
    intro i r hr v
    rw [complexField_fieldDerivative period i b hb,
      complexField_word period v _ (fieldDerivative_smooth period _ b hb)]
    exact complexField_memLp period _ (hbL2 i r hr v)
  have hhC : ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (complexField period h)) 2 (liftMeasure period) := by
    intro r hr v
    rw [complexField_word period v h hh]
    exact complexField_memLp period _ (hhL2 r hr v)
  have hA := word_transport_commutator_L2 period hn w (complexField period b) (complexField period h)
    (complexField_smooth period b hb) (complexField_smooth period h hh) hbC hhC
  rw [complexField_commutator period w b h hb hh, complexField_eLpNorm,
    complexField_gradientSobolevNorm period b hb, complexField_sobolevNorm period 5 h hh] at hA
  exact hA

/-- The corresponding real commutator is in L², not merely assigned an extended seminorm. -/
theorem real_word_commutator_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4)
    (b h : LiftDomain period → ℝ)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure period)) :
    MemLp (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) 2 (liftMeasure period) := by
  have hbC : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) (complexField period b)))
        2 (liftMeasure period) := by
    intro i r hr v
    rw [complexField_fieldDerivative period i b hb,
      complexField_word period v _ (fieldDerivative_smooth period _ b hb)]
    exact complexField_memLp period _ (hbL2 i r hr v)
  have hhC : ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (complexField period h)) 2 (liftMeasure period) := by
    intro r hr v
    rw [complexField_word period v h hh]
    exact complexField_memLp period _ (hhL2 r hr v)
  have hA := mixedCommutator_memLp period (List.ofFn w) (by simpa using hn)
    (complexField period b) (complexField period h) (complexField_smooth period b hb) (complexField_smooth period h hh) hbC hhC
  simp only [mixedCommutator, listDerivative_ofFn] at hA
  rw [complexField_commutator period w b h hb hh] at hA
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period
      (iteratedFieldDerivative period w (b*h)-b*iteratedFieldDerivative period w h) x) :=
    fun x => (iteratedFieldDerivative_smooth period w (b*h) (fun y => (hb y).mul (hh y)) x).sub
      ((hb x).mul (iteratedFieldDerivative_smooth period w h hh x))
  apply hA.of_le (smoothField_continuous period _ hs).aestronglyMeasurable
  filter_upwards [] with x
  exact (Complex.norm_real _).ge

/-- The actual scalar-coefficient commutator acting on a real vector field. -/
noncomputable def vectorCommutator {n : ℕ} (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q) : LiftDomain period → Domain q :=
  iteratedFieldDerivative period w (fun x => b x • h x) -
    (fun x => b x • iteratedFieldDerivative period w h x)

omit [Fact (0 < period)] in
theorem coordinate_vectorCommutator {n : ℕ} (w : Fin n → Fin 4) (q : ℕ) (i : Fin q)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x)) :
    coordinate q i ∘ vectorCommutator period w q b h =
      iteratedFieldDerivative period w (b*(coordinate q i ∘ h)) -
        b*iteratedFieldDerivative period w (coordinate q i ∘ h) := by
  rw [← coordinate_smul]
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (fun y => b y • h y) x) := fun x => (hb x).smul (hh x)
  rw [iteratedFieldDerivative_postcomp period (coordinate q i) w (fun x => b x • h x) hs,
    iteratedFieldDerivative_postcomp period (coordinate q i) w h hh]
  funext x
  simp [vectorCommutator, Function.comp_def, map_sub, map_smul, smul_eq_mul]

/-- The full mixed transport commutator for real vector fields on the cylinder. -/
theorem vector_word_transport_commutator_L2 {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure period)) :
    (eLpNorm (vectorCommutator period w q b h) 2 (liftMeasure period)).toReal ≤
      ((q : ℝ) * (12*mixedProductConstant period)) * realGradientSobolevNorm period b * liftSobolevNorm period 5 h := by
  have hcoords (i : Fin q) : MemLp (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure period) := by
    have hA := real_word_commutator_memLp period hn w b (coordinate q i ∘ h) hb (postcomp_smooth period _ h hh)
      hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2 v)
    rw [← coordinate_vectorCommutator period w q i b h hb hh] at hA
    exact hA
  have hA := vector_eLpNorm_le_sum_coordinates period q (vectorCommutator period w q b h) hcoords
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 (fun i _ => (hcoords i).eLpNorm_ne_top)) hA
  rw [ENNReal.toReal_sum (fun i _ => (hcoords i).eLpNorm_ne_top)] at hB
  have hC (i : Fin q) : (eLpNorm (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure period)).toReal ≤
      (12*mixedProductConstant period) * realGradientSobolevNorm period b * liftSobolevNorm period 5 h := by
    change (eLpNorm (coordinate q i ∘ vectorCommutator period w q b h) 2 (liftMeasure period)).toReal ≤ _
    rw [coordinate_vectorCommutator period w q i b h hb hh]
    have hbound := real_word_transport_commutator_L2 period hn w b (coordinate q i ∘ h) hb
      (postcomp_smooth period _ h hh) hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2 v)
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (postcomp_sobolevNorm_le period 5 _ (coordinate_norm_le q i) h hh hhL2)
      (mul_nonneg (mul_nonneg (by norm_num) (mixedProductConstant_nonneg period)) (realGradientSobolevNorm_nonneg period b)))
  have hD := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hC i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hD
  have he (q C A B : ℝ) : q*(C*A*B)=(q*C)*A*B := by ring
  exact hB.trans (hD.trans_eq (he _ _ _ _))

/-- The full real vector transport commutator belongs to L² under the same derivative hypotheses. -/
theorem vector_word_commutator_memLp {n : ℕ} (hn : n ≤ 6) (w : Fin n → Fin 4) (q : ℕ)
    (b : LiftDomain period → ℝ) (h : LiftDomain period → Domain q)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hh : ∀ x, ContDiff ℝ ∞ (localFieldLift period h x))
    (hbL2 : ∀ i : Fin 4, ∀ r ≤ 5, ∀ v : Fin r → Fin 4,
      MemLp (iteratedFieldDerivative period v (fieldDerivative period (standardDirection i) b)) 2 (liftMeasure period))
    (hhL2 : ∀ r ≤ 5, ∀ v : Fin r → Fin 4, MemLp (iteratedFieldDerivative period v h) 2 (liftMeasure period)) :
    MemLp (vectorCommutator period w q b h) 2 (liftMeasure period) := by
  have hcoords (i : Fin q) : MemLp (fun x => vectorCommutator period w q b h x i) 2 (liftMeasure period) := by
    have hA := real_word_commutator_memLp period hn w b (coordinate q i ∘ h) hb (postcomp_smooth period _ h hh)
      hbL2 (fun r hr v => postcomp_word_memLp period hr _ h hh hhL2 v)
    rw [← coordinate_vectorCommutator period w q i b h hb hh] at hA
    exact hA
  have hs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (vectorCommutator period w q b h) x) := by
    intro x
    exact (iteratedFieldDerivative_smooth period w (fun y => b y • h y) (fun y => (hb y).smul (hh y)) x).sub
      ((hb x).smul (iteratedFieldDerivative_smooth period w h hh x))
  refine ⟨(smoothField_continuous period _ hs).aestronglyMeasurable, ?_⟩
  exact (vector_eLpNorm_le_sum_coordinates period q _ hcoords).trans_lt
    (ENNReal.sum_lt_top.2 (fun i _ => (hcoords i).eLpNorm_lt_top))

end EulerRealMixedTransport

end

section

/-! Genuine approximate identities for the lifted L² translation representation. -/


namespace EulerCylinderMollifier

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderCoordinates
  EulerSobolev EulerNoncompactTransport EulerSpatialSobolevInverse
open scoped ContDiff ENNReal NNReal Topology Convolution

variable (period : ℝ) [Fact (0 < period)]

/-- Actual cylinder translations act strongly continuously on L². -/
theorem translation_continuous (f : LiftL2 period) :
    Continuous (fun a : LiftDomain period => translation period a f) := by
  let g : LiftDomain period → C(LiftDomain period, LiftDomain period) :=
    fun a => ⟨fun x => x + a, continuous_id.add_const a⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  have h := (continuous_const : Continuous (fun _ : LiftDomain period => f)).compMeasurePreservingLp
    hg (fun a => measurePreserving_translation period a) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  convert h using 1
  funext a
  rfl

omit [Fact (0 < period)] in
theorem euclideanCover_continuous : Continuous (euclideanCover period) := by
  exact ((continuous_fst).prodMk ((AddCircle.continuous_mk' period).comp continuous_snd)).comp coordinateEquiv.continuous

omit [Fact (0 < period)] in
theorem euclideanCover_add (x y : Domain 4) :
    euclideanCover period (x + y) = euclideanCover period x + euclideanCover period y := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_zero : euclideanCover period 0 = 0 := by
  ext i <;> simp [euclideanCover, coveringMap]

/-- The actual L² translation orbit in Euclidean covering coordinates. -/
def orbit (f : LiftL2 period) (x : Domain 4) : LiftL2 period :=
  translation period (euclideanCover period x) f

theorem orbit_continuous (f : LiftL2 period) : Continuous (orbit period f) :=
  (translation_continuous period f).comp (euclideanCover_continuous period)

@[simp]
theorem orbit_zero (f : LiftL2 period) : orbit period f 0 = f := by
  simp [orbit, euclideanCover_zero, translation_zero]

theorem orbit_norm (f : LiftL2 period) (x : Domain 4) : ‖orbit period f x‖ = ‖f‖ :=
  translation_norm period _ f

/-- A normalized approximate-identity bump with radii tending to zero. -/
def mollifierBump (n : ℕ) : ContDiffBump (0 : Domain 4) where
  rIn := cutoffScale n
  rOut := 2 * cutoffScale n
  rIn_pos := cutoffScale_pos n
  rIn_lt_rOut := by have h := cutoffScale_pos n; linarith

/-- The real smooth compact approximate-identity kernel. -/
def mollifierKernel (n : ℕ) : Domain 4 → ℝ := (mollifierBump n).normed volume

theorem mollifierKernel_smooth (n : ℕ) : ContDiff ℝ ∞ (mollifierKernel n) :=
  (mollifierBump n).contDiff_normed

theorem mollifierKernel_compact (n : ℕ) : HasCompactSupport (mollifierKernel n) :=
  (mollifierBump n).hasCompactSupport_normed

theorem mollifierKernel_nonneg (n : ℕ) (x : Domain 4) : 0 ≤ mollifierKernel n x :=
  (mollifierBump n).nonneg_normed x

theorem mollifierKernel_integral (n : ℕ) : ∫ x, mollifierKernel n x = 1 :=
  (mollifierBump n).integral_normed

/-- Bochner convolution of the actual L² orbit with the smooth approximate identity. -/
def smoothOrbit (n : ℕ) (f : LiftL2 period) : Domain 4 → LiftL2 period :=
  convolution (mollifierKernel n) (orbit period f) (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The actual L² mollification; its expected representative is the classical periodic convolution. -/
def mollify (n : ℕ) (f : LiftL2 period) : LiftL2 period := smoothOrbit period n f 0

theorem smoothOrbit_contDiff (n : ℕ) (f : LiftL2 period) : ContDiff ℝ ∞ (smoothOrbit period n f) :=
  (mollifierKernel_compact n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifierKernel_smooth n) (orbit_continuous period f).locallyIntegrable

/-- These actual smoothings converge strongly in the genuine cylinder L² space. -/
theorem mollify_tendsto (f : LiftL2 period) :
    Filter.Tendsto (fun n => mollify period n f) Filter.atTop (𝓝 f) := by
  have hr : Filter.Tendsto (fun n => (mollifierBump n).rOut) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mollifierBump, mul_zero] using cutoffScale_tendsto.const_mul 2
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Domain 4)))
    hr (orbit_continuous period f) 0
  simpa only [orbit_zero, mollify, smoothOrbit, mollifierKernel] using h

theorem mollify_eq_integral (n : ℕ) (f : LiftL2 period) :
    mollify period n f = ∫ y : Domain 4, mollifierKernel n y • orbit period f (-y) := by
  simp only [mollify, smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub]

theorem kernel_orbit_integrable (n : ℕ) (f : LiftL2 period) :
    Integrable (fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) :=
  ((mollifierKernel_smooth n).continuous.smul ((orbit_continuous period f).comp continuous_neg)).integrable_of_hasCompactSupport
    (mollifierKernel_compact n).smul_right

/-- Smoothing is contractive in the actual cylinder L² norm. -/
theorem mollify_norm_le (n : ℕ) (f : LiftL2 period) : ‖mollify period n f‖ ≤ ‖f‖ := by
  rw [mollify_eq_integral]
  have h := norm_integral_le_of_norm_le
    (((mollifierBump n).integrable_normed (μ := (volume : Measure (Domain 4)))).mul_const ‖f‖)
    (f := fun y : Domain 4 => mollifierKernel n y • orbit period f (-y)) ?_
  · simpa only [integral_mul_const, mollifierKernel, (mollifierBump n).integral_normed, one_mul] using h
  apply Filter.Eventually.of_forall
  intro y
  rw [norm_smul, orbit_norm, Real.norm_eq_abs, abs_of_nonneg (mollifierKernel_nonneg n y)]
  exact le_rfl

theorem mollify_add (n : ℕ) (f g : LiftL2 period) :
    mollify period n (f + g) = mollify period n f + mollify period n g := by
  simp only [mollify_eq_integral, orbit, map_add, smul_add]
  exact integral_add (kernel_orbit_integrable period n f) (kernel_orbit_integrable period n g)

theorem mollify_smul (n : ℕ) (c : ℝ) (f : LiftL2 period) :
    mollify period n (c • f) = c • mollify period n f := by
  simp only [mollify_eq_integral, orbit, map_smul]
  simp_rw [smul_comm (mollifierKernel n _) c]
  exact integral_smul c _

/-- The actual linear averaging map associated with a smooth compact kernel. -/
def mollifierLinearMap (n : ℕ) : LiftL2 period →ₗ[ℝ] LiftL2 period where
  toFun := mollify period n
  map_add' := mollify_add period n
  map_smul' := mollify_smul period n

/-- The bounded L² approximate-identity operator, with operator norm at most one. -/
def mollifierOperator (n : ℕ) : LiftL2 period →L[ℝ] LiftL2 period :=
  (mollifierLinearMap period n).mkContinuous 1 (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)

theorem mollifierOperator_apply (n : ℕ) (f : LiftL2 period) :
    mollifierOperator period n f = mollify period n f := rfl

theorem mollifierOperator_norm_le (n : ℕ) : ‖mollifierOperator period n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    change ‖mollify period n f‖ ≤ 1 * ‖f‖
    simpa using mollify_norm_le period n f)

/-- The averaging operator commutes with every actual spatial or angular translation. -/
theorem mollify_translation (n : ℕ) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (mollify period n f) = mollify period n (translation period a f) := by
  rw [mollify_eq_integral, mollify_eq_integral]
  change (translation period a).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y)) = _
  rw [← (translation period a).toContinuousLinearMap.integral_comp_comm (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period a (translation period (euclideanCover period (-y)) f) = _
  rw [translation_add, translation_add, add_comm a]

/-- Smoothing produces actual strong Sobolev jets and commutes with every derivative word. -/
def mollifyJet {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) :
    SpatialJet period directions s (mollify period n f) :=
  EulerPressureJetIdentities.SpatialJet.map (mollifierOperator period n)
    (mollify_translation period n) J

theorem mollifyJet_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (n : ℕ) (w : Fin k → Fin 4) :
    (mollifyJet period J n).word w = mollify period n (J.word w) :=
  EulerPressureJetIdentities.SpatialJet.map_word J (mollifierOperator period n)
    (mollify_translation period n) w

/-- Every finite actual derivative word converges strongly under the same mollification. -/
theorem mollifyJet_word_tendsto {directions : Fin 4 → LiftTangent} {s k : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) (w : Fin k → Fin 4) :
    Filter.Tendsto (fun n => (mollifyJet period J n).word w) Filter.atTop (𝓝 (J.word w)) := by
  simp only [mollifyJet_word]
  exact mollify_tendsto period (J.word w)

theorem sub_word {directions : Fin 4 → LiftTangent} {s k : ℕ} {f g : LiftL2 period}
    (J : SpatialJet period directions s f) (K : SpatialJet period directions s g)
    (w : Fin k → Fin 4) : (J.sub K).word w = J.word w - K.word w := by
  induction s generalizing f g k with
  | zero => cases J; cases K; cases k <;> simp [SpatialJet.sub, SpatialJet.word]
  | succ s ih =>
    cases J with
    | succ df lower hd =>
      cases K with
      | succ dg lowerG hG =>
        cases k with
        | zero => simp
        | succ k =>
          simp only [SpatialJet.sub, SpatialJet.word_succ]
          exact ih (lower _) (lowerG _) _

/-- The same genuine mollifiers converge in every finite Sobolev jet norm. -/
theorem mollifyJet_sobolevNorm_tendsto {directions : Fin 4 → LiftTangent} {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period directions s f) :
    Filter.Tendsto (fun n => ((mollifyJet period J n).sub J).sobolevNorm) Filter.atTop (𝓝 0) := by
  have hword : ∀ k (w : Fin k → Fin 4), Filter.Tendsto
      (fun n => ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k w
    simpa using ((mollify_tendsto period (J.word w)).sub_const (J.word w)).norm
  have hlevel : ∀ k, Filter.Tendsto (fun n => ∑ w : Fin k → Fin 4,
      ‖mollify period n (J.word w) - J.word w‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    intro k
    simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin k → Fin 4))) (fun w _ => hword k w)
  have h := tendsto_finsetSum (s := Finset.range (s + 1)) (fun k _ => hlevel k)
  simpa only [SpatialJet.sobolevNorm_eq_sum_words, sub_word, mollifyJet_word, Finset.sum_const_zero] using h

/-- The smooth Hilbert-valued convolution is exactly the translation orbit of the mollified field. -/
theorem smoothOrbit_eq_orbit_mollify (n : ℕ) (f : LiftL2 period) (x : Domain 4) :
    smoothOrbit period n f x = orbit period (mollify period n f) x := by
  rw [orbit, mollify_eq_integral]
  change _ = (translation period (euclideanCover period x)).toContinuousLinearMap
    (∫ y : Domain 4, mollifierKernel n y • orbit period f (-y))
  rw [← (translation period (euclideanCover period x)).toContinuousLinearMap.integral_comp_comm
    (kernel_orbit_integrable period n f)]
  simp only [smoothOrbit, convolution_def, ContinuousLinearMap.lsmul_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [map_smul, orbit]
  change mollifierKernel n y • translation period (euclideanCover period (x - y)) f =
    mollifierKernel n y • translation period (euclideanCover period x)
      (translation period (euclideanCover period (-y)) f)
  rw [translation_add, ← euclideanCover_add, sub_eq_add_neg]

/-- Mollification produces C∞ vectors for the genuine L² translation representation. -/
theorem mollify_orbit_contDiff (n : ℕ) (f : LiftL2 period) :
    ContDiff ℝ ∞ (orbit period (mollify period n f)) := by
  have heq : orbit period (mollify period n f) = smoothOrbit period n f := by
    funext x
    exact (smoothOrbit_eq_orbit_mollify period n f x).symm
  rw [heq]
  exact smoothOrbit_contDiff period n f

/-- A single sequence of genuine mollifiers approximates every derivative order with
geometrically small errors once that order has entered the diagonal. -/
theorem mollify_diagonal_sequence {directions : Fin 4 → LiftTangent} {f : LiftL2 period}
    (J : ∀ s : ℕ, SpatialJet period directions s f) :
    ∃ index : ℕ → ℕ, (∀ n, n ≤ index n) ∧
      ∀ n s, s ≤ n → ((mollifyJet period (J s) (index n)).sub (J s)).sobolevNorm ≤ (1 / 2 : ℝ) ^ n := by
  have hex : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧
      ∀ s ≤ n, ((mollifyJet period (J s) k).sub (J s)).sobolevNorm ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    have hsum := tendsto_finsetSum (s := Finset.range (n + 1))
      (fun s _ => mollifyJet_sobolevNorm_tendsto period (J s))
    have heps : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have hsmall : ∀ᶠ k in Filter.atTop,
        (∑ s ∈ Finset.range (n + 1), ((mollifyJet period (J s) k).sub (J s)).sobolevNorm) <
          (1 / 2 : ℝ) ^ n := by
      have hsum0 : Filter.Tendsto (fun k => ∑ s ∈ Finset.range (n + 1),
          ((mollifyJet period (J s) k).sub (J s)).sobolevNorm) Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa only [Finset.sum_const_zero] using hsum
      exact hsum0.eventually (gt_mem_nhds heps)
    obtain ⟨k, hkn, hk⟩ := ((Filter.eventually_ge_atTop n).and hsmall).exists
    refine ⟨k, hkn, fun s hs => ?_⟩
    have hs' : s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (fun j _ => ((mollifyJet period (J j) k).sub (J j)).nonneg) hs').trans hk.le
  choose index hindex using hex
  exact ⟨index, fun n => (hindex n).1, fun n s hs => (hindex n).2 s hs⟩

end EulerCylinderMollifier

end

section

/-! Set integration as a bounded functional on L², and its commutation with Bochner averages. -/


namespace EulerSetIntegralL2

open MeasureTheory
open scoped ENNReal NNReal Topology

variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Integration on a finite-measure set as a genuine bounded linear map on L². -/
def setIntegralL2 (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) : Lp V 2 μ →L[ℝ] V :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2
    (indicatorConstLp 2 hs hμs (1 : ℝ))

theorem setIntegralL2_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp V 2 μ) : setIntegralL2 s hs hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x, s.indicator (fun y => f y) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    _ = _ := integral_indicator hs

/-- Bochner averaging of L² elements commutes with integration on every finite-measure set. -/
theorem setIntegral_integral_L2 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (F : Y → Lp V 2 μ) (hF : Integrable F ν) :
    (∫ x in s, (∫ y, F y ∂ν) x ∂μ) = ∫ y, ∫ x in s, F y x ∂μ ∂ν := by
  rw [← setIntegralL2_apply s hs hμs,
    ← (setIntegralL2 s hs hμs).integral_comp_comm hF]
  simp_rw [setIntegralL2_apply]

section Cylinder

open EulerLiftedGradientSpace EulerCylinderCoordinates EulerCylinderMollifier EulerSobolev

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_neg (y : Domain 4) : euclideanCover period (-y) = -euclideanCover period y := by
  simp [euclideanCover, coveringMap, map_neg]

/-- The Bochner L² mollifier and the classical convolution have the same iterated finite-set integrals. -/
theorem mollify_setIntegral (n : ℕ) (f : LiftL2 period) (s : Set (LiftDomain period))
    (hs : MeasurableSet s) (hμs : liftMeasure period s ≠ ⊤) :
    (∫ x in s, mollify period n f x ∂liftMeasure period) =
      ∫ y : Domain 4, ∫ x in s, mollifierKernel n y • f (x - euclideanCover period y)
        ∂liftMeasure period := by
  rw [mollify_eq_integral, setIntegral_integral_L2 s hs hμs _ (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (mollifierKernel n y) (orbit period f (-y))),
    ae_restrict_of_ae (translation_ae period (euclideanCover period (-y)) f)] with x hx hy
  rw [hx]
  change mollifierKernel n y • (translation period (euclideanCover period (-y)) f) x = _
  rw [hy, euclideanCover_neg, sub_eq_add_neg]

end Cylinder

end EulerSetIntegralL2

end

section

/-! Classical smooth cylinder representatives obtained by Euclidean mollification. -/

namespace EulerCoverMollification

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal Convolution Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
theorem euclideanCover_add (z w : Domain 4) :
    euclideanCover period (z+w) = euclideanCover period z + euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_add]

omit [Fact (0 < period)] in
theorem euclideanCover_sub (z w : Domain 4) :
    euclideanCover period (z-w) = euclideanCover period z - euclideanCover period w := by
  simp [euclideanCover, coveringMap, map_sub]

omit [Fact (0 < period)] in
theorem euclideanCover_surjective : Function.Surjective (euclideanCover period) := by
  intro x
  obtain ⟨v, hv⟩ := (coveringMap_isOpenQuotient period).surjective x
  refine ⟨coordinateEquiv.symm v, ?_⟩
  simpa only [euclideanCover, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hv

section Integrability
variable {F : Type*} [NormedAddCommGroup F]

/-- L² cylinder fields have locally integrable periodic lifts to the Euclidean covering space. -/
theorem locallyIntegrable_cover (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    LocallyIntegrable (f ∘ euclideanCover period) (volume : Measure (Domain 4)) := by
  intro x
  have hT : 0 < period := Fact.out
  let a : ℝ := x 0 - period/2
  have hsubset : Metric.ball x (period/4) ⊆ {z : Domain 4 | z 0 ∈ Set.Ioc a (a+period)} := by
    intro z hz
    have hd : ‖z-x‖ < period/4 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hc : |z 0-x 0| ≤ ‖z-x‖ := PiLp.norm_apply_le (z-x) 0
    have hh := abs_le.mp (hc.trans hd.le)
    change a < z 0 ∧ z 0 ≤ a+period
    dsimp [a]
    constructor <;> linarith
  have hmeasure : (volume : Measure (Domain 4)).restrict (Metric.ball x (period/4)) ≤ stripMeasure period a :=
    Measure.restrict_mono hsubset le_rfl
  have hb : MemLp (f ∘ euclideanCover period) 2
      ((volume : Measure (Domain 4)).restrict (Metric.ball x (period/4))) :=
    MemLp.mono_measure hmeasure (memLp_cover period f hf a)
  have : Fact ((volume : Measure (Domain 4)) (Metric.ball x (period/4)) < ⊤) := ⟨measure_ball_lt_top⟩
  exact ⟨Metric.ball x (period/4), Metric.ball_mem_nhds x (by positivity), hb.integrable (by norm_num)⟩

end Integrability

section Convolution
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Euclidean convolution of the periodic lift with a normalized compact bump. -/
noncomputable def coverConvolution (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) : Domain 4 → F :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f ∘ euclideanCover period)

/-- The same convolution defined directly on the cylinder, with the usual negative translation. -/
noncomputable def cylinderConvolution (φ : ContDiffBump (0 : Domain 4))
    (f : LiftDomain period → F) (x : LiftDomain period) : F :=
  ∫ y : Domain 4, φ.normed volume y • f (x - euclideanCover period y)

omit [Fact (0 < period)] [CompleteSpace F] in
theorem cylinderConvolution_cover (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (z : Domain 4) :
    cylinderConvolution period φ f (euclideanCover period z) = coverConvolution period φ f z := by
  rw [coverConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply, Function.comp_apply, euclideanCover_sub]

omit [CompleteSpace F] in
/-- The classical covering-space convolution is genuinely C∞. -/
theorem coverConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) : ContDiff ℝ ∞ (coverConvolution period φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))) (locallyIntegrable_cover period f hf)

omit [CompleteSpace F] in
/-- The convolution descends to a C∞ cylinder field in the actual local covering coordinates. -/
theorem cylinderConvolution_smooth (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F)
    (hf : MemLp f 2 (liftMeasure period)) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (cylinderConvolution period φ f) x) := by
  intro x
  obtain ⟨z, hz⟩ := euclideanCover_surjective period x
  have he : localFieldLift period (cylinderConvolution period φ f) x =
      fun v => coverConvolution period φ f (z + coordinateEquiv.symm v) := by
    funext v
    rw [← cylinderConvolution_cover, euclideanCover_add, hz]
    congr 1
  rw [he]
  exact (coverConvolution_smooth period φ f hf).comp (contDiff_const.add coordinateEquiv.symm.contDiff)

omit [Fact (0 < period)] [CompleteSpace F] in
/-- The covering-space convolution is periodic in the angular direction. -/
theorem coverConvolution_periodic (φ : ContDiffBump (0 : Domain 4)) (f : LiftDomain period → F) :
    Function.Periodic (coverConvolution period φ f) (EuclideanSpace.single 0 period) := by
  intro z
  rw [← cylinderConvolution_cover, ← cylinderConvolution_cover, euclideanCover_add]
  have hz : euclideanCover period (EuclideanSpace.single 0 period) = 0 := by
    apply Prod.ext
    · ext i
      simp [euclideanCover, coveringMap]
    · simp [euclideanCover, coveringMap]
  rw [hz, add_zero]

/-- Normalized shrinking bump convolutions recover the original covering-space function almost everywhere. -/
theorem ae_coverConvolution_tendsto {φ : ℕ → ContDiffBump (0 : Domain 4)}
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hshape : ∀ᶠ n in Filter.atTop, (φ n).rOut ≤ 2*(φ n).rIn)
    (f : LiftDomain period → F) (hf : MemLp f 2 (liftMeasure period)) :
    ∀ᵐ z ∂(volume : Measure (Domain 4)), Filter.Tendsto (fun n => coverConvolution period (φ n) f z)
      Filter.atTop (𝓝 (f (euclideanCover period z))) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hshape (locallyIntegrable_cover period f hf)

end Convolution
end EulerCoverMollification

end

section

/-! The finite-set Fubini bridge identifying classical and L² cylinder mollification. -/

namespace EulerCoverMollificationFubini

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCoverMollification EulerLiftedGradientSpace
open scoped ENNReal ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The elementary L²-to-L¹ bound on an arbitrary finite-measure set. -/
theorem finite_set_integral_norm_le (f : LiftDomain period → Vector3)
    (hf : MemLp f 2 (liftMeasure period)) (K : Set (LiftDomain period))
    (hK : liftMeasure period K < ⊤) :
    (∫ x in K, ‖f x‖ ∂liftMeasure period) ≤
      (eLpNorm f 2 (liftMeasure period)).toReal * (liftMeasure period K).toReal ^ (1/2 : ℝ) := by
  have hA := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (1 : ℝ≥0∞)) (q := 2)
    (by norm_num) (hf.restrict K).1
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one, Measure.restrict_apply_univ] at hA
  have hB : eLpNorm f 2 ((liftMeasure period).restrict K) * (liftMeasure period K)^(1/2 : ℝ) ≤
      eLpNorm f 2 (liftMeasure period) * (liftMeasure period K)^(1/2 : ℝ) :=
    mul_le_mul' (eLpNorm_mono_measure f (Measure.restrict_le_self (s := K))) le_rfl
  have hfin : eLpNorm f 2 (liftMeasure period) * (liftMeasure period K) ^ (1/2 : ℝ) ≠ ⊤ := by finiteness
  have hC := ENNReal.toReal_mono hfin (hA.trans hB)
  rw [integral_norm_eq_lintegral_enorm (hf.restrict K).1, ← eLpNorm_one_eq_lintegral_enorm]
  convert hC using 1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

omit [Fact (0 < period)] in
/-- The Euclidean covering map is continuous. -/
theorem euclideanCover_continuous : Continuous (euclideanCover period) :=
  (coveringMap_isOpenQuotient period).isQuotientMap.continuous.comp coordinateEquiv.continuous

/-- The convolution kernel is jointly integrable over the kernel variable and any finite cylinder set. -/
theorem kernel_integrable_prod (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    Integrable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1))
      ((volume : Measure (Domain 4)).prod ((liftMeasure period).restrict K)) := by
  have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
  have hmap : Measurable (fun p : Domain 4 × LiftDomain period => p.2 - euclideanCover period p.1) :=
    (continuous_snd.sub ((euclideanCover_continuous period).comp continuous_fst)).measurable
  have hsm : StronglyMeasurable (fun p : Domain 4 × LiftDomain period =>
      φ.normed volume p.1 • U (p.2 - euclideanCover period p.1)) :=
    ((φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable U).comp_measurable hmap)
  have hshift (y : Domain 4) : MemLp (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) := by
    convert! (Lp.memLp U).comp_measurePreserving
      (measurePreserving_translation period (-euclideanCover period y)) using 1
  apply (integrable_prod_iff hsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with y
    have hint : Integrable (fun x => U (x-euclideanCover period y)) ((liftMeasure period).restrict K) :=
      ((hshift y).restrict K).integrable (by norm_num)
    exact hint.smul (φ.normed volume y)
  · have hbound (y : Domain 4) : (∫ x in K, ‖φ.normed volume y • U (x - euclideanCover period y)‖ ∂liftMeasure period) ≤
        ‖φ.normed volume y‖ * (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ)) := by
      simp only [norm_smul, integral_const_mul]
      have he : eLpNorm (fun x => U (x - euclideanCover period y)) 2 (liftMeasure period) =
          eLpNorm U 2 (liftMeasure period) := by
        simpa only [Function.comp_def, sub_eq_add_neg] using
          eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) (Lp.aestronglyMeasurable U)
            (measurePreserving_translation period (-euclideanCover period y))
      have h := finite_set_integral_norm_le period _ (hshift y) K hK
      rw [he, ← Lp.norm_def] at h
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    exact (φ.integrable_normed.norm.mul_const (‖U‖ * (liftMeasure period K).toReal ^ (1/2 : ℝ))).mono'
      hsm.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
        exact hbound y))

/-- The classical cylinder convolution is integrable on each finite-measure set. -/
theorem cylinderConvolution_integrableOn (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    IntegrableOn (cylinderConvolution period φ U) K (liftMeasure period) := by
  exact (kernel_integrable_prod period φ U K hK).integral_prod_right

/-- Exact Fubini identity for every finite cylinder set. -/
theorem setIntegral_cylinderConvolution (φ : ContDiffBump (0 : Domain 4)) (U : LiftL2 period)
    (K : Set (LiftDomain period)) (hK : liftMeasure period K < ⊤) :
    (∫ x in K, cylinderConvolution period φ U x ∂liftMeasure period) =
      ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure period) := by
  have h := integral_integral_swap (f := fun (y : Domain 4) (x : LiftDomain period) =>
      φ.normed volume y • U (x-euclideanCover period y))
    (μ := (volume : Measure (Domain 4))) (ν := (liftMeasure period).restrict K)
    (kernel_integrable_prod period φ U K hK)
  change (∫ x in K, ∫ y : Domain 4, φ.normed volume y • U (x-euclideanCover period y) ∂volume ∂liftMeasure period) = _
  rw [← h]
  simp only [integral_smul]

/-- Equality of finite-set integrals identifies a Bochner L² mollifier with the classical smooth field. -/
theorem ae_eq_cylinderConvolution_of_setIntegrals (φ : ContDiffBump (0 : Domain 4)) (U V : LiftL2 period)
    (hV : ∀ K : Set (LiftDomain period), MeasurableSet K → liftMeasure period K < ⊤ →
      (∫ x in K, V x ∂liftMeasure period) =
        ∫ y : Domain 4, φ.normed volume y • (∫ x in K, U (x-euclideanCover period y) ∂liftMeasure period)) :
    (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] cylinderConvolution period φ U := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro K _ hK
    have : Fact (liftMeasure period K < ⊤) := ⟨hK⟩
    exact ((Lp.memLp V).restrict K).integrable (by norm_num)
  · intro K _ hK
    exact cylinderConvolution_integrableOn period φ U K hK
  · intro K hK hfin
    exact (hV K hK hfin).trans (setIntegral_cylinderConvolution period φ U K hfin).symm

end EulerCoverMollificationFubini

end

section

/-! Actual classical smooth representatives of the strong L² cylinder mollifiers. -/

namespace EulerMollifierRepresentative

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev
open EulerLiftedGradientSpace EulerMetricTransport EulerCoverMollification
open EulerCoverMollificationFubini EulerCylinderMollifier EulerSpatialSobolevInverse EulerStrongSmoothJet
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The concrete classical convolution representing the Bochner L² mollifier. -/
noncomputable def smoothMollifier (n : ℕ) (U : LiftL2 period) : LiftDomain period → Vector3 :=
  cylinderConvolution period (mollifierBump n) U

/-- The smooth convolution and the Bochner convolution are the same almost everywhere. -/
theorem mollify_ae_smoothMollifier (n : ℕ) (U : LiftL2 period) :
    (mollify period n U : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      smoothMollifier period n U := by
  apply ae_eq_cylinderConvolution_of_setIntegrals period (mollifierBump n) U (mollify period n U)
  intro K hK hfin
  simpa only [mollifierKernel, integral_smul] using
    EulerSetIntegralL2.mollify_setIntegral period n U K hK hfin.ne

/-- Every strong L² mollifier has an actual C∞ representative on the cylinder. -/
theorem smoothMollifier_smooth (n : ℕ) (U : LiftL2 period) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (smoothMollifier period n U) x) :=
  cylinderConvolution_smooth period (mollifierBump n) U (Lp.memLp U)

/-- Strong mollified jets are precisely the classical derivatives of the smooth convolution. -/
theorem smoothMollifier_word_ae {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    (mollify period n (J.word w) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (smoothMollifier period n U) := by
  rw [← mollifyJet_word period J n w]
  exact jet_word_ae period hk _ (mollifyJet period J n) w _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

/-- All available classical derivatives of the smooth mollifier are genuinely in L². -/
theorem smoothMollifier_word_memLp {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    MemLp (iteratedFieldDerivative period w (smoothMollifier period n U)) 2 (liftMeasure period) :=
  (Lp.memLp _).ae_eq (smoothMollifier_word_ae period hk U J n w)

/-- The strong and classical Sobolev norms of each mollifier agree exactly. -/
theorem smoothMollifier_sobolevNorm {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) :
    (mollifyJet period J n).sobolevNorm = liftSobolevNorm period s (smoothMollifier period n U) :=
  jet_sobolevNorm_eq period _ (mollifyJet period J n) _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

end EulerMollifierRepresentative

end

section

/-! Uniform control of every classical derivative word by actual strong Sobolev jets. -/


namespace EulerMollifierUniform

open MeasureTheory EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates EulerVectorCylinder
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerSpatialSobolevInverse
  EulerStrongSmoothJet EulerCylinderMollifier EulerMollifierRepresentative
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- An arbitrary derivative word has H³ norm controlled by the full norm three orders higher. -/
theorem word_H3_le_higher {m : ℕ} (w : Fin m → Fin 4) (f : LiftDomain period → Vector3) :
    liftSobolevNorm period 3 (iteratedFieldDerivative period w f) ≤
      85 * liftSobolevNorm period (m + 3) f := by
  have hA : (∑ n ∈ Finset.range (3+1), ∑ v : Fin n → Fin 4,
      (eLpNorm (iteratedFieldDerivative period v (iteratedFieldDerivative period w f)) 2
        (liftMeasure period)).toReal) ≤
      ∑ n ∈ Finset.range (3+1), ∑ _v : Fin n → Fin 4, liftSobolevNorm period (m + 3) f := by
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨u, hu⟩ := iteratedFieldDerivative_comp_exists period v w f
    rw [hu]
    exact word_L2_le_liftSobolevNorm period (by have := Finset.mem_range.1 hn; omega) u f
  apply hA.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  norm_num [Finset.sum_range_succ]
  ring

/-- Every actual smooth derivative word is uniformly controlled by its genuine strong jet. -/
theorem jet_word_pointwise_bound {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (f : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * J.sobolevNorm) := by
  have hLp : ∀ j ≤ m + 3, ∀ u : Fin j → Fin 4,
      MemLp (iteratedFieldDerivative period u f) 2 (liftMeasure period) :=
    fun j hj u => jet_classical_memLp period hj U J u f hrep hf
  have hA := vector_cylinder_pointwise_le_H3 period 3 (iteratedFieldDerivative period w f)
    (iteratedFieldDerivative_smooth period w f hf)
    (fun j hj v => word_memLp period (by omega : m+j ≤ m+3) v w f hLp) x
  have hB := word_H3_le_higher period w f
  rw [← jet_sobolevNorm_eq period U J f hrep hf] at hB
  exact hA.trans (mul_le_mul_of_nonneg_left hB
    (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)))

omit [Fact (0 < period)] in
theorem fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    fieldDerivative period a (fun y => f y - g y) x =
      fieldDerivative period a f x - fieldDerivative period a g x := by
  have h := ((((hf x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)).sub
    (((hg x).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0))).fderiv
  have h' := congrArg (fun L : LiftTangent →L[ℝ] Vector3 => L a) h
  simpa +unfoldPartialApp [fieldDerivative, localFieldLift, Pi.sub_def] using h'

omit [Fact (0 < period)] in
theorem word_sub {m : ℕ} (w : Fin m → Fin 4) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    iteratedFieldDerivative period w (fun y => f y - g y) =
      fun x => iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedFieldDerivative_succ, ih (Fin.tail w)]
    funext x
    exact fieldDerivative_sub period (standardDirection (w 0)) _ _
      (iteratedFieldDerivative_smooth period (Fin.tail w) f hf)
      (iteratedFieldDerivative_smooth period (Fin.tail w) g hg) x

/-- Uniform derivative differences are controlled by the actual L² Sobolev difference jet. -/
theorem jet_word_difference_bound {m : ℕ} (U V : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U)
    (K : SpatialJet period standardDirection (m + 3) V) (w : Fin m → Fin 4)
    (f g : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hrepG : (V : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    ‖iteratedFieldDerivative period w f x - iteratedFieldDerivative period w g x‖ ≤
      (3 * cylinderEmbeddingConstant period) * (85 * (J.sub K).sobolevNorm) := by
  have hrepD : ((U - V : LiftL2 period) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      fun x => f x - g x := by
    filter_upwards [Lp.coeFn_sub U V, hrep, hrepG] with y hy hfy hgy
    simpa [hfy, hgy] using hy
  have h := jet_word_pointwise_bound period (U - V) (J.sub K) w (fun x => f x - g x)
    hrepD (fun x => (hf x).sub (hg x)) x
  simpa only [word_sub period w f g hf hg] using h

/-- A genuine Sobolev difference is bounded through any third jet at the same order. -/
theorem jet_sub_triangle {s : ℕ} {U V W : LiftL2 period}
    (J : SpatialJet period standardDirection s U) (K : SpatialJet period standardDirection s V)
    (L : SpatialJet period standardDirection s W) :
    (J.sub K).sobolevNorm ≤ (J.sub L).sobolevNorm + (K.sub L).sobolevNorm := by
  simp only [SpatialJet.sobolevNorm_eq_sum_words, sub_word]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  calc
    ‖J.word w - K.word w‖ = ‖(J.word w - L.word w) + (L.word w - K.word w)‖ := by congr 1; abel
    _ ≤ ‖J.word w - L.word w‖ + ‖L.word w - K.word w‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (L.word w) (K.word w)]

/-- Every actual classical derivative word of the mollifiers is uniformly Cauchy. -/
theorem smoothMollifier_word_uniformCauchy {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    UniformCauchySeqOn (fun n x => iteratedFieldDerivative period w (smoothMollifier period n U) x)
      Filter.atTop Set.univ := by
  let C : ℝ := (3 * cylinderEmbeddingConstant period) * 85
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (cylinderEmbeddingConstant_nonneg period)) (by norm_num)
  have hlim : Filter.Tendsto (fun n => C * ((mollifyJet period J n).sub J).sobolevNorm)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (mollifyJet_sobolevNorm_tendsto period J).const_mul C
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, fun a ha b hb x _ => ?_⟩
  have hab := jet_word_difference_bound period (mollify period a U) (mollify period b U)
    (mollifyJet period J a) (mollifyJet period J b) w
    (smoothMollifier period a U) (smoothMollifier period b U)
    (mollify_ae_smoothMollifier period a U) (mollify_ae_smoothMollifier period b U)
    (smoothMollifier_smooth period a U) (smoothMollifier_smooth period b U) x
  have htri := jet_sub_triangle period (mollifyJet period J a) (mollifyJet period J b) J
  have hna := hN a ha
  have hnb := hN b hb
  calc
    _ = ‖iteratedFieldDerivative period w (smoothMollifier period a U) x -
        iteratedFieldDerivative period w (smoothMollifier period b U) x‖ := dist_eq_norm _ _
    _ ≤ (3 * cylinderEmbeddingConstant period) *
        (85 * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm) := hab
    _ = C * ((mollifyJet period J a).sub (mollifyJet period J b)).sobolevNorm := by dsimp [C]; ring
    _ ≤ C * (((mollifyJet period J a).sub J).sobolevNorm +
        ((mollifyJet period J b).sub J).sobolevNorm) := mul_le_mul_of_nonneg_left htri hC
    _ < ε := by linarith

/-- Completeness produces a uniform limit for every actual derivative word. -/
theorem exists_smoothMollifier_word_uniform_limit {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4) :
    ∃ g : LiftDomain period → Vector3,
      TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n U))
        g Filter.atTop := by
  have hC := smoothMollifier_word_uniformCauchy period U J w
  have hex : ∀ x : LiftDomain period, ∃ v : Vector3,
      Filter.Tendsto (fun n => iteratedFieldDerivative period w (smoothMollifier period n U) x)
        Filter.atTop (𝓝 v) := fun x => cauchySeq_tendsto_of_complete (hC.cauchySeq (Set.mem_univ x))
  choose g hg using hex
  exact ⟨g, tendstoUniformlyOn_univ.mp (hC.tendstoUniformlyOn_of_tendsto (fun x _ => hg x))⟩

/-- The uniform classical word limit represents the actual strong L² derivative word. -/
theorem smoothMollifier_word_limit_ae {m : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection (m + 3) U) (w : Fin m → Fin 4)
    (g : LiftDomain period → Vector3)
    (hlim : TendstoUniformly (fun n => iteratedFieldDerivative period w (smoothMollifier period n U))
      g Filter.atTop) : (J.word w : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  obtain ⟨index, hindex, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (mollify_tendsto period (J.word w))).exists_seq_tendsto_ae'
  have hrep : ∀ᵐ x ∂liftMeasure period, ∀ n : ℕ,
      mollify period (index n) (J.word w) x =
        iteratedFieldDerivative period w (smoothMollifier period (index n) U) x :=
    ae_all_iff.mpr (fun n => smoothMollifier_word_ae period (by omega) U J (index n) w)
  filter_upwards [hsub, hrep] with x hx hxr
  have heq : (fun n => mollify period (index n) (J.word w) x) =
      fun n => iteratedFieldDerivative period w (smoothMollifier period (index n) U) x := funext hxr
  rw [heq] at hx
  exact tendsto_nhds_unique hx ((hlim.tendsto_at x).comp hindex)

/-- Strong H³ cylinder jets have genuine continuous representatives. -/
theorem exists_continuous_representative (U : LiftL2 period)
    (J : SpatialJet period standardDirection 3 U) :
    ∃ g : LiftDomain period → Vector3, Continuous g ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U J w
  refine ⟨g, ?_, ?_⟩
  · apply hg.continuous
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall fun n =>
      smoothField_continuous period _ (smoothMollifier_smooth period n U)
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U J w g hg

end EulerMollifierUniform

end

section

/-! Full Fréchet tensor convergence from the genuine cylinder derivative words. -/

namespace EulerMollifierTensors

open MeasureTheory Filter EulerSobolev EulerCylinderSobolev EulerCylinderCoordinates
open EulerLiftedGradientSpace EulerMetricTransport EulerSobolevDerivativeNorm
open scoped ContDiff Topology

variable (period : ℝ)

/-- The operator norm of a difference of derivative tensors is controlled by the finite coordinate sum. -/
theorem tensor_difference_le_word_sum (m : ℕ) (f g : LiftDomain period → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (x : LiftDomain period) (z : Domain 4) :
    ‖iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z‖ ≤
    ∑ w : Fin m → Fin 4,
      ‖iteratedFieldDerivative period w f (euclideanCover period z + x) -
        iteratedFieldDerivative period w g (euclideanCover period z + x)‖ := by
  have h := multilinear_norm_le_coordinate_sum 4 m
    (iteratedFDeriv ℝ m (euclideanLift period f x) z -
      iteratedFDeriv ℝ m (euclideanLift period g x) z)
  simpa only [sub_apply,
    ← euclideanLift_iteratedFieldDerivative period _ f hf,
    ← euclideanLift_iteratedFieldDerivative period _ g hg,
    euclideanLift_eq_translated_cover, translated] using h

/-- Uniform Cauchy convergence of every coordinate word gives uniform Cauchy convergence of the full tensor. -/
theorem tensor_uniformCauchy_of_words (m : ℕ) (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ w : Fin m → Fin 4,
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (x : LiftDomain period) :
    UniformCauchySeqOn
      (fun k => iteratedFDeriv ℝ m (euclideanLift period (f k) x)) atTop Set.univ := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hc : 0 < (4 : ℝ)^m := pow_pos (by norm_num) _
  have hsmall := fun w : Fin m → Fin 4 =>
    Metric.uniformCauchySeqOn_iff.mp (hC w) (ε / (4 : ℝ)^m) (div_pos hε hc)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N, ?_⟩
  intro k hk l hl z _
  have hword (w : Fin m → Fin 4) :
      ‖iteratedFieldDerivative period w (f k) (euclideanCover period z + x) -
        iteratedFieldDerivative period w (f l) (euclideanCover period z + x)‖ < ε / (4 : ℝ)^m := by
    simpa only [dist_eq_norm] using hN w k
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hk) l
      ((Finset.le_sup (f := N) (Finset.mem_univ w)).trans hl)
      (euclideanCover period z + x) (Set.mem_univ _)
  rw [dist_eq_norm]
  apply (tensor_difference_le_word_sum period m (f k) (f l) (hf k) (hf l) x z).trans_lt
  calc
    _ < ∑ _w : Fin m → Fin 4, ε / (4 : ℝ)^m := by
      apply Finset.sum_lt_sum (fun w _ => (hword w).le)
      exact ⟨fun _ => 0, Finset.mem_univ _, hword _⟩
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      exact mul_div_cancel₀ ε hc.ne'

end EulerMollifierTensors

end

section

/-! Smoothness of uniform limits of complete Fréchet derivative towers. -/

namespace EulerSmoothTensorLimit

open Filter
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A uniformly Cauchy sequence at every actual Fréchet derivative order has a genuine smooth limit. -/
theorem exists_smooth_limit (f : ℕ → E → F) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hC : ∀ m, UniformCauchySeqOn (fun k => iteratedFDeriv ℝ m (f k)) atTop Set.univ) :
    ∃ g : E → F, TendstoUniformly f g atTop ∧ ContDiff ℝ ∞ g := by
  let L (m : ℕ) : (E [×(m+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×m]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (m k : ℕ) (x : E) : HasFDerivAt (iteratedFDeriv ℝ m (f k))
      (L m (iteratedFDeriv ℝ (m+1) (f k) x)) x := by
    have hd := (hf k).differentiable_iteratedFDeriv
      (show (m : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top m) x
    exact hd.hasFDerivAt
  obtain ⟨J, hJ, hJs⟩ := EulerSmoothUniformLimit.exists_smooth_limit_of_uniform_cauchy_tower
    (fun m k => iteratedFDeriv ℝ m (f k)) L hD hC
  let A := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun x => A (J 0 x), ?_, A.contDiff.comp (hJs 0)⟩
  have h := A.uniformContinuous.comp_tendstoUniformly (hJ 0)
  simpa only [A, Function.comp_def, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] using h

section Cylinder

open EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev EulerLiftedGradientSpace
open EulerMetricTransport EulerMollifierTensors

/-- A pointwise cylinder limit is C∞ when every coordinate derivative word is uniformly Cauchy. -/
theorem cylinder_smooth_of_uniformCauchy_words (period : ℝ)
    (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ m (w : Fin m → Fin 4),
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (g : LiftDomain period → Vector3)
    (hpoint : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := by
  intro x
  obtain ⟨G, hG, hGs⟩ := exists_smooth_limit
    (fun k => euclideanLift period (f k) x)
    (fun k => euclideanLift_smooth period (f k) (hf k) x)
    (fun m => tensor_uniformCauchy_of_words period m f hf (hC m) x)
  have he : euclideanLift period g x = G := by
    funext z
    have hp : Tendsto (fun k => euclideanLift period (f k) x z) atTop
        (𝓝 (euclideanLift period g x z)) := by
      simpa only [euclideanLift_eq_translated_cover, translated] using
        hpoint (euclideanCover period z + x)
    exact tendsto_nhds_unique hp (hG.tendsto_at z)
  have hlocal : localFieldLift period g x = G ∘ coordinateEquiv.symm := by
    rw [← he]
    funext v
    simp only [euclideanLift, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hlocal]
  exact hGs.comp coordinateEquiv.symm.contDiff

end Cylinder

end EulerSmoothTensorLimit

end

section

/-! Actual C∞ representatives obtained from all-order strong cylinder jets. -/


namespace EulerSmoothPressureRepresentative

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMollifierRepresentative EulerMollifierUniform
open scoped ContDiff Topology

variable (period : ℝ) [Fact (0 < period)]

/-- All-order strong cylinder jets produce an actual C∞ representative of the L² field. -/
theorem exists_smooth_representative (U : LiftL2 period)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s U) :
    ∃ g : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) ∧
      (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g := by
  let w : Fin 0 → Fin 4 := Fin.elim0
  obtain ⟨g, hg⟩ := exists_smoothMollifier_word_uniform_limit period U (J 3) w
  have hpoint : ∀ x, Filter.Tendsto (fun n => smoothMollifier period n U x)
      Filter.atTop (𝓝 (g x)) := fun x => hg.tendsto_at x
  have hC : ∀ m (v : Fin m → Fin 4), UniformCauchySeqOn
      (fun n => iteratedFieldDerivative period v (smoothMollifier period n U)) Filter.atTop Set.univ :=
    fun m v => smoothMollifier_word_uniformCauchy period U (J (m + 3)) v
  refine ⟨g, ?_, ?_⟩
  · exact EulerSmoothTensorLimit.cylinder_smooth_of_uniformCauchy_words period
      (fun n => smoothMollifier period n U) (fun n => smoothMollifier_smooth period n U) hC g hpoint
  · simpa only [SpatialJet.word_zero] using smoothMollifier_word_limit_ae period U (J 3) w g hg

/-- The genuine coercive pressure inverse has a C∞ representative when its actual coefficients
and forcing possess strong derivative jets at every finite order. -/
theorem exists_smooth_pressure (A : SmoothCoefficient period) (f : LiftL2 period)
    (K : ∀ s : ℕ, CoefficientJet period standardDirection s A)
    (J : ∀ s : ℕ, SpatialJet period standardDirection s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A.coefficient x v) v) :
    ∃ p : LiftDomain period → Vector3,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period p x)) ∧
      (A.pressure κ m c hc hpos f : LiftDomain period → Vector3) =ᵐ[liftMeasure period] p :=
  exists_smooth_representative period (A.pressure κ m c hc hpos f)
    (fun s => (J s).solvePressure (K s) κ m c hc hpos)

end EulerSmoothPressureRepresentative

end

section

open Set MeasureTheory

namespace EulerTerminalEnergy

open InnerProductSpace

theorem integral_sq_le_length_mul (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ t in a..b, g t) / (b - a)
  have hgi := hg.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hgs := (hg.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  change IntervalIntegrable (fun t => (g t) ^ 2) volume a b at hgs
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (fun t _ => sq_nonneg (g t - c))
  have hex : (fun t => (g t - c) ^ 2) =
      (fun t => (g t) ^ 2 - 2 * c * g t + c ^ 2) := by
    funext t
    ring
  rw [hex, intervalIntegral.integral_add (hgs.sub (hgi.const_mul (2 * c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hgs (hgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hc : c * (b - a) = ∫ t in a..b, g t := div_mul_cancel₀ _ hlen.ne'
  have := mul_nonneg hlen.le hn
  nlinarith [sq_nonneg ((b - a) * c - ∫ t in a..b, g t)]

theorem norm_integral_sq_le_length_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ‖∫ t in a..b, g t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) hab
  have hq := integral_sq_le_length_mul (fun t => ‖g t‖) hab hg.norm
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hq

theorem terminal_trace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S t : ℝ} (ht : t ≤ S)
    (hv : ContinuousOn v (Icc t S))
    (hη : ∀ s ∈ Icc t S, HasDerivAt η (v s) s) (hS : η S = 0) :
    ‖η t‖ ^ 2 ≤ (S - t) * ∫ s in t..S, ‖v s‖ ^ 2 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hη s ((uIcc_of_le ht) ▸ hs))
    (hv.intervalIntegrable_of_Icc ht)
  have hn := norm_integral_sq_le_length_mul v ht hv
  simpa only [he, hS, zero_sub, norm_neg] using hn

theorem terminal_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S : ℝ} (hS0 : 0 ≤ S)
    (hv : ContinuousOn v (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0) :
    (∫ t in 0..S, ‖η t‖ ^ 2) ≤ S ^ 2 / 2 * ∫ t in 0..S, ‖v t‖ ^ 2 := by
  let energy := ∫ t in 0..S, ‖v t‖ ^ 2
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hp : ∀ t ∈ Icc 0 S, ‖η t‖ ^ 2 ≤ (S - t) * energy := by
    intro t ht
    have hsub : Icc t S ⊆ Icc 0 S := Icc_subset_Icc_left ht.1
    have htrace := terminal_trace η v ht.2 (hv.mono hsub)
      (fun s hs => hη s (hsub hs)) hS
    have hi := intervalIntegral.integral_mono_interval (μ := volume)
      ht.1 ht.2 (le_refl S) (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) hvi
    exact htrace.trans (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hS0
    ((hηc.norm.pow 2).intervalIntegrable_of_Icc hS0)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable
      (a := 0) (b := S)) hp
  have he : (∫ t in 0..S, (S - t) * energy) = S ^ 2 / 2 * energy := by
    have hic : IntervalIntegrable (fun _ : ℝ => S) volume 0 S := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 S :=
      continuous_id.intervalIntegrable 0 S
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub hic hid,
      intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  exact hm.trans_eq he

theorem localized_boundary_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M A R : E →L[ℝ] E) (Be Bc C₁ C₂ r L : ℝ)
    (hBc : 0 ≤ Bc) (hC : 0 ≤ L - Bc * C₁)
    (hA : ∀ z, 0 ≤ ⟪A z, z⟫_ℝ)
    (hM : ∀ z, -Be * ‖z‖ ^ 2 - Bc * ‖R z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ)
    (hR : ∀ z, ‖R z‖ ^ 2 ≤ C₁ * ⟪A z, z⟫_ℝ + C₂ * r ^ 3 * ‖z‖ ^ 2)
    (z : E) :
    -(Be + C₂ * Bc * r ^ 3) * ‖z‖ ^ 2 ≤
      ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ := by
  have h1 := mul_le_mul_of_nonneg_left (hR z) hBc
  have h2 := mul_nonneg hC (hA z)
  nlinarith [hM z]

theorem mean_form_coercive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (η v : ℝ → E) (H : ℝ → E →L[ℝ] E) (M A : E →L[ℝ] E)
    (S K B L : ℝ) (hS0 : 0 ≤ S) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hsmall : K * S ^ 2 / 2 + B * S ≤ 1 / 2)
    (hv : ContinuousOn v (Icc 0 S)) (hH : ContinuousOn H (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0)
    (hpot : ∀ t ∈ Icc 0 S, ∀ z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
    (hboundary : ∀ z, -B * ‖z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ) :
    (∫ t in 0..S, ‖v t‖ ^ 2) / 2 ≤
      (∫ t in 0..S, ‖v t‖ ^ 2 - ⟪H t (η t), η t⟫_ℝ) +
        ⟪M (η 0), η 0⟫_ℝ + L * ⟪A (η 0), η 0⟫_ℝ := by
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηi : IntervalIntegrable (fun t => ‖η t‖ ^ 2) volume 0 S :=
    (hηc.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hHi : IntervalIntegrable (fun t => ⟪H t (η t), η t⟫_ℝ) volume 0 S :=
    ((hH.clm_apply hηc).inner hηc).intervalIntegrable_of_Icc hS0
  have hip := intervalIntegral.integral_mono_on hS0 hHi (hηi.const_mul K)
    (fun t ht => hpot t ht (η t))
  rw [intervalIntegral.integral_const_mul] at hip
  have htrace := terminal_trace η v hS0 hv hη hS
  simp only [sub_zero] at htrace
  have hpoin := terminal_poincare η v hS0 hv hη hS
  have h1 := mul_le_mul_of_nonneg_left hpoin hK
  have h2 := mul_le_mul_of_nonneg_left htrace hB
  have he : 0 ≤ ∫ t in 0..S, ‖v t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hS0 (fun t _ => sq_nonneg ‖v t‖)
  have h3 := mul_le_mul_of_nonneg_right hsmall he
  rw [intervalIntegral.integral_sub hvi hHi]
  nlinarith [hboundary (η 0)]

end EulerTerminalEnergy

end

section

namespace EulerIntervalTrace

open Set MeasureTheory EulerTerminalEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_sub_sq_le_interval_energy (f v : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ^ 2 ≤ (b - a) * ∫ r in a..b, ‖v r‖ ^ 2 := by
  have hvi : IntervalIntegrable (fun r => ‖v r‖ ^ 2) volume a b :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hab
  have hpos : 0 ≤ ∫ r in a..b, ‖v r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun r _ => sq_nonneg _)
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (le_of_lt (lt_of_not_ge hst))
    simpa only [norm_sub_rev] using h
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hf r (hsub ((uIcc_of_le hst) ▸ hr)))
    ((hv.mono hsub).intervalIntegrable_of_Icc hst)
  have hq := norm_integral_sq_le_length_mul v hst (hv.mono hsub)
  rw [he] at hq
  have hi := intervalIntegral.integral_mono_interval hs.1 hst ht.2
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖v r‖)) hvi
  exact hq.trans ((mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hst)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2] : t - s ≤ b - a) hpos))

/-- Point evaluation on an interval is bounded by the actual zeroth and first derivative energies. -/
theorem pointwise_H1_trace (f v : ℝ → E) (a b : ℝ) (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ 2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfi := (hc.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  let V := ∫ s in a..b, ‖v s‖ ^ 2
  have hp (s : ℝ) (hs : s ∈ Icc a b) :
      ‖f t‖ ^ 2 ≤ 2 * ‖f s‖ ^ 2 + 2 * (b - a) * V := by
    have hd := norm_sub_sq_le_interval_energy f v a b hab.le hv hf s t hs ht
    have hn : ‖f t‖ ≤ ‖f t - f s‖ + ‖f s‖ := by
      calc
        _ = ‖(f t - f s) + f s‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp [V]
    nlinarith [norm_nonneg (f t), norm_nonneg (f s), norm_nonneg (f t - f s),
      sq_nonneg (‖f t - f s‖ - ‖f s‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (intervalIntegrable_const (c := ‖f t‖ ^ 2))
    ((hfi.const_mul 2).add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hfi.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hlen : 0 < b - a := sub_pos.mpr hab
  apply (mul_le_mul_iff_right₀ hlen).mp
  dsimp [V] at hi ⊢
  have he : (b - a) * (2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) =
      2 * (∫ s in a..b, ‖f s‖ ^ 2) + (b - a) *
        (2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) := by
    field_simp [hlen.ne']
  rw [he]
  exact hi

end EulerIntervalTrace

end

section

/-! Quantitative endpoint selection in the activation step, equations (26)–(27). -/

namespace EulerDNSelection

open InnerProductSpace

theorem positive_cross_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ : E →L[ℝ] E) (hΛ : Λ.IsPositive) (p q : E) :
    ⟪Λ p, q⟫_ℝ ^ 2 ≤ ⟪Λ p, p⟫_ℝ * ⟪Λ q, q⟫_ℝ := by
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  have hquad : ∀ t : ℝ, 0 ≤ ⟪Λ p, p⟫_ℝ * (t * t) +
      (2 * ⟪Λ p, q⟫_ℝ) * t + ⟪Λ q, q⟫_ℝ := by
    intro t
    have ht := hΛ.inner_nonneg_left (t • p + q)
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hsym] at ht
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- A positive semidefinite endpoint matrix, perturbed by a unit shear and a small
matrix with negative first diagonal entry, allows the required polarized output. -/
theorem select_endpoint
    (C ε a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C) (hbC : |b| ≤ C)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε)
    (hpq : |cpq| ≤ ε) (hqp : |cqp| ≤ ε) (hqq : |cqq| ≤ ε) :
    ∃ yp yq : ℝ,
      (b - 1 - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) := by
  have hεsmall : ε ≤ 1 / 16 := by
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) hε]
  have hu : 0 < a - cpp := by linarith
  have huC : a - cpp ≤ C + ε := by
    have := (abs_le.mp hppε).1
    linarith
  rcases le_or_gt b (1 / 2) with hb | hb
  · let D := 1 + cqp - b
    have hD : 1 / 3 ≤ D := by
      have := (abs_le.mp hqp).1
      dsimp [D]
      linarith
    have hDpos : 0 < D := by linarith
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hquot : (a - cpp) / D ≤ 8 * (C + 1) := by
      apply (div_le_iff₀ hDpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ D - 1 / 3 by linarith)]
    have hinv : 1 / D ≤ 3 := (div_le_iff₀ hDpos).2 (by linarith)
    refine ⟨-1 / D, 0, ?_, ?_, ?_, ?_⟩
    · have heq : b - 1 - cqp = -D := by dsimp [D]; ring
      rw [heq, mul_zero, add_zero]
      field_simp
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -(a - cpp) / D := by ring
      rw [heq, neg_div]
      linarith
    · have heq : (a - cpp) * (-1 / D) + (b - cpq) * 0 = -((a - cpp) / D) := by ring
      rw [heq]
      exact neg_nonpos.mpr (div_nonneg hu.le hDpos.le)
    · simp only [abs_zero, add_zero, abs_div, abs_neg, abs_one, abs_of_pos hDpos]
      linarith
  · let Δ := (a - cpp) * (d - cqq) - (b - 1 - cqp) * (b - cpq)
    have hbpos : 0 ≤ b := by linarith
    have hb_bound : b ≤ C := (abs_le.mp hbC).2
    have hud : b ^ 2 ≤ (a - cpp) * d := by
      nlinarith [mul_nonneg (show 0 ≤ -cpp by linarith) hd]
    have hucqq : (a - cpp) * cqq ≤ (C + ε) * ε :=
      (mul_le_mul_of_nonneg_left (abs_le.mp hqq).2 hu.le).trans
        (mul_le_mul_of_nonneg_right huC hε)
    have hbpq : -(C * ε) ≤ b * cpq := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hpq).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hbqp : -(C * ε) ≤ b * cqp := by
      have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp hqp).1 hbpos
      have h₂ := mul_le_mul_of_nonneg_right hb_bound hε
      nlinarith
    have hprod : cqp * cpq ≤ ε ^ 2 := by
      calc
        cqp * cpq ≤ |cqp * cpq| := le_abs_self _
        _ = |cqp| * |cpq| := abs_mul _ _
        _ ≤ ε * ε := mul_le_mul hqp hpq (abs_nonneg _) hε
        _ = ε ^ 2 := by ring
    have hΔ : 1 / 4 ≤ Δ := by
      have hpq_upper := (abs_le.mp hpq).2
      have hεsq : ε ^ 2 ≤ ε := by nlinarith
      dsimp [Δ]
      nlinarith
    have hΔpos : 0 < Δ := by linarith
    have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
    have hnum : |b - cpq| ≤ C + ε :=
      (abs_sub b cpq).trans (add_le_add hbC hpq)
    have huabs : |a - cpp| ≤ C + ε := by rwa [abs_of_pos hu]
    have hnorm : |-(b - cpq) / Δ| + |(a - cpp) / Δ| ≤ 8 * (C + 1) := by
      rw [abs_div, abs_div, abs_neg, abs_of_pos hΔpos, ← add_div]
      apply (div_le_iff₀ hΔpos).2
      nlinarith [mul_nonneg (show 0 ≤ C + 1 by linarith)
        (show 0 ≤ Δ - 1 / 4 by linarith)]
    refine ⟨-(b - cpq) / Δ, (a - cpp) / Δ, ?_, ?_, ?_, hnorm⟩
    · field_simp [hΔne]
      dsimp [Δ]
      ring
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]
      linarith
    · have heq : (a - cpp) * (-(b - cpq) / Δ) +
          (b - cpq) * ((a - cpp) / Δ) = 0 := by ring
      rw [heq]

/-- The endpoint choice at an arbitrary positive shear scale `h`. -/
theorem select_endpoint_scaled
    (C ε h a b d cpp cpq cqp cqq : ℝ)
    (hC : 1 ≤ C) (hε : 0 ≤ ε) (hsmall : 16 * (C + 1) * ε ≤ 1)
    (hh : 0 < h) (ha : 0 ≤ a) (had : b ^ 2 ≤ a * d) (hd : 0 ≤ d)
    (haC : a ≤ C * h) (hbC : |b| ≤ C * h)
    (hpp : cpp < 0) (hppε : |cpp| ≤ ε * h)
    (hpq : |cpq| ≤ ε * h) (hqp : |cqp| ≤ ε * h) (hqq : |cqq| ≤ ε * h) :
    ∃ yp yq : ℝ,
      (b - h - cqp) * yp + (d - cqq) * yq = 1 ∧
      -8 * (C + 1) ≤ (a - cpp) * yp + (b - cpq) * yq ∧
      (a - cpp) * yp + (b - cpq) * yq ≤ 0 ∧
      |yp| + |yq| ≤ 8 * (C + 1) / h := by
  have habs (x R : ℝ) (hx : |x| ≤ R * h) : |x / h| ≤ R := by
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).2 hx
  have hpsd : (b / h) ^ 2 ≤ (a / h) * (d / h) := by
    rw [div_pow, div_mul_div_comm, ← pow_two]
    exact div_le_div_of_nonneg_right had (sq_nonneg h)
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint C ε
    (a / h) (b / h) (d / h) (cpp / h) (cpq / h) (cqp / h) (cqq / h)
    hC hε hsmall (div_nonneg ha hh.le) hpsd (div_nonneg hd hh.le)
    ((div_le_iff₀ hh).2 haC) (habs b C hbC)
    (div_neg_of_neg_of_pos hpp hh) (habs cpp ε hppε)
    (habs cpq ε hpq) (habs cqp ε hqp) (habs cqq ε hqq)
  have heqp : (a - cpp) * (yp / h) + (b - cpq) * (yq / h) =
      (a / h - cpp / h) * yp + (b / h - cpq / h) * yq := by ring
  have heqq : (b - h - cqp) * (yp / h) + (d - cqq) * (yq / h) =
      (b / h - 1 - cqp / h) * yp + (d / h - cqq / h) * yq := by
    field_simp
  refine ⟨yp / h, yq / h, heqq.trans hwq, heqp ▸ hwpl, heqp ▸ hwpu, ?_⟩
  rw [abs_div, abs_div, abs_of_pos hh, ← add_div]
  exact div_le_div_of_nonneg_right hnorm hh.le

theorem select_endpoint_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (Λ B : E →L[ℝ] E) (p q : E)
    (C ε h : ℝ) (hΛ : Λ.IsPositive) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ⟪p, q⟫_ℝ = 0) (hC : 1 ≤ C) (hε : 0 ≤ ε) (hh : 0 < h)
    (hsmall : 16 * (C + 1) * ε ≤ 1) (hΛbound : ‖Λ‖ ≤ C * h)
    (hBbound : ‖B‖ ≤ ε * h) (hBpp : ⟪B p, p⟫_ℝ < 0) :
    ∃ yp yq : ℝ, let Y := yp • p + yq • q
      let w := Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q
      ⟪w, q⟫_ℝ = 1 ∧ -8 * (C + 1) ≤ ⟪w, p⟫_ℝ ∧
        ⟪w, p⟫_ℝ ≤ 0 ∧ ‖Y‖ ≤ 8 * (C + 1) / h := by
  have hbound (T : E →L[ℝ] E) (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      |⟪T v, w⟫_ℝ| ≤ ‖T‖ := by
    calc
      |⟪T v, w⟫_ℝ| ≤ ‖T v‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg w)
      _ = ‖T‖ := by rw [hv, hw, mul_one, mul_one]
  have hsym : ⟪Λ q, p⟫_ℝ = ⟪Λ p, q⟫_ℝ := by
    rw [hΛ.inner_left_eq_inner_right, real_inner_comm]
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hnorm⟩ := select_endpoint_scaled C ε h
    ⟪Λ p, p⟫_ℝ ⟪Λ p, q⟫_ℝ ⟪Λ q, q⟫_ℝ
    ⟪B p, p⟫_ℝ ⟪B q, p⟫_ℝ ⟪B p, q⟫_ℝ ⟪B q, q⟫_ℝ
    hC hε hsmall hh (hΛ.inner_nonneg_left p) (positive_cross_sq_le Λ hΛ p q)
    (hΛ.inner_nonneg_left q)
    ((le_abs_self _).trans ((hbound Λ p p hp hp).trans hΛbound))
    ((hbound Λ p q hp hq).trans hΛbound) hBpp
    ((hbound B p p hp hp).trans hBbound) ((hbound B q p hq hp).trans hBbound)
    ((hbound B p q hp hq).trans hBbound) ((hbound B q q hq hq).trans hBbound)
  have hqp : ⟪q, p⟫_ℝ = 0 := (real_inner_comm _ _).trans hpq
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hqq : ⟪q, q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hq, one_pow]
  refine ⟨yp, yq, ?_, ?_, ?_, ?_⟩
  · convert hwq using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hpq, hpp, hqq]
    ring
  · convert hwpl using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · convert hwpu using 1
    simp only [map_add, map_smul, inner_sub_left, inner_add_left,
        inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsym, hpq, hqp, hpp]
    ring
  · calc
      ‖yp • p + yq • q‖ ≤ ‖yp • p‖ + ‖yq • q‖ := norm_add_le _ _
      _ = |yp| + |yq| := by rw [norm_smul, norm_smul, hp, hq]; simp
      _ ≤ 8 * (C + 1) / h := hnorm

end EulerDNSelection

end

section

namespace EulerLagrangian

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The unforced Euler momentum residual, with space-time derivative and the
canonical real gradient. -/
def momentumResidual (u : ℝ × E → E) (p : ℝ × E → ℝ) (z : ℝ × E) : E :=
  fderiv ℝ u z (1, u z) + gradient (fun x => p (z.1, x)) z.2

omit [CompleteSpace E] in
theorem material_derivative (w : ℝ × E → E) (X : ℝ → E) (t : ℝ)
    (U : E) (D : (ℝ × E) →L[ℝ] E)
    (hX : HasDerivAt X U t) (hw : HasFDerivAt w D (t, X t)) :
    HasDerivAt (fun s => w (s, X s)) (D (1, U)) t :=
  hw.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

theorem gradient_add (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y + g y) x = gradient f x + gradient g x := by
  have hs : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  simp only [gradient, hs.fderiv, map_add]

theorem momentum_perturbation (u w : ℝ × E → E) (p q : ℝ × E → ℝ)
    (z : ℝ × E) (Du Dw : (ℝ × E) →L[ℝ] E)
    (hu : HasFDerivAt u Du z) (hw : HasFDerivAt w Dw z)
    (hp : DifferentiableAt ℝ (fun x => p (z.1, x)) z.2)
    (hq : DifferentiableAt ℝ (fun x => q (z.1, x)) z.2) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) z =
      momentumResidual u p z + Dw (1, u z) + Du (0, w z) + Dw (0, w z) +
        gradient (fun x => q (z.1, x)) z.2 := by
  have hsplit : ((1 : ℝ), u z + w z) = (1, u z) + (0, w z) := by simp
  have hs : HasFDerivAt (fun y => u y + w y) (Du + Dw) z := hu.add hw
  simp only [momentumResidual, hs.fderiv, hu.fderiv,
    add_apply, hsplit, map_add,
    gradient_add _ _ _ hp hq]
  abel

theorem euler_perturbation_along_flow (u w : ℝ × E → E)
    (p q : ℝ × E → ℝ) (X : ℝ → E) (t : ℝ)
    (Du Dw : (ℝ × E) →L[ℝ] E) (V : E)
    (hX : HasDerivAt X (u (t, X t)) t)
    (hu : HasFDerivAt u Du (t, X t)) (hw : HasFDerivAt w Dw (t, X t))
    (hW : HasDerivAt (fun s => w (s, X s)) V t)
    (hp : DifferentiableAt ℝ (fun x => p (t, x)) (X t))
    (hq : DifferentiableAt ℝ (fun x => q (t, x)) (X t))
    (hparent : momentumResidual u p (t, X t) = 0) :
    momentumResidual (fun y => u y + w y) (fun y => p y + q y) (t, X t) =
      V + Du (0, w (t, X t)) + Dw (0, w (t, X t)) +
        gradient (fun x => q (t, x)) (X t) := by
  have hV := hW.unique (material_derivative w X t _ Dw hX hw)
  rw [momentum_perturbation u w p q (t, X t) Du Dw hu hw hp hq, hparent,
    zero_add, ← hV]

omit [CompleteSpace E] in
theorem deformation_acceleration (F M H : ℝ → E →L[ℝ] E) (t : ℝ)
    (hF : HasDerivAt F ((M t).comp (F t)) t)
    (hM : HasDerivAt M (-((M t).comp (M t)) - H t) t) :
    HasDerivAt (fun s => (M s).comp (F s)) (-((H t).comp (F t))) t := by
  convert hM.clm_comp hF using 1
  ext v
  simp only [add_apply, sub_apply, neg_apply, ContinuousLinearMap.comp_apply]
  abel

omit [CompleteSpace E] in
theorem derivative_pullback_inverse (f X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    fderiv ℝ f (X x) = (fderiv ℝ (f ∘ X) x).comp F.symm.toContinuousLinearMap := by
  rw [(hf.hasFDerivAt.comp x hX).fderiv]
  ext v
  simp

theorem gradient_pullback (f : E → ℝ) (X : E → E) (F : E →L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F x) (hf : DifferentiableAt ℝ f (X x)) :
    gradient (f ∘ X) x = F.adjoint (gradient f (X x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    (hf.hasFDerivAt.comp x hX).fderiv]
  rfl

theorem gradient_pullback_inverse (f : E → ℝ) (X : E → E) (F : E ≃L[ℝ] E) (x : E)
    (hX : HasFDerivAt X F.toContinuousLinearMap x)
    (hf : DifferentiableAt ℝ f (X x)) :
    gradient f (X x) = F.symm.toContinuousLinearMap.adjoint (gradient (f ∘ X) x) := by
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, gradient_pullback f X _ x hX hf,
    ContinuousLinearMap.adjoint_inner_left]
  simp

end EulerLagrangian

end

section

namespace EulerVectorCalculus

open EulerSmoothLimit
open scoped ContDiff

/-- The ordinary coordinate derivative, evaluated using the Fréchet derivative. -/
def partialDerivative (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The three-dimensional curl of a vector potential in standard coordinates. -/
def curl (ψ : Fin 3 → Space → ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
    (fun i => partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x)

@[simp] theorem curl_apply (ψ : Fin 3 → Space → ℝ) (x : Space) (i : Fin 3) :
    curl ψ x i = partialDerivative (ψ (i + 2)) (i + 1) x -
      partialDerivative (ψ (i + 1)) (i + 2) x := rfl

theorem contDiff_partialDerivative (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (partialDerivative f i) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_curl (ψ : Fin 3 → Space → ℝ) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) :
    ContDiff ℝ ∞ (curl ψ) := by
  apply (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm.contDiff.comp
  exact contDiff_pi.mpr (fun i =>
    (contDiff_partialDerivative _ (hψ _) _).sub (contDiff_partialDerivative _ (hψ _) _))

theorem partialDerivative_comm (f : Space → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Space) :
    partialDerivative (partialDerivative f i) j x =
      partialDerivative (partialDerivative f j) i x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have he (a b : Fin 3) : partialDerivative (partialDerivative f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold partialDerivative
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [he, he]
  exact (hf.contDiffAt.isSymmSndFDerivAt (n := 2) (by simp)).eq _ _

theorem fderiv_coordinate (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) (v : Space) :
    fderiv ℝ (fun y => f y i) x v = (fderiv ℝ f x v) i := by
  have he : HasFDerivAt (fun y => f y i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ f x)) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f x) i).comp x hf.hasFDerivAt
  rw [he.fderiv]
  rfl

theorem divergence_curl (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (x : Space) : divergence (curl ψ) x = 0 := by
  have hc : DifferentiableAt ℝ (curl ψ) x :=
    ((contDiff_curl ψ hψ).differentiable (by simp)).differentiableAt
  have hp (f : Space → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
      DifferentiableAt ℝ (partialDerivative f i) x :=
    ((contDiff_partialDerivative f hf i).differentiable (by simp)).differentiableAt
  have he (i : Fin 3) : (fderiv ℝ (curl ψ) x (EuclideanSpace.single i 1)) i =
      partialDerivative (partialDerivative (ψ (i + 2)) (i + 1)) i x -
        partialDerivative (partialDerivative (ψ (i + 1)) (i + 2)) i x := by
    rw [← fderiv_coordinate _ _ hc i]
    simp only [curl_apply]
    have hd : HasFDerivAt
        (fun y => partialDerivative (ψ (i + 2)) (i + 1) y -
          partialDerivative (ψ (i + 1)) (i + 2) y)
        (fderiv ℝ (partialDerivative (ψ (i + 2)) (i + 1)) x -
          fderiv ℝ (partialDerivative (ψ (i + 1)) (i + 2)) x) x :=
      (hp _ (hψ _) _).hasFDerivAt.sub (hp _ (hψ _) _).hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [divergence_eq_coordinate_sum, Fin.sum_univ_three, he, he, he]
  change partialDerivative (partialDerivative (ψ 2) 1) 0 x -
    partialDerivative (partialDerivative (ψ 1) 2) 0 x +
    (partialDerivative (partialDerivative (ψ 0) 2) 1 x -
    partialDerivative (partialDerivative (ψ 2) 0) 1 x) +
    (partialDerivative (partialDerivative (ψ 1) 0) 2 x -
    partialDerivative (partialDerivative (ψ 0) 1) 2 x) = 0
  rw [partialDerivative_comm (ψ 2) ((hψ 2).of_le (by simp)) 1 0 x,
    partialDerivative_comm (ψ 0) ((hψ 0).of_le (by simp)) 2 1 x,
    partialDerivative_comm (ψ 1) ((hψ 1).of_le (by simp)) 0 2 x]
  ring

theorem tsupport_curl_subset (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsClosed K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    tsupport (curl ψ) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  have hzero : curl ψ x = 0 := by
    ext i
    have h₁ : x ∉ tsupport (ψ (i + 2)) := fun h => hnot (hψ _ h)
    have h₂ : x ∉ tsupport (ψ (i + 1)) := fun h => hnot (hψ _ h)
    simp [curl_apply, partialDerivative, fderiv_of_notMem_tsupport ℝ h₁,
      fderiv_of_notMem_tsupport ℝ h₂]
  exact hx hzero

theorem hasCompactSupport_curl (ψ : Fin 3 → Space → ℝ) (K : Set Space)
    (hK : IsCompact K) (hψ : ∀ i, tsupport (ψ i) ⊆ K) :
    HasCompactSupport (curl ψ) :=
  hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_curl_subset ψ K hK.isClosed hψ)

theorem partialDerivative_odd_of_even (f : Space → ℝ) (hf : Differentiable ℝ f)
    (heven : ∀ x, f (-x) = f x) (i : Fin 3) (x : Space) :
    partialDerivative f i (-x) = -partialDerivative f i x := by
  have he : (fun y => f (-y)) = f := funext heven
  have hd : HasFDerivAt (fun y => f (-y))
      ((fderiv ℝ f (-x)).comp (-ContinuousLinearMap.id ℝ Space)) x :=
    (hf (-x)).hasFDerivAt.comp x (hasFDerivAt_id x).neg
  have hv := congrArg (fun A : Space →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd.fderiv
  rw [he] at hv
  simp only [ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg] at hv
  exact neg_eq_iff_eq_neg.mp hv.symm

theorem odd_curl_of_even (ψ : Fin 3 → Space → ℝ)
    (hψ : ∀ i, Differentiable ℝ (ψ i)) (heven : ∀ i x, ψ i (-x) = ψ i x) (x : Space) :
    curl ψ (-x) = -curl ψ x := by
  ext i
  simp only [curl_apply, PiLp.neg_apply,
    partialDerivative_odd_of_even _ (hψ _) (heven _) _ _]
  ring

/-- The vector potential `-x × (L x) / 3` in cyclic coordinates. -/
def linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) : ℝ :=
  (-1 / 3 : ℝ) * (x (i + 1) * (L x) (i + 2) - x (i + 2) * (L x) (i + 1))

theorem contDiff_linearPotential (L : Space →L[ℝ] Space) (i : Fin 3) :
    ContDiff ℝ ∞ (linearPotential L i) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x j) :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
  have hL (j : Fin 3) : ContDiff ℝ ∞ (fun x : Space => L x j) := (hc j).comp L.contDiff
  exact contDiff_const.mul (((hc _).mul (hL _)).sub ((hc _).mul (hL _)))

theorem linearPotential_even (L : Space →L[ℝ] Space) (i : Fin 3) (x : Space) :
    linearPotential L i (-x) = linearPotential L i x := by
  simp [linearPotential, map_neg, PiLp.neg_apply]

theorem partialDerivative_linearPotential (L : Space →L[ℝ] Space) (i j : Fin 3)
    (x : Space) :
    partialDerivative (linearPotential L i) j x =
      -((EuclideanSpace.single j (1 : ℝ) : Space) (i + 1) * (L x) (i + 2) +
        x (i + 1) * (L (EuclideanSpace.single j 1)) (i + 2) -
        ((EuclideanSpace.single j (1 : ℝ) : Space) (i + 2) * (L x) (i + 1) +
        x (i + 2) * (L (EuclideanSpace.single j 1)) (i + 1))) / 3 := by
  have hc (a : Fin 3) := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x a
  have hL (a : Fin 3) := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (L x) a).comp x L.hasFDerivAt
  have hd := (((hc (i + 1)).mul (hL (i + 2))).sub
    ((hc (i + 2)).mul (hL (i + 1)))).const_mul (-1 / 3 : ℝ)
  change HasFDerivAt (linearPotential L i) _ x at hd
  unfold partialDerivative
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply, PiLp.proj_apply, smul_eq_mul]
  ring

theorem curl_linearPotential (L : Space →L[ℝ] Space) (x : Space) :
    curl (linearPotential L) x = L x -
      (LinearMap.trace ℝ Space L.toLinearMap / 3) • x := by
  have hx : (∑ j : Fin 3, x j • (EuclideanSpace.single j 1 : Space)) = x := by
    simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hL (i : Fin 3) : (L x) i =
      ∑ j : Fin 3, x j * (L (EuclideanSpace.single j 1)) i := by
    nth_rw 1 [← hx]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [← coordinateTrace_eq_linearTrace]
  ext i
  fin_cases i <;>
    simp [curl_apply, partialDerivative_linearPotential, coordinateTrace,
      Fin.sum_univ_three, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, hL] <;> ring

theorem curl_linearPotential_of_trace_zero (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0) (x : Space) :
    curl (linearPotential L) x = L x := by
  rw [curl_linearPotential, hL, zero_div, zero_smul, sub_zero]

theorem curl_congr_nhds (ψ φ : Fin 3 → Space → ℝ) (x : Space)
    (h : ∀ i, ψ i =ᶠ[nhds x] φ i) : curl ψ x = curl φ x := by
  ext i
  simp only [curl_apply, partialDerivative, (h (i + 2)).fderiv_eq,
    (h (i + 1)).fderiv_eq]

/-- A trace-free linear velocity has an odd, smooth, compactly supported,
divergence-free extension from any prescribed ball. -/
theorem compact_solenoidal_extension (L : Space →L[ℝ] Space)
    (hL : LinearMap.trace ℝ Space L.toLinearMap = 0)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    ∃ u : Space → Space, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      tsupport u ⊆ Metric.closedBall 0 R ∧
      (∀ x, divergence u x = 0) ∧ (∀ x, u (-x) = -u x) ∧
      (∀ x ∈ Metric.ball 0 r, u x = L x) := by
  let χ : ContDiffBump (0 : Space) := ⟨r, R, hr, hrR⟩
  let ψ : Fin 3 → Space → ℝ := fun i x => χ x * linearPotential L i x
  have hψ (i : Fin 3) : ContDiff ℝ ∞ (ψ i) :=
    χ.contDiff.mul (contDiff_linearPotential L i)
  have hsupport (i : Fin 3) : tsupport (ψ i) ⊆ Metric.closedBall 0 R := by
    have hs : tsupport (ψ i) ⊆ tsupport χ := tsupport_mul_subset_left
    exact hs.trans_eq χ.tsupport_eq
  refine ⟨curl ψ, contDiff_curl ψ hψ,
    hasCompactSupport_curl ψ _ (isCompact_closedBall 0 R) hsupport,
    tsupport_curl_subset ψ _ Metric.isClosed_closedBall hsupport,
    divergence_curl ψ hψ, ?_, ?_⟩
  · intro x
    apply odd_curl_of_even ψ (fun i => (hψ i).differentiable (by simp))
    intro i y
    dsimp [ψ]
    rw [χ.neg, linearPotential_even]
  · intro x hx
    have hχ : (χ : Space → ℝ) =ᶠ[nhds x] 1 := χ.eventuallyEq_one_of_mem_ball hx
    have he (i : Fin 3) : ψ i =ᶠ[nhds x] linearPotential L i := by
      filter_upwards [hχ] with y hy
      change χ y * linearPotential L i y = linearPotential L i y
      rw [hy]
      exact one_mul _
    rw [curl_congr_nhds ψ (linearPotential L) x he,
      curl_linearPotential_of_trace_zero L hL]

end EulerVectorCalculus

end

section

namespace EulerGevreyCutoff

open Set Filter Complex MeasureTheory
open scoped Topology ContDiff

/-- Holomorphic function used to estimate the flat real bump by Cauchy's inequality. -/
def complexFlat (z : ℂ) : ℂ := Complex.exp (-z⁻¹)

theorem real_part_inv_lower_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) : 1 / (8 * x) ≤ (z⁻¹).re := by
  have hre : x / 2 ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hz
    simp only [sub_re, ofReal_re] at h
    have := (abs_le.mp h).1
    linarith
  have hn : ‖z‖ ≤ 2 * x := by
    calc
      ‖z‖ = ‖(z - (x : ℂ)) + (x : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ x / 2 + x := by simpa [Complex.norm_real, abs_of_pos hx] using add_le_add_right hz x
      _ ≤ 2 * x := by linarith
  have hzn : z ≠ 0 := by intro h; simp [h] at hre; linarith
  have hden : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzn)
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * x) hden).2
  have hsq : ‖z‖ ^ 2 ≤ (2 * x) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hn 2
  nlinarith

theorem complexFlat_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ complexFlat z :=
  Complex.differentiableAt_exp.comp z (differentiableAt_id.inv hz).neg

theorem complexFlat_disc_bound (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz : ‖z - (x : ℂ)‖ ≤ x / 2) :
    ‖complexFlat z‖ ≤ Real.exp (-(1 / (8 * x))) := by
  rw [complexFlat, Complex.norm_exp, neg_re]
  exact Real.exp_le_exp.mpr (neg_le_neg (real_part_inv_lower_bound x hx z hz))

theorem factorial_decay (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-t) ≤ n.factorial := by
  have hf : 0 < (n.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp t ht n)
  calc
    t ^ n * Real.exp (-t) ≤ (Real.exp t * n.factorial) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = n.factorial := by rw [Real.exp_neg]; field_simp

theorem complexFlat_gevrey_bound (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hr : 0 < x / 2 := by positivity
  have hfd : DifferentiableOn ℂ complexFlat (Metric.closedBall (x : ℂ) (x / 2)) := by
    intro z hz
    have hd : ‖z - (x : ℂ)‖ ≤ x / 2 := by simpa [dist_eq_norm] using hz
    have hn : z ≠ 0 := by
      intro h
      simp [h, Complex.norm_real, abs_of_pos hx] at hd
      linarith
    exact (complexFlat_differentiableAt hn).differentiableWithinAt
  have hfc : DiffContOnCl ℂ complexFlat (Metric.ball (x : ℂ) (x / 2)) :=
    (hfd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hfc
    (fun z hz => complexFlat_disc_bound x hx z (by
      exact le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz)))
  let t : ℝ := 1 / (8 * x)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hi : (x / 2)⁻¹ = 16 * t := by dsimp [t]; field_simp; ring
  have he : (n.factorial : ℝ) * Real.exp (-t) / (x / 2) ^ n =
      (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := by
    rw [div_eq_mul_inv, ← inv_pow, hi, mul_pow]
    ring
  change ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤ _
  calc
    ‖iteratedDeriv n complexFlat (x : ℂ)‖ ≤
        n.factorial * Real.exp (-t) / (x / 2) ^ n := hc
    _ = (16 : ℝ) ^ n * n.factorial * (t ^ n * Real.exp (-t)) := he
    _ ≤ (16 : ℝ) ^ n * n.factorial * n.factorial :=
      mul_le_mul_of_nonneg_left (factorial_decay n t ht) (by positivity)
    _ = (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by ring

theorem iteratedDeriv_real_restriction (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (n : ℕ) (x : ℝ) (hx : (x : ℂ) ∈ s) :
    iteratedDeriv n (fun t : ℝ => (f (t : ℂ)).re) x =
      (iteratedDeriv n f (x : ℂ)).re := by
  have hc : ContDiffOn ℂ n f s := hf.contDiffOn hs
  have hr : ContDiffOn ℝ n f s := hc.restrict_scalars ℝ
  have hsR : IsOpen (Complex.ofRealCLM ⁻¹' s) := hs.preimage Complex.ofRealCLM.continuous
  have he := Complex.ofRealCLM.iteratedFDerivWithin_comp_right hr hs.uniqueDiffOn
    hsR.uniqueDiffOn hx (le_refl (n : ℕ∞ω))
  rw [iteratedFDerivWithin_of_isOpen n hsR hx] at he
  simp only [Complex.ofRealCLM_apply] at he
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) n hs hx] at he
  have hca : ContDiffAt ℂ n f (x : ℂ) := (hc _ hx).contDiffAt (hs.mem_nhds hx)
  have hra : ContDiffAt ℝ n (f ∘ Complex.ofRealCLM) x :=
    (hca.restrict_scalars ℝ).comp_continuousLinearMap Complex.ofRealCLM
  have hre := Complex.reCLM.iteratedFDeriv_comp_left hra (le_refl (n : ℕ∞ω))
  change (iteratedFDeriv ℝ n (Complex.reCLM ∘ (f ∘ Complex.ofRealCLM)) x)
    (fun _ => 1) = ((iteratedFDeriv ℂ n f (x : ℂ)) (fun _ => 1)).re
  rw [hre, he, ← hca.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp

theorem polynomial_glue_flat (p : Polynomial ℝ) (n : ℕ) (x : ℝ) (hx : x ≤ 0) :
    iteratedDeriv n (fun y => p.eval y⁻¹ * expNegInvGlue y) x = 0 := by
  induction n generalizing p with
  | zero => simp [expNegInvGlue.zero_of_nonpos hx]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y => p.eval y⁻¹ * expNegInvGlue y) =
        fun y => (Polynomial.X ^ 2 * (p - p.derivative)).eval y⁻¹ * expNegInvGlue y :=
      funext (fun y => (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p y).deriv)
    rw [hd]
    exact ih _

theorem expNegInvGlue_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n expNegInvGlue x| ≤ (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  by_cases hx : x ≤ 0
  · have hz : iteratedDeriv n expNegInvGlue x = 0 := by
      simpa using polynomial_glue_flat 1 n x hx
    rw [hz, abs_zero]
    positivity
  have hx : 0 < x := lt_of_not_ge hx
  have hs : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hd : DifferentiableOn ℂ complexFlat ({0}ᶜ : Set ℂ) :=
    fun z hz => (complexFlat_differentiableAt hz).differentiableWithinAt
  have hr := iteratedDeriv_real_restriction complexFlat _ hs hd n x (by simpa using hx.ne')
  have hg : expNegInvGlue =ᶠ[nhds x] (fun t : ℝ => (complexFlat (t : ℂ)).re) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [expNegInvGlue, hy.not_ge, complexFlat, ← Complex.ofReal_inv,
      ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [hg.iteratedDeriv_eq n, hr]
  exact (Complex.abs_re_le_norm _).trans (complexFlat_gevrey_bound n x hx)

/-- Nonnegative even smooth bump supported on the unit interval. -/
def rawBump (x : ℝ) : ℝ := expNegInvGlue (x + 1) * expNegInvGlue (1 - x)

theorem rawBump_contDiff : ContDiff ℝ ∞ rawBump := by
  exact (expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem rawBump_nonneg (x : ℝ) : 0 ≤ rawBump x :=
  mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem rawBump_even (x : ℝ) : rawBump (-x) = rawBump x := by
  simp only [rawBump, neg_add_eq_sub, sub_neg_eq_add]
  rw [add_comm (1 : ℝ) x, mul_comm]

theorem rawBump_pos_zero : 0 < rawBump 0 := by
  apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> norm_num

theorem rawBump_support : tsupport rawBump ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])
  · by_contra h
    have hz := expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)
    exact hx (by simp [rawBump, hz])

theorem rawBump_compactSupport : HasCompactSupport rawBump :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) rawBump_support

theorem rawBump_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n rawBump x| ≤ 3 * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun y => expNegInvGlue (y + 1)
  let g : ℝ → ℝ := fun y => expNegInvGlue (1 - y)
  have hf : ContDiff ℝ ∞ f := expNegInvGlue.contDiff.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ g := expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hb₁ (k : ℕ) : |iteratedDeriv k f x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [f, EulerGevrey.majorant, iteratedDeriv_comp_add_const] using
      expNegInvGlue_gevrey_bound k (x + 1)
  have hb₂ (k : ℕ) : |iteratedDeriv k g x| ≤ 1 * EulerGevrey.majorant 16 0 k := by
    simpa [g, EulerGevrey.majorant, iteratedDeriv_comp_const_sub, abs_mul, abs_pow] using
      expNegInvGlue_gevrey_bound k (1 - x)
  have hp := EulerGevrey.sequence_product_majorant 16 1 1 (by norm_num) (by norm_num)
    (by norm_num) 0 0 (fun k => iteratedDeriv k f x) (fun k => iteratedDeriv k g x) hb₁ hb₂ n
  have hmul : rawBump = f * g := rfl
  rw [hmul, iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  simpa [EulerGevrey.majorant, mul_assoc] using hp

/-- Positive integral used to normalize the smooth transition. -/
def bumpMass : ℝ := ∫ t in (-1 : ℝ)..1, rawBump t

theorem bumpMass_pos : 0 < bumpMass := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (rawBump_contDiff.continuous.intervalIntegrable _ _)
  · intro x hx
    apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> linarith [hx.1, hx.2]
  · norm_num

/-- Smooth monotone transition from zero to one, with explicit Gevrey bounds. -/
def transition (x : ℝ) : ℝ := (∫ t in (-1 : ℝ)..x, rawBump t) / bumpMass

theorem transition_hasDerivAt (x : ℝ) :
    HasDerivAt transition (rawBump x / bumpMass) x := by
  have hc := rawBump_contDiff.continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).div_const bumpMass

theorem transition_deriv : deriv transition = fun x => rawBump x / bumpMass :=
  funext (fun x => (transition_hasDerivAt x).deriv)

theorem transition_contDiff : ContDiff ℝ ∞ transition := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (transition_hasDerivAt x).differentiableAt,
    transition_deriv ▸ rawBump_contDiff.div_const bumpMass⟩

theorem rawBump_eq_zero_of_le (x : ℝ) (hx : x ≤ -1) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show x + 1 ≤ 0 by linarith)]

theorem rawBump_eq_zero_of_ge (x : ℝ) (hx : 1 ≤ x) : rawBump x = 0 := by
  simp [rawBump, expNegInvGlue.zero_of_nonpos (show 1 - x ≤ 0 by linarith)]

theorem transition_zero_of_le (x : ℝ) (hx : x ≤ -1) : transition x = 0 := by
  have hi : (∫ t in x..(-1 : ℝ), rawBump t) = 0 := by
    calc
      _ = ∫ t in x..(-1 : ℝ), (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_le t (((uIcc_of_le hx) ▸ ht).2))
      _ = 0 := by simp
  unfold transition
  rw [intervalIntegral.integral_symm, hi]
  simp

theorem transition_one_of_ge (x : ℝ) (hx : 1 ≤ x) : transition x = 1 := by
  have hi : (∫ t in (1 : ℝ)..x, rawBump t) = 0 := by
    calc
      _ = ∫ t in (1 : ℝ)..x, (0 : ℝ) := intervalIntegral.integral_congr (fun t ht =>
        rawBump_eq_zero_of_ge t (((uIcc_of_le hx) ▸ ht).1))
      _ = 0 := by simp
  unfold transition
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (rawBump_contDiff.continuous.intervalIntegrable (-1) 1)
    (rawBump_contDiff.continuous.intervalIntegrable 1 x), hi, add_zero]
  exact div_self bumpMass_pos.ne'

theorem transition_monotone : Monotone transition := by
  apply monotone_of_deriv_nonneg (fun x => (transition_hasDerivAt x).differentiableAt)
  intro x
  rw [transition_deriv]
  exact div_nonneg (rawBump_nonneg x) bumpMass_pos.le

theorem transition_mem_unitInterval (x : ℝ) : transition x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · by_cases hx : x ≤ -1
    · rw [transition_zero_of_le x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_zero_of_le (-1) le_rfl] at h
  · by_cases hx : 1 ≤ x
    · rw [transition_one_of_ge x hx]
    · have h := transition_monotone (le_of_lt (lt_of_not_ge hx))
      rwa [transition_one_of_ge 1 le_rfl] at h

theorem transition_gevrey_bound (n : ℕ) (x : ℝ) :
    |iteratedDeriv n transition x| ≤
      (1 + 3 / bumpMass) * (16 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 := by
  have hm := bumpMass_pos
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg (transition_mem_unitInterval x).1]
    have h := (transition_mem_unitInterval x).2
    have : 0 < 3 / bumpMass := div_pos (by norm_num) bumpMass_pos
    linarith
  | succ n =>
    rw [iteratedDeriv_succ', transition_deriv]
    have he : (fun x => rawBump x / bumpMass) = fun x => rawBump x * bumpMass⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos bumpMass_pos]
    have hb := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n x) (inv_nonneg.mpr bumpMass_pos.le)
    have hp : (16 : ℝ) ^ n ≤ 16 ^ (n + 1) := by gcongr <;> norm_num
    have hf : (n.factorial : ℝ) ^ 2 ≤ ((n + 1).factorial : ℝ) ^ 2 := by
      gcongr
      omega
    have hA : 3 * bumpMass⁻¹ ≤ 1 + 3 / bumpMass := by rw [div_eq_mul_inv]; linarith
    calc
      _ ≤ (3 * 16 ^ n * (n.factorial : ℝ) ^ 2) * bumpMass⁻¹ := hb
      _ = (3 * bumpMass⁻¹) * 16 ^ n * (n.factorial : ℝ) ^ 2 := by ring
      _ ≤ (1 + 3 / bumpMass) * 16 ^ (n + 1) * ((n + 1).factorial : ℝ) ^ 2 := by
        gcongr


end EulerGevreyCutoff

end

section

namespace EulerGevreyFunctions

open EulerGevreyCutoff EulerGevrey
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem product_bound (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb₁ : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ A * majorant R 0 n)
    (hb₂ : ∀ n x, ‖iteratedFDeriv ℝ n g x‖ ≤ B * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ (3 * A * B) * majorant R 0 n := by
  have hp := sequence_product_majorant R A B hR hA hB 0 0
    (fun k => ‖iteratedFDeriv ℝ k f x‖) (fun k => ‖iteratedFDeriv ℝ k g x‖)
    (fun k => by simpa only [abs_norm] using hb₁ k x)
    (fun k => by simpa only [abs_norm] using hb₂ k x) n
  exact (norm_iteratedFDeriv_mul_le hf hg x (by simp)).trans
    ((le_abs_self _).trans (by simpa using hp))

theorem linear_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ A * majorant (R * C) 0 n := by
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hnorm
  calc
    _ ≤ |iteratedDeriv n f (L x)| * ‖L‖ ^ n := hnorm
    _ ≤ (A * majorant R 0 n) * C ^ n :=
      mul_le_mul (hb n (L x)) (pow_le_pow_left₀ (norm_nonneg _) hL n)
        (pow_nonneg (norm_nonneg _) n) (mul_nonneg hA (majorant_nonneg R hR 0 n))
    _ = A * majorant (R * C) 0 n := by simp [majorant, mul_pow]; ring

theorem affine_composition_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] ℝ) (a R A C : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hL : ‖L‖ ≤ C) (hb : ∀ n x, |iteratedDeriv n f x| ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => f (L y + a)) x‖ ≤ A * majorant (R * C) 0 n := by
  exact linear_composition_bound (fun t => f (t + a))
    (hf.comp (contDiff_id.add contDiff_const)) L R A C hR hA hC hL
    (fun k y => by simpa only [iteratedDeriv_comp_add_const] using hb k (y + a)) n x

theorem finite_product_bound {ι : Type*} [DecidableEq ι] (u : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ u, ContDiff ℝ ∞ (f i))
    (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ i ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f i) x‖ ≤ A * majorant R 0 n)
    (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∏ i ∈ u, f i y) x‖ ≤
      (3 * A) ^ u.card * majorant R 0 n := by
  induction u using Finset.induction_on generalizing n x with
  | empty =>
    cases n with
    | zero => simp [majorant]
    | succ n => simp [iteratedFDeriv_succ_const, majorant_nonneg R hR]
  | @insert i u hi ih =>
    have hfu : ∀ j ∈ u, ContDiff ℝ ∞ (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hbu : ∀ j ∈ u, ∀ n x, ‖iteratedFDeriv ℝ n (f j) x‖ ≤ A * majorant R 0 n :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have he : (fun y => ∏ j ∈ insert i u, f j y) =
        fun y => f i y * ∏ j ∈ u, f j y := by
      funext y
      rw [Finset.prod_insert hi]
    rw [he, Finset.card_insert_of_notMem hi]
    have hp := product_bound (f i) (fun y => ∏ j ∈ u, f j y)
      (hf i (Finset.mem_insert_self _ _)) (contDiff_prod hfu)
      R A ((3 * A) ^ u.card) hR hA (by positivity)
      (hb i (Finset.mem_insert_self _ _)) (fun k y => ih hfu hbu k y) n x
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hp

end EulerGevreyFunctions

end

section

namespace EulerGevreyInverse

open EulerGevrey Finset
open scoped ContDiff

theorem reciprocal_derivative_recurrence (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x = -(f x)⁻¹ *
      ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv (k + 1) f x * iteratedDeriv (n + 1 - (k + 1)) (fun y => (f y)⁻¹) x := by
  have hi : ContDiff ℝ ∞ (fun y => (f y)⁻¹) := hf.inv hnz
  have he : (fun y => f y * (f y)⁻¹) = fun _ => (1 : ℝ) := by
    funext y
    exact mul_inv_cancel₀ (hnz y)
  have hp := congrArg (fun g : ℝ → ℝ => iteratedDeriv (n + 1) g x) he
  have hmul : (fun y => f y * (f y)⁻¹) = f * (fun y => (f y)⁻¹) := rfl
  rw [hmul] at hp
  rw [iteratedDeriv_mul (hf.contDiffAt.of_le (by simp)) (hi.contDiffAt.of_le (by simp)),
    sum_range_succ'] at hp
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
    Nat.sub_zero, iteratedDeriv_const, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte] at hp
  have h := congrArg (fun z : ℝ => (f x)⁻¹ * z) hp
  field_simp [hnz x] at h ⊢
  nlinarith

theorem reciprocal_gevrey_shift (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ majorant R 1 n := by
  have hA0 : 0 ≤ A := by linarith
  have hR0 : 0 ≤ R := by nlinarith
  apply triangular_inverse_majorant A Rc R hA hRc hR 0
    (fun n => if n = 0 then 1 else 0)
    (fun n => |iteratedDeriv n (fun y => (f y)⁻¹) x|) _ _ n
  · intro k
    split_ifs with hk
    · subst k
      simp [majorant]
    · exact majorant_nonneg R hR0 0 k
  · intro k
    cases k with
    | zero => simpa using hb x
    | succ k =>
      rw [reciprocal_derivative_recurrence f hf hnz k x, abs_mul, abs_neg]
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
      apply mul_le_mul (hb x) _ (abs_nonneg _) hA0
      calc
        _ ≤ ∑ j ∈ range (k + 1), |((k + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) f x *
            iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x| := abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply sum_le_sum
          intro j _
          have hj : (0 : ℝ) ≤ (k + 1).choose (j + 1) := by positivity
          have h := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hc j x) hj)
            (abs_nonneg (iteratedDeriv (k + 1 - (j + 1)) (fun y => (f y)⁻¹) x))
          simpa only [abs_mul, abs_of_nonneg hj, majorant, Nat.add_zero, mul_assoc] using h

theorem shift_one_bound (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 1 n ≤ R * majorant (4 * R) 0 n := by
  have hnat : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
  have hn : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hs : ((n : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ n := by
    calc
      _ ≤ ((2 : ℝ) ^ n) ^ 2 := by gcongr
      _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
  simp only [majorant, Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_pow, pow_succ]
  have hp := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (pow_nonneg hR n) (mul_nonneg hR (sq_nonneg (n.factorial : ℝ))))
  nlinarith

theorem reciprocal_gevrey (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hnz : ∀ x, f x ≠ 0) (A Rc R : ℝ) (hA : 1 ≤ A) (hRc : 0 ≤ Rc)
    (hR : 2 * A * (Rc + 1) ≤ R)
    (hb : ∀ x, |(f x)⁻¹| ≤ A)
    (hc : ∀ n x, |iteratedDeriv (n + 1) f x| ≤ majorant Rc 0 (n + 1))
    (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => (f y)⁻¹) x| ≤ R * majorant (4 * R) 0 n := by
  have hR0 : 0 ≤ R := by nlinarith
  exact (reciprocal_gevrey_shift f hf hnz A Rc R hA hRc hR hb hc n x).trans
    (shift_one_bound R hR0 n)

end EulerGevreyInverse

end

section

namespace EulerSpatialCutoffs

open EulerGevrey EulerGevreyCutoff EulerGevreyFunctions EulerSmoothLimit
open scoped ContDiff
open Set

/-- The even one-dimensional bump normalized to have value one at the origin. -/
def normalizedBump (t : ℝ) : ℝ := rawBump t / rawBump 0

theorem normalizedBump_contDiff : ContDiff ℝ ∞ normalizedBump :=
  rawBump_contDiff.div_const _

theorem normalizedBump_zero : normalizedBump 0 = 1 :=
  div_self rawBump_pos_zero.ne'

theorem normalizedBump_even (t : ℝ) : normalizedBump (-t) = normalizedBump t := by
  simp only [normalizedBump, rawBump_even]

theorem normalizedBump_nonneg (t : ℝ) : 0 ≤ normalizedBump t :=
  div_nonneg (rawBump_nonneg t) rawBump_pos_zero.le

theorem normalizedBump_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n normalizedBump t| ≤ (3 / rawBump 0) * majorant 16 0 n := by
  have he : normalizedBump = fun x => rawBump x * (rawBump 0)⁻¹ := by
    funext x
    simp [normalizedBump, div_eq_mul_inv]
  rw [he, iteratedDeriv_mul_const_field, abs_mul, abs_inv, abs_of_pos rawBump_pos_zero]
  have h := mul_le_mul_of_nonneg_right (rawBump_gevrey_bound n t)
    (inv_nonneg.mpr rawBump_pos_zero.le)
  simpa [majorant, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- A plateau on the unit interval with support inside the interval of radius nine eighths. -/
def outerWindow (t : ℝ) : ℝ := transition (17 + 16 * t) * transition (17 - 16 * t)

theorem outerWindow_contDiff : ContDiff ℝ ∞ outerWindow :=
  (transition_contDiff.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).mul
    (transition_contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem outerWindow_even (t : ℝ) : outerWindow (-t) = outerWindow t := by
  simp [outerWindow, sub_eq_add_neg, mul_comm]

theorem outerWindow_one (t : ℝ) (ht : |t| ≤ 1) : outerWindow t = 1 := by
  have ht' := abs_le.mp ht
  simp [outerWindow, transition_one_of_ge _ (show 1 ≤ 17 + 16 * t by linarith),
    transition_one_of_ge _ (show 1 ≤ 17 - 16 * t by linarith)]

theorem outerWindow_zero (t : ℝ) (ht : 9 / 8 ≤ |t|) : outerWindow t = 0 := by
  rcases le_abs.mp ht with h | h
  · simp [outerWindow, transition_zero_of_le _ (show 17 - 16 * t ≤ -1 by linarith)]
  · simp [outerWindow, transition_zero_of_le _ (show 17 + 16 * t ≤ -1 by linarith)]

theorem outerWindow_gevrey (n : ℕ) (t : ℝ) :
    |iteratedDeriv n outerWindow t| ≤
      (3 * (1 + 3 / bumpMass) ^ 2) * majorant 256 0 n := by
  let L : ℝ →L[ℝ] ℝ := (16 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hn : ‖L‖ ≤ 16 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    simp [L, norm_mul]
  have hmass := bumpMass_pos
  have hb : ∀ n t, |iteratedDeriv n transition t| ≤ (1 + 3 / bumpMass) * majorant 16 0 n :=
    fun n t => by simpa [majorant, mul_assoc] using transition_gevrey_bound n t
  have hp := affine_composition_bound transition transition_contDiff L 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num) hn hb
  have hm := affine_composition_bound transition transition_contDiff (-L) 17 16
    (1 + 3 / bumpMass) 16 (by norm_num) (by positivity) (by norm_num)
    (by simpa using hn) hb
  have hf : ContDiff ℝ ∞ (fun y : ℝ => transition (L y + 17)) :=
    transition_contDiff.comp (L.contDiff.add contDiff_const)
  have hg : ContDiff ℝ ∞ (fun y : ℝ => transition ((-L) y + 17)) :=
    transition_contDiff.comp ((-L).contDiff.add contDiff_const)
  have h := product_bound _ _ hf hg 256 (1 + 3 / bumpMass) (1 + 3 / bumpMass)
    (by norm_num) (by positivity) (by positivity) (by norm_num at hp; exact hp)
    (by norm_num at hm; exact hm) n t
  have he : outerWindow = (fun y => transition (L y + 17) * transition ((-L) y + 17)) := by
    funext y
    simp [outerWindow, L, sub_eq_add_neg, add_comm]
  rw [he]
  simpa [L, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, sub_eq_add_neg, add_comm, pow_two, mul_assoc] using h

/-- Product of three copies of a scalar profile at a common coordinate scale. -/
def tensorCutoff (g : ℝ → ℝ) (a : ℝ) (x : Space) : ℝ := ∏ i : Fin 3, g (a * x i)

theorem tensorCutoff_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (tensorCutoff g a) := by
  apply contDiff_prod
  intro i _
  have hc : ContDiff ℝ ∞ (fun y : Space => y i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff
  exact hg.comp (contDiff_const.mul hc)

theorem tensorCutoff_even (g : ℝ → ℝ) (hg : ∀ t, g (-t) = g t) (a : ℝ) (x : Space) :
    tensorCutoff g a (-x) = tensorCutoff g a x := by
  simp [tensorCutoff, hg]

theorem tensorCutoff_gevrey (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (a R A : ℝ) (ha : 0 ≤ a) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n t, |iteratedDeriv n g t| ≤ A * majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (tensorCutoff g a) x‖ ≤ (3 * A) ^ 3 * majorant (R * a) 0 n := by
  have hL (i : Fin 3) : ‖(a • EuclideanSpace.proj i : Space →L[ℝ] ℝ)‖ ≤ a := by
    apply (a • EuclideanSpace.proj i : Space →L[ℝ] ℝ).opNorm_le_bound ha
    intro y
    simpa [Real.norm_eq_abs, abs_of_nonneg ha] using
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y i) ha
  have hi (i : Fin 3) := linear_composition_bound g hg (a • EuclideanSpace.proj i)
    R A a hR hA ha (hL i) hb
  have h := finite_product_bound (Finset.univ : Finset (Fin 3))
    (fun i (y : Space) => g (a * y i))
    (fun i _ => hg.comp (contDiff_const.mul
      (show ContDiff ℝ ∞ (fun y : Space => y i) from
        (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff)))
    (R * a) A (mul_nonneg hR ha) hA (fun i _ k y => by
      simpa only [Function.comp_def, smul_apply, smul_eq_mul, PiLp.proj_apply] using hi i k y) n x
  have he : tensorCutoff g a = (fun y : Space => ∏ i : Fin 3, g (a * y i)) := rfl
  rw [he]
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Inner spatial cutoff used to localize the leading oscillatory packet. -/
def innerCutoff : Space → ℝ := tensorCutoff normalizedBump 4

/-- Outer plateau used by the compactly supported mean correction. -/
def outerCutoff : Space → ℝ := tensorCutoff outerWindow 1

theorem innerCutoff_contDiff : ContDiff ℝ ∞ innerCutoff :=
  tensorCutoff_contDiff _ normalizedBump_contDiff _

theorem outerCutoff_contDiff : ContDiff ℝ ∞ outerCutoff :=
  tensorCutoff_contDiff _ outerWindow_contDiff _

theorem innerCutoff_even (x : Space) : innerCutoff (-x) = innerCutoff x :=
  tensorCutoff_even _ normalizedBump_even _ _

theorem outerCutoff_even (x : Space) : outerCutoff (-x) = outerCutoff x :=
  tensorCutoff_even _ outerWindow_even _ _

theorem innerCutoff_nonneg (x : Space) : 0 ≤ innerCutoff x := by
  unfold innerCutoff tensorCutoff
  exact Finset.prod_nonneg (fun i _ => normalizedBump_nonneg _)

theorem innerCutoff_zero : innerCutoff 0 = 1 := by
  simp [innerCutoff, tensorCutoff, normalizedBump_zero]

theorem outerCutoff_one (x : Space) (hx : ‖x‖ ≤ 1) : outerCutoff x = 1 := by
  unfold outerCutoff tensorCutoff
  apply Finset.prod_eq_one
  intro i _
  apply outerWindow_one
  simpa only [one_mul, ← Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx

theorem innerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n innerCutoff x‖ ≤
      (9 / rawBump 0) ^ 3 * majorant 64 0 n := by
  have hpos := rawBump_pos_zero
  have h := tensorCutoff_gevrey _ normalizedBump_contDiff 4 16 (3 / rawBump 0)
    (by norm_num) (by norm_num) (by positivity) normalizedBump_gevrey n x
  simpa only [innerCutoff, show (16 : ℝ) * 4 = 64 by norm_num,
    show (3 : ℝ) * (3 / rawBump 0) = 9 / rawBump 0 by ring] using h

theorem outerCutoff_gevrey (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n outerCutoff x‖ ≤
      (9 * (1 + 3 / bumpMass) ^ 2) ^ 3 * majorant 256 0 n := by
  have h := tensorCutoff_gevrey _ outerWindow_contDiff 1 256 (3 * (1 + 3 / bumpMass) ^ 2)
    (by norm_num) (by norm_num) (by positivity) outerWindow_gevrey n x
  simpa only [outerCutoff, mul_one,
    show (3 : ℝ) * (3 * (1 + 3 / bumpMass) ^ 2) = 9 * (1 + 3 / bumpMass) ^ 2 by ring] using h


theorem cube_closed (r : ℝ) : IsClosed (({x : Space | ∀ i, |x i| ≤ r})) := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.abs) continuous_const

theorem norm_sq_le_of_mem_cube (r : ℝ) (hr : 0 ≤ r) (x : Space) (hx : x ∈ ({x : Space | ∀ i, |x i| ≤ r})) :
    ‖x‖ ^ 2 ≤ 3 * r ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (sq_le_sq₀ (abs_nonneg (x i)) hr).2 (hx i)
      simpa only [sq_abs] using h
    _ = _ := by simp

theorem tensorCutoff_support (g : ℝ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ b) :
    tsupport (tensorCutoff g a) ⊆ ({x : Space | ∀ i, |x i| ≤ b / a}) := by
  apply closure_minimal _ (cube_closed _)
  intro x hx i
  have hgx : g (a * x i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  have h := hg (a * x i) hgx
  rw [abs_mul, abs_of_pos ha] at h
  exact (le_div_iff₀ ha).2 (by nlinarith)

theorem innerCutoff_support : tsupport innerCutoff ⊆ Metric.ball (0 : Space) (1 / 2) := by
  have hs := tensorCutoff_support normalizedBump 4 1 (by norm_num) (fun t ht => by
    have hraw : rawBump t ≠ 0 := fun h => ht (by simp [normalizedBump, h])
    exact abs_le.mpr (rawBump_support (subset_tsupport _ hraw)))
  intro x hx
  have hn := norm_sq_le_of_mem_cube (1 / 4) (by norm_num) x (hs hx)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem outerCutoff_support : tsupport outerCutoff ⊆ Metric.closedBall (0 : Space) 2 := by
  have hs := tensorCutoff_support outerWindow 1 (9 / 8) (by norm_num) (fun t ht => by
    by_contra h
    exact ht (outerWindow_zero t (le_of_lt (lt_of_not_ge h))))
  intro x hx
  have hc : x ∈ ({x : Space | ∀ i, |x i| ≤ 9 / 8}) := by simpa using hs hx
  have hn := norm_sq_le_of_mem_cube (9 / 8) (by norm_num) x hc
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg x]

theorem innerCutoff_compactSupport : HasCompactSupport innerCutoff := by
  apply (isCompact_closedBall (0 : Space) (1 / 2)).of_isClosed_subset (isClosed_tsupport _)
  exact innerCutoff_support.trans Metric.ball_subset_closedBall

theorem outerCutoff_compactSupport : HasCompactSupport outerCutoff :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _) outerCutoff_support

end EulerSpatialCutoffs

end

section

namespace EulerPeriodicProfile

open scoped ContDiff
open Real
open EulerGevrey EulerGevreyInverse EulerGevreyFunctions

/-- Explicit smooth periodic profile with a narrow positive derivative peak. -/
def profile (δ t : ℝ) : ℝ := arctan (sin t / (1 + δ - cos t))

/-- Denominator of the derivative of the periodic profile. -/
def denominator (δ t : ℝ) : ℝ := (1 + δ) ^ 2 - 2 * (1 + δ) * cos t + 1

theorem first_denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < 1 + δ - cos t := by
  linarith [cos_le_one t]

theorem denominator_lower (δ : ℝ) (hδ : 0 ≤ δ) (t : ℝ) : δ ^ 2 ≤ denominator δ t := by
  have h := mul_nonneg (show 0 ≤ 2 * (1 + δ) by positivity) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem denominator_pos (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : 0 < denominator δ t :=
  lt_of_lt_of_le (sq_pos_of_pos hδ) (denominator_lower δ hδ.le t)

theorem profile_contDiff (δ : ℝ) (hδ : 0 < δ) : ContDiff ℝ ∞ (profile δ) := by
  apply contDiff_arctan.comp
  exact contDiff_sin.div ((contDiff_const.add contDiff_const).sub contDiff_cos)
    (fun t => (first_denominator_pos δ hδ t).ne')

theorem profile_odd (δ t : ℝ) : profile δ (-t) = -profile δ t := by
  simp [profile, neg_div]

theorem profile_periodic (δ : ℝ) : Function.Periodic (profile δ) (2 * π) := by
  intro t
  simp [profile, sin_add_two_pi, cos_add_two_pi]

theorem profile_hasDerivAt (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (profile δ) (((1 + δ) * cos t - 1) / denominator δ t) t := by
  have hd := first_denominator_pos δ hδ t
  have he := denominator_pos δ hδ t
  have hs := sin_sq_add_cos_sq t
  have hg : HasDerivAt (fun x => sin x / (1 + δ - cos x))
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) t := by
    have hfun : (sin / ((fun _ : ℝ => 1 + δ) - cos)) =
        (fun x => sin x / (1 + δ - cos x)) := rfl
    have ht := (hasDerivAt_sin t).div
      ((hasDerivAt_const t (1 + δ)).sub (hasDerivAt_cos t)) hd.ne'
    rw [hfun] at ht
    simpa only [sub_neg_eq_add, zero_add, Pi.sub_apply, Pi.div_apply] using
      ht
  have heq : (1 + (sin t / (1 + δ - cos t)) ^ 2)⁻¹ *
      ((cos t * (1 + δ - cos t) - sin t * sin t) / (1 + δ - cos t) ^ 2) =
      ((1 + δ) * cos t - 1) / denominator δ t := by
    have hds : (1 + δ - cos t) ^ 2 + sin t ^ 2 = denominator δ t := by
      dsimp [denominator]
      nlinarith
    have hnum : cos t * (1 + δ - cos t) - sin t * sin t = (1 + δ) * cos t - 1 := by
      nlinarith
    rw [hnum]
    field_simp [hd.ne', he.ne']
    rw [hds]
    ring
  exact hg.arctan.congr_deriv (by simpa only [one_div] using heq)

theorem profile_deriv (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    deriv (profile δ) t = ((1 + δ) * cos t - 1) / denominator δ t :=
  (profile_hasDerivAt δ hδ t).deriv

theorem profile_deriv_zero (δ : ℝ) (hδ : 0 < δ) : deriv (profile δ) 0 = δ⁻¹ := by
  rw [profile_deriv δ hδ]
  have he : denominator δ 0 = δ ^ 2 := by simp [denominator]; ring
  rw [he, cos_zero, mul_one]
  ring_nf
  field_simp [hδ.ne']

theorem profile_deriv_lower (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : -1 ≤ deriv (profile δ) t := by
  rw [profile_deriv δ hδ, le_div_iff₀ (denominator_pos δ hδ t)]
  have h := mul_pos (show 0 < 1 + δ by linarith) (first_denominator_pos δ hδ t)
  dsimp [denominator]
  nlinarith

theorem profile_deriv_upper (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : deriv (profile δ) t ≤ δ⁻¹ := by
  rw [profile_deriv δ hδ, inv_eq_one_div,
    div_le_div_iff₀ (denominator_pos δ hδ t) hδ]
  have h := mul_nonneg (mul_nonneg (show 0 ≤ 2 + δ by linarith)
    (show 0 ≤ 1 + δ by linarith)) (sub_nonneg.mpr (cos_le_one t))
  dsimp [denominator]
  nlinarith

theorem profile_mean_zero (δ : ℝ) : ∫ t in (-π)..π, profile δ t = 0 := by
  have he : (fun t => profile δ (-t)) = fun t => -profile δ t := funext (profile_odd δ)
  have hi := intervalIntegral.integral_comp_neg (f := profile δ) (a := -π) (b := π)
  rw [he, intervalIntegral.integral_neg] at hi
  simp only [neg_neg] at hi
  linarith

theorem denominator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (denominator δ) := by
  exact ((contDiff_const.sub (contDiff_const.mul contDiff_cos)).add contDiff_const)

theorem denominator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv (n + 1) (denominator δ) t| ≤ majorant 4 0 (n + 1) := by
  have he : denominator δ = fun t => ((1 + δ) ^ 2 + 1) - (2 * (1 + δ)) * cos t := by
    funext t
    dsimp [denominator]
    ring
  rw [he, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg,
    iteratedDeriv_const_mul_field, abs_neg, abs_mul,
    abs_of_nonneg (show 0 ≤ 2 * (1 + δ) by positivity)]
  have hc := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
    (show 0 ≤ 2 * (1 + δ) by positivity)
  have hp : (4 : ℝ) ≤ 4 ^ (n + 1) := by
    have h : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    nlinarith
  have hf : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) ^ 2 := by
    have hh : (1 : ℝ) ≤ (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    nlinarith
  dsimp [majorant]
  nlinarith

theorem denominator_inverse_bound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (fun t => (denominator δ t)⁻¹) t| ≤
      (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ hδsq).2
    nlinarith
  have hb (t : ℝ) : |(denominator δ t)⁻¹| ≤ (δ ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (denominator_pos δ hδ t))]
    exact inv_anti₀ hδsq (denominator_lower δ hδ.le t)
  have h := reciprocal_gevrey (denominator δ) (denominator_contDiff δ)
    (fun t => (denominator_pos δ hδ t).ne') ((δ ^ 2)⁻¹) 4 (10 * (δ ^ 2)⁻¹)
    hA (by norm_num) (by ring_nf; rfl) hb (denominator_derivative_bound δ hδ.le hδ1) n t
  simpa only [show (4 : ℝ) * (10 * (δ ^ 2)⁻¹) = 40 * (δ ^ 2)⁻¹ by ring] using h

/-- The numerator of the derivative of the explicit periodic profile. -/
def numerator (δ t : ℝ) : ℝ := (1 + δ) * cos t - 1

theorem numerator_contDiff (δ : ℝ) : ContDiff ℝ ∞ (numerator δ) :=
  (contDiff_const.mul contDiff_cos).sub contDiff_const

theorem numerator_derivative_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (t : ℝ) : |iteratedDeriv n (numerator δ) t| ≤ 3 := by
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero]
    dsimp [numerator]
    have ht := abs_cos_le_one t
    have h : |(1 + δ) * cos t - 1| ≤ |(1 + δ) * cos t| + |(1 : ℝ)| := abs_sub _ _
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity), abs_one] at h
    nlinarith
  | succ n =>
    have he : numerator δ = fun t => (-1 : ℝ) + (1 + δ) * cos t := by
      funext t
      dsimp [numerator]
      ring
    rw [he, iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg (show 0 ≤ 1 + δ by positivity)]
    have h := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le_one (n + 1) t)
      (show 0 ≤ 1 + δ by positivity)
    nlinarith

theorem profile_gevrey (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) (t : ℝ) :
    |iteratedDeriv n (profile δ) t| ≤
      (100 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
  have hA : 1 ≤ (δ ^ 2)⁻¹ := by
    apply (one_le_inv₀ (sq_pos_of_pos hδ)).2
    nlinarith
  have hB : 1 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hBi : 0 ≤ 40 * (δ ^ 2)⁻¹ := by linarith
  have hAi : 0 ≤ (δ ^ 2)⁻¹ := by positivity
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero, majorant, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have hp := arctan_lt_pi_div_two (sin t / (1 + δ - cos t))
    have hm := neg_pi_div_two_lt_arctan (sin t / (1 + δ - cos t))
    rw [abs_le]
    dsimp [profile]
    constructor <;> nlinarith [pi_le_four]
  | succ n =>
    have hn (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (numerator δ) x‖ ≤
        3 * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      have hp : 1 ≤ (40 * (δ ^ 2)⁻¹) ^ k := one_le_pow₀ hB
      have hf : (1 : ℝ) ≤ (k.factorial : ℝ) ^ 2 := by
        have hh : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        nlinarith
      have hb := numerator_derivative_bound δ hδ.le hδ1 k x
      dsimp [majorant]
      nlinarith
    have hi (k : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ k (fun t => (denominator δ t)⁻¹) x‖ ≤
        (10 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 k := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        denominator_inverse_bound δ hδ hδ1 k x
    have hp := product_bound (numerator δ) (fun t => (denominator δ t)⁻¹)
      (numerator_contDiff δ) ((denominator_contDiff δ).inv (fun t => (denominator_pos δ hδ t).ne'))
      (40 * (δ ^ 2)⁻¹) 3 (10 * (δ ^ 2)⁻¹) hBi (by norm_num) (by positivity) hn hi n t
    have he : deriv (profile δ) = fun t => numerator δ t * (denominator δ t)⁻¹ := by
      funext t
      rw [profile_deriv δ hδ]
      rfl
    rw [iteratedDeriv_succ', he]
    have hm : majorant (40 * (δ ^ 2)⁻¹) 0 n ≤ majorant (40 * (δ ^ 2)⁻¹) 0 (n + 1) := by
      unfold majorant
      apply mul_le_mul
      · exact pow_le_pow_right₀ hB (by omega)
      · gcongr; omega
      · positivity
      · positivity
    have hp' : |iteratedDeriv n (fun t => numerator δ t * (denominator δ t)⁻¹) t| ≤
        (90 * (δ ^ 2)⁻¹) * majorant (40 * (δ ^ 2)⁻¹) 0 n := by
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
        show (3 : ℝ) * 3 * (10 * (δ ^ 2)⁻¹) = 90 * (δ ^ 2)⁻¹ by ring] using hp
    exact hp'.trans (mul_le_mul (by nlinarith) hm (majorant_nonneg _ hBi _ _)
      (by positivity))

end EulerPeriodicProfile

end

section

namespace EulerAnglePartition

open EulerGevreyCutoff Set
open scoped ContDiff

/-- A compact smooth partition function whose period translates telescope. -/
def partition (T t : ℝ) : ℝ := transition (t / T) - transition (t / T - 1)

theorem partition_contDiff (T : ℝ) : ContDiff ℝ ∞ (partition T) :=
  (transition_contDiff.comp (contDiff_id.div_const T)).sub
    (transition_contDiff.comp ((contDiff_id.div_const T).sub contDiff_const))

theorem partition_nonneg (T t : ℝ) : 0 ≤ partition T t := by
  exact sub_nonneg.mpr (transition_monotone (by linarith))

theorem partition_support (T : ℝ) (hT : 0 < T) :
    tsupport (partition T) ⊆ Icc (-T) (2 * T) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  constructor
  · by_contra h
    have hq : t / T ≤ -1 := (div_le_iff₀ hT).2 (by linarith)
    exact ht (by simp [partition, transition_zero_of_le _ hq,
      transition_zero_of_le _ (show t / T - 1 ≤ -1 by linarith)])
  · by_contra h
    have hq : 2 ≤ t / T := (le_div_iff₀ hT).2 (by linarith)
    exact ht (by simp [partition, transition_one_of_ge _ (show 1 ≤ t / T by linarith),
      transition_one_of_ge _ (show 1 ≤ t / T - 1 by linarith)])

theorem partition_compactSupport (T : ℝ) (hT : 0 < T) : HasCompactSupport (partition T) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (partition_support T hT)

theorem seven_translate_identity (T t : ℝ) (hT : T ≠ 0) :
    (∑ k ∈ Finset.range 7, partition T (t + (3 - (k : ℝ)) * T)) =
      transition (t / T + 3) - transition (t / T - 4) := by
  unfold partition
  simp only [add_div, mul_div_cancel_right₀ _ hT]
  norm_num [Finset.sum_range_succ]
  ring_nf

theorem seven_translate_partition (T : ℝ) (hT : 0 < T) (t : ℝ)
    (ht : t ∈ Icc (-2 * T) (2 * T)) :
    (∑ k ∈ Finset.range 7, partition T (t + (3 - (k : ℝ)) * T)) = 1 := by
  rw [seven_translate_identity T t hT.ne']
  have hlo : -2 ≤ t / T := (le_div_iff₀ hT).2 ht.1
  have hhi : t / T ≤ 2 := (div_le_iff₀ hT).2 ht.2
  rw [transition_one_of_ge _ (show 1 ≤ t / T + 3 by linarith),
    transition_zero_of_le _ (show t / T - 4 ≤ -1 by linarith)]
  norm_num

end EulerAnglePartition

end

section

namespace EulerEnergyBootstrap

open Set Real

theorem radius_bounds (C B Δ ρ₀ S R₀ : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hΔ : 0 ≤ Δ) (hρ : 0 < ρ₀) (_hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    ρ₀ / 2 ≤ ρ₀ - 2 * C * (B + Δ) * t ∧
      0 < ρ₀ - 2 * C * (B + Δ) * t ∧
      (ρ₀ - 2 * C * (B + Δ) * t) * R₀ ≤ 1 := by
  have hl := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 2 * C * (B + Δ) by positivity)
  have hn := mul_nonneg (show 0 ≤ 2 * C * (B + Δ) by positivity) ht.1
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

theorem shrinking_radius_cancels_loss (C B Δ ρ R₀ X : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (hρ : 0 < ρ)
    (hR : 0 ≤ R₀) (hscale : ρ * R₀ ≤ 1) (hX : X ≤ Δ) :
    (-2 * C * (B + Δ)) / ρ + C * (ρ⁻¹ + R₀) * (B + X) ≤ 0 := by
  have hinv : R₀ ≤ ρ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hρ).2 (by nlinarith)
  have hp : C * (ρ⁻¹ + R₀) * (B + X) ≤ C * (ρ⁻¹ + R₀) * (B + Δ) := by
    gcongr
  have hq : C * (ρ⁻¹ + R₀) * (B + Δ) ≤ 2 * C * (B + Δ) / ρ := by
    calc
      _ ≤ C * (ρ⁻¹ + ρ⁻¹) * (B + Δ) := by gcongr
      _ = _ := by ring
  have hneg : (-2 * C * (B + Δ)) / ρ = -(2 * C * (B + Δ) / ρ) := by ring
  rw [hneg]
  linarith

/-- The shrinking-radius energy inequality closes without assuming the bootstrap conclusion. -/
theorem close_energy_estimate
    (X X' Y : ℝ → ℝ) (C B Δ r ρ₀ S R₀ : ℝ)
    (hC : 0 < C) (hB : 0 ≤ B) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : 0 < r) (hρ : 0 < ρ₀) (hS : 0 ≤ S) (hR : 0 ≤ R₀)
    (hdecay : 2 * C * (B + Δ) * S ≤ ρ₀ / 2) (hscale : ρ₀ * R₀ ≤ 1)
    (hsmall : 2 * r * exp (3 * C * S) ≤ Δ / 2)
    (hcont : ContinuousOn X (Icc 0 S)) (hinit : X 0 ≤ 2 * r)
    (hder : ∀ t ∈ Ico 0 S, HasDerivAt X (X' t) t)
    (hY : ∀ t ∈ Ico 0 S, 0 ≤ Y t)
    (hineq : ∀ t ∈ Ico 0 S,
      X' t ≤ C * (X t + (X t) ^ 2 + r) +
        ((-2 * C * (B + Δ)) / (ρ₀ - 2 * C * (B + Δ) * t) +
          C * ((ρ₀ - 2 * C * (B + Δ) * t)⁻¹ + R₀) * (B + X t)) * Y t) :
    ∀ t ∈ Icc 0 S, X t ≤ 2 * r * exp (3 * C * t) ∧ X t ≤ Δ / 2 := by
  let F : ℝ → ℝ := fun t => 2 * r * exp (3 * C * t)
  have hF (t : ℝ) : HasDerivAt F (3 * C * F t) t := by
    have hlin : HasDerivAt (fun s : ℝ => 3 * C * s) (3 * C) t := by
      simpa using (hasDerivAt_id t).const_mul (3 * C)
    change HasDerivAt (fun s => 2 * r * exp (3 * C * s))
      (3 * C * (2 * r * exp (3 * C * t))) t
    exact (hlin.exp.const_mul (2 * r)).congr_deriv (by ring)
  have hFle (t : ℝ) (ht : t ∈ Icc 0 S) : F t ≤ Δ / 2 := by
    calc
      F t ≤ 2 * r * exp (3 * C * S) := by dsimp [F]; gcongr; exact ht.2
      _ ≤ _ := hsmall
  have hFp (t : ℝ) : 0 < F t := by dsimp [F]; positivity
  have hFbase (t : ℝ) (ht : 0 ≤ t) : 2 * r ≤ F t := by
    have he : 1 ≤ exp (3 * C * t) := one_le_exp_iff.mpr (by positivity)
    dsimp [F]
    nlinarith
  have hbound : ∀ t ∈ Icc 0 S, X t ≤ F t := by
    apply image_le_of_deriv_right_lt_deriv_boundary hcont
      (fun t ht => (hder t ht).hasDerivWithinAt)
    · simpa only [F, mul_zero, exp_zero, mul_one] using hinit
    · exact hF
    · intro t ht hXF
      have htc : t ∈ Icc 0 S := ⟨ht.1, ht.2.le⟩
      have hrad := radius_bounds C B Δ ρ₀ S R₀ hC.le hB hΔ.le hρ hS hR hdecay hscale t htc
      have hloss := shrinking_radius_cancels_loss C B Δ _ R₀ (X t)
        hC.le hB hΔ.le hrad.2.1 hR hrad.2.2 (by rw [hXF]; linarith [hFle t htc])
      have hlossY := mul_nonpos_of_nonpos_of_nonneg hloss (hY t ht)
      have hmain := hineq t ht
      have hFt := hFp t
      have hFΔ := hFle t htc
      have hFr := hFbase t ht.1
      rw [hXF] at hmain hlossY
      have hFsq : (F t) ^ 2 ≤ F t := by nlinarith
      have hCsq := mul_le_mul_of_nonneg_left hFsq hC.le
      have hCr := mul_le_mul_of_nonneg_left hFr hC.le
      have hpos := mul_pos hC hFt
      nlinarith
  intro t ht
  exact ⟨hbound t ht, (hbound t ht).trans (hFle t ht)⟩

/-- Uniform stability from a quadratic differential inequality and small initial error. -/
theorem quadratic_stability (X X' : ℝ → ℝ) (C ε S : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hS : 0 ≤ S)
    (hsmall : 2 * ε * exp (3 * C * S) ≤ 1 / 2)
    (hcont : ContinuousOn X (Icc 0 S)) (hinit : X 0 ≤ ε)
    (hder : ∀ t ∈ Ico 0 S, HasDerivAt X (X' t) t)
    (hineq : ∀ t ∈ Ico 0 S, X' t ≤ C * (X t + (X t) ^ 2)) :
    ∀ t ∈ Icc 0 S, X t ≤ 2 * ε * exp (3 * C * S) := by
  have hρ : 0 < 4 * C * S + 1 := by positivity
  have h := close_energy_estimate X X' (fun _ => 0) C 0 1 ε (4 * C * S + 1) S 0
    hC (by norm_num) (by norm_num) (by norm_num) hε hρ hS (by norm_num)
    (by nlinarith) (by simp) hsmall hcont (by linarith) hder
    (fun _ _ => le_rfl) (fun t ht => by
      have hi := hineq t ht
      simp only [mul_zero, add_zero]
      nlinarith)
  intro t ht
  exact (h t ht).1.trans (by gcongr; exact ht.2)

end EulerEnergyBootstrap

end

section

namespace EulerEnergyParameters

open Real EulerGevreyCutoff

theorem exponential_error_small (z : ℝ) (hz : 256 ≤ z) :
    exp (-z) ≤ 1 / (8 * z ^ 3) := by
  have hz0 : 0 < z := by linarith
  have h := factorial_decay 4 z hz0.le
  norm_num only [Nat.factorial, Nat.cast_ofNat] at h
  apply (le_div_iff₀ (show 0 < 8 * z ^ 3 by positivity)).2
  have hm := mul_le_mul_of_nonneg_right (show (192 : ℝ) ≤ z by linarith)
    (show 0 ≤ z ^ 3 * exp (-z) by positivity)
  nlinarith

theorem radius_budget (z C B ρ₀ S : ℝ) (hz : 256 ≤ z)
    (_hC : 0 ≤ C) (hCz : C ≤ z) (hB : 0 ≤ B) (hBz : B ≤ 1 / (8 * z ^ 3))
    (hρ : 1 / z ^ 2 ≤ ρ₀) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    2 * C * (B + exp (-z)) * S ≤ ρ₀ / 2 := by
  have hz0 : 0 < z := by linarith
  have he := exponential_error_small z hz
  calc
    _ ≤ 2 * z * (1 / (8 * z ^ 3) + 1 / (8 * z ^ 3)) * 1 := by gcongr
    _ = (1 / z ^ 2) / 2 := by field_simp; ring
    _ ≤ ρ₀ / 2 := by linarith

theorem residual_beats_amplification (z C S L : ℝ) (hz : 256 ≤ z)
    (hC : 0 ≤ C) (hCz : C ≤ z) (_hS : 0 ≤ S) (hS1 : S ≤ 1) (hL : 1 ≤ L) :
    2 * exp (-(7 / 10) * z ^ 2 * L) * exp (3 * C * S) ≤ exp (-z) / 2 := by
  have hz0 : 0 < z := by linarith
  have hCS : C * S ≤ z := (mul_le_mul_of_nonneg_left hS1 hC).trans (by simpa using hCz)
  have hLz := mul_le_mul_of_nonneg_left hL (show 0 ≤ (7 / 10 : ℝ) * z ^ 2 by positivity)
  have hlog : -(7 / 10) * z ^ 2 * L + 3 * C * S ≤ -2 * z := by nlinarith
  have hprod : exp (-(7 / 10) * z ^ 2 * L) * exp (3 * C * S) ≤ exp (-2 * z) := by
    rw [← exp_add]
    exact exp_le_exp.mpr hlog
  have he : exp (-z) ≤ 1 / 4 := by
    have hh : 4 ≤ exp z := by linarith [add_one_le_exp z]
    simpa only [exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hh
  have heq : exp (-2 * z) = exp (-z) ^ 2 := by
    rw [show -2 * z = -z + -z by ring, exp_add, pow_two]
  rw [heq] at hprod
  nlinarith [exp_pos (-z)]

theorem frequency_transport_budget (k θ : ℝ) (hk : 1 ≤ k) (hθ : θ ≤ 1 / 4)
    (hz : 8 ≤ k ^ (θ / 2)) :
    k ^ (-(1 / 2 : ℝ)) ≤ 1 / (8 * (k ^ (θ / 2)) ^ 3) := by
  have hk0 : 0 < k := by linarith
  have hz0 : 0 < k ^ (θ / 2) := rpow_pos_of_pos hk0 _
  have hp : (k ^ (θ / 2)) ^ 4 ≤ k ^ (1 / 2 : ℝ) := by
    rw [← rpow_natCast _ 4, ← rpow_mul hk0.le]
    exact rpow_le_rpow_of_exponent_le hk (by norm_num; nlinarith)
  rw [rpow_neg hk0.le]
  calc
    _ ≤ ((k ^ (θ / 2)) ^ 4)⁻¹ := inv_anti₀ (by positivity) hp
    _ ≤ 1 / (8 * (k ^ (θ / 2)) ^ 3) := by
      rw [inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have h := mul_le_mul_of_nonneg_right hz (pow_nonneg hz0.le 3)
      nlinarith

theorem source_coefficient_bound (P k c Q θ : ℝ) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hc : c ≤ Q) (hθ : 0 ≤ θ) (hsmall : P ^ Q ≤ k ^ (θ / 100)) :
    P ^ c ≤ k ^ (θ / 2) := by
  exact (rpow_le_rpow_of_exponent_le hP hc).trans
    (hsmall.trans (rpow_le_rpow_of_exponent_le hk (by nlinarith)))

theorem source_residual_budget (k θ C S : ℝ) (hk : 0 < k)
    (hz : 256 ≤ k ^ (θ / 2)) (hlog : 1 ≤ log k)
    (hC : 0 ≤ C) (hCk : C ≤ k ^ (θ / 2)) (hS : 0 ≤ S) (hS1 : S ≤ 1) :
    2 * exp (-(7 / 10) * k ^ θ * log k) * exp (3 * C * S) ≤
      exp (-(k ^ (θ / 2))) / 2 := by
  have he : (k ^ (θ / 2)) ^ 2 = k ^ θ := by
    rw [← rpow_natCast _ 2, ← rpow_mul hk.le]
    congr 1
    norm_num
  simpa only [he] using residual_beats_amplification (k ^ (θ / 2)) C S (log k)
    hz hC hCk hS hS1 hlog

end EulerEnergyParameters

end

section

namespace EulerWeightedConvolution

open Finset EulerPacketWeights

theorem triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - p.2)
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - l = n' - l' := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - p.2) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      sum_le_sum_of_injOn e hinj himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (ha p.1) (hb p.2))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem external_commutator_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ) (hl : 1 ≤ l)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    weight ρ (j + l) * ((j + l).choose l : ℝ) * a * b ≤
      ρ⁻¹ * (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (external_commutator_ratio_le ρ hρ j l hl)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hp

/-- The full truncated external-commutator convolution has a constant independent of the cutoff. -/
theorem external_commutator_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n,
      weight ρ n * (n.choose (l + 1) : ℝ) * a (l + 1) * b (n - l)) ≤
      ρ⁻¹ * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
        ρ⁻¹ * (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := external_commutator_term ρ hρ (n - (l + 1)) (l + 1) (by omega)
        (a (l + 1)) (b (n - l)) (ha _) (hb _)
      have h1 : n - (l + 1) + (l + 1) = n := by omega
      have h2 : n - (l + 1) + 1 = n - l := by omega
      simpa only [h1, h2] using h
    _ = ρ⁻¹ * (∑ n ∈ range (N + 1), ∑ l ∈ range n,
        (weight ρ (l + 1) * a (l + 1)) *
          (((n - l : ℕ) : ℝ) * weight ρ (n - l) * b (n - l))) := by
      simp only [mul_assoc, mul_sum]
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hρ.le)
      exact triangular_sum_le_product N (fun l => weight ρ l * a l)
        (fun j => (j : ℝ) * weight ρ j * b j)
        (fun l => mul_nonneg (hp l) (ha l))
        (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

theorem shifted_triangular_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1), a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  have hi (n : ℕ) : (∑ l ∈ range (n + 1), a l * b (n - l + 1)) =
      (∑ l ∈ range n, a (l + 1) * b (n - l)) + a 0 * b (n + 1) := by
    rw [sum_range_succ']
    congr 1
    apply sum_congr rfl
    intro l hl
    have : n - (l + 1) + 1 = n - l := by have := mem_range.mp hl; omega
    rw [this]
  simp_rw [hi]
  rw [sum_add_distrib]
  have hrest : (∑ n ∈ range N, ∑ l ∈ range n, a (l + 1) * b (n - l)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    apply le_trans _ (triangular_sum_le_product N a b ha hb)
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro n _ _
    exact sum_nonneg (fun l _ => mul_nonneg (ha _) (hb _))
  have ha0 : a 0 ≤ ∑ l ∈ range (N + 1), a l :=
    single_le_sum (fun l _ => ha l) (mem_range.mpr (by omega))
  have hsum : (∑ n ∈ range N, b (n + 1)) ≤ ∑ j ∈ range (N + 1), b j := by
    rw [sum_range_succ']
    linarith [hb 0]
  have hfirst : (∑ n ∈ range N, a 0 * b (n + 1)) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
    rw [← mul_sum]
    exact mul_le_mul ha0 hsum (sum_nonneg (fun n _ => hb _))
      (sum_nonneg (fun n _ => ha _))
  nlinarith

theorem shifted_source_term (ρ : ℝ) (hρ : 0 < ρ) (j l : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) * a * b ≤
      (weight ρ l * a) * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * b) := by
  have hden : 0 < weight ρ l * ((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) := by
    have h1 := weight_pos hρ l
    have h2 := weight_pos hρ (j + 1)
    positivity
  have h := (div_le_iff₀ hden).mp (shifted_source_ratio_le_one ρ hρ.ne' j l)
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h ha) hb
  simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using hp

/-- The pressure-source derivative shift sums with a cutoff-independent constant. -/
theorem shifted_source_sum (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range N, ∑ l ∈ range (n + 1),
      ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * (n.choose l : ℝ) * a l * b (n - l + 1)) ≤
      2 * (∑ l ∈ range (N + 1), weight ρ l * a l) *
        (∑ j ∈ range (N + 1), (j : ℝ) * weight ρ j * b j) := by
  have hp : ∀ n, 0 ≤ weight ρ n := fun n => (weight_pos hρ n).le
  calc
    _ ≤ ∑ n ∈ range N, ∑ l ∈ range (n + 1),
        (weight ρ l * a l) * (((n - l + 1 : ℕ) : ℝ) * weight ρ (n - l + 1) * b (n - l + 1)) := by
      apply sum_le_sum
      intro n _
      apply sum_le_sum
      intro l hl
      have hln := mem_range.mp hl
      have h := shifted_source_term ρ hρ (n - l) l (a l) (b (n - l + 1)) (ha _) (hb _)
      have he : n - l + l = n := by omega
      simpa only [he] using h
    _ ≤ _ := shifted_triangular_sum_le_product N (fun l => weight ρ l * a l)
      (fun j => (j : ℝ) * weight ρ j * b j)
      (fun l => mul_nonneg (hp l) (ha l))
      (fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (hp j)) (hb j))

end EulerWeightedConvolution

end

section

namespace EulerWeightedEnergy

open Finset EulerPacketWeights

theorem weight_hasDerivAt (ρ : ℝ → ℝ) (ρ' t : ℝ) (hρ : HasDerivAt ρ ρ' t)
    (hpos : 0 < ρ t) (n : ℕ) :
    HasDerivAt (fun s => weight (ρ s) n)
      ((ρ' / ρ t) * (n : ℝ) * weight (ρ t) n) t := by
  have he : ((n : ℝ) * (ρ t) ^ (n - 1) * ρ') / (n.factorial : ℝ) ^ 2 =
      (ρ' / ρ t) * (n : ℝ) * weight (ρ t) n := by
    cases n with
    | zero => simp
    | succ n =>
      simp only [weight, Nat.succ_sub_one, pow_succ, Nat.cast_add, Nat.cast_one]
      field_simp [hpos.ne', factorial_cast_ne_zero]
  exact ((hρ.pow n).div_const ((n.factorial : ℝ) ^ 2)).congr_deriv he

/-- Exact differentiation of the finite weighted Gevrey energy, including radius loss. -/
theorem finite_weighted_energy_hasDerivAt
    (ρ : ℝ → ℝ) (ρ' t : ℝ) (hρ : HasDerivAt ρ ρ' t) (hpos : 0 < ρ t)
    (E : ℕ → ℝ → ℝ) (E' : ℕ → ℝ) (N : ℕ)
    (hE : ∀ n ∈ range (N + 1), HasDerivAt (E n) (E' n) t) :
    HasDerivAt (fun s => ∑ n ∈ range (N + 1), weight (ρ s) n * E n s)
      ((∑ n ∈ range (N + 1), weight (ρ t) n * E' n) +
        (ρ' / ρ t) * ∑ n ∈ range (N + 1), (n : ℝ) * weight (ρ t) n * E n t) t := by
  have h : HasDerivAt (fun s => ∑ n ∈ range (N + 1), weight (ρ s) n * E n s)
      (∑ n ∈ range (N + 1), ((ρ' / ρ t) * (n : ℝ) * weight (ρ t) n * E n t +
        weight (ρ t) n * E' n)) t := by
    exact HasDerivAt.fun_sum (u := range (N + 1))
      (fun n hn => (weight_hasDerivAt ρ ρ' t hρ hpos n).fun_mul (hE n hn))
  apply h.congr_deriv
  rw [sum_add_distrib]
  simp only [mul_assoc, mul_sum]
  ring

end EulerWeightedEnergy

end

section

namespace EulerGraphPullback

open InnerProductSpace Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The linear graph carrying the oscillating phase. -/
def graphMap (k : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.id ℝ E).prod (k • toDual ℝ E m)

/-- The constant lifted differential direction associated with a spatial vector. -/
def liftedDirection (κ : ℝ) (m : E) : E →L[ℝ] (E × ℝ) :=
  (κ • ContinuousLinearMap.id ℝ E).prod (toDual ℝ E m)

theorem graphMap_apply (k : ℝ) (m v : E) : graphMap k m v = (v, k * ⟪m, v⟫_ℝ) := rfl

theorem liftedDirection_apply (κ : ℝ) (m v : E) :
    liftedDirection κ m v = (κ • v, ⟪m, v⟫_ℝ) := rfl

theorem graph_direction_identity (k κ : ℝ) (hκ : k * κ = 1) (m v : E) :
    graphMap k m v = k • liftedDirection κ m v := by
  rw [graphMap_apply, liftedDirection_apply]
  ext <;> simp [smul_smul, hκ]

theorem graph_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × ℝ → F) (k κ : ℝ) (hκ : k * κ = 1) (m x v : E)
    (hf : DifferentiableAt ℝ f (graphMap k m x)) :
    fderiv ℝ (fun y => f (graphMap k m y)) x v =
      k • fderiv ℝ f (graphMap k m x) (liftedDirection κ m v) := by
  have h : HasFDerivAt (fun y => f (graphMap k m y))
      ((fderiv ℝ f (graphMap k m x)).comp (graphMap k m)) x :=
    hf.hasFDerivAt.comp x (graphMap k m).hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, graph_direction_identity k κ hκ m v, map_smul]

/-- A smooth vector field with symmetric derivative has a genuine smooth scalar potential. -/
theorem smooth_gradient_potential (v : E → E) (hv : ContDiff ℝ ∞ v)
    (hsymm : ∀ x a b, ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ) :
    ∃ p : E → ℝ, ContDiff ℝ ∞ p ∧ ∀ x, gradient p x = v x := by
  let form : E → E →L[ℝ] ℝ := fun x => toDual ℝ E (v x)
  have hω : ContDiff ℝ ∞ form := (toDual ℝ E).toContinuousLinearEquiv.contDiff.comp hv
  have hωd (x : E) : HasFDerivAt form
      ((toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ v x)) x :=
    (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      ((hv.differentiable (by simp)) x).hasFDerivAt
  obtain ⟨p, hp⟩ := (convex_univ : Convex ℝ (univ : Set E)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hω.differentiable (by simp)).differentiableOn (fun x _ a b => by
      rw [(hωd x).fderiv]
      change ⟪fderiv ℝ v x a, b⟫_ℝ = ⟪fderiv ℝ v x b, a⟫_ℝ
      exact hsymm x a b)
  have hp' (x : E) : HasFDerivAt p (form x) x := hp x (mem_univ _)
  have hpd : Differentiable ℝ p := fun x => (hp' x).differentiableAt
  have hpf : fderiv ℝ p = form := funext (fun x => (hp' x).fderiv)
  refine ⟨p, ?_, ?_⟩
  · rw [contDiff_infty_iff_fderiv]
    exact ⟨hpd, by rwa [hpf]⟩
  · intro x
    rw [gradient, (hp' x).fderiv]
    exact (toDual ℝ E).symm_apply_apply (v x)

/-- Closedness for the lifted derivatives becomes a scalar pressure potential on the graph. -/
theorem lifted_closed_field_has_graph_potential (p : E × ℝ → E)
    (hp : ContDiff ℝ ∞ p) (k κ : ℝ) (hκ : k * κ = 1) (m : E)
    (hclosed : ∀ z a b,
      ⟪fderiv ℝ p z (liftedDirection κ m a), b⟫_ℝ =
        ⟪fderiv ℝ p z (liftedDirection κ m b), a⟫_ℝ) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧
      ∀ x, gradient q x = κ • p (graphMap k m x) := by
  let v : E → E := fun x => κ • p (graphMap k m x)
  have hv : ContDiff ℝ ∞ v := (hp.comp (graphMap k m).contDiff).const_smul κ
  apply smooth_gradient_potential v hv
  intro x a b
  have hg := (hp.differentiable (by simp)) (graphMap k m x)
  have hd : fderiv ℝ v x = κ • fderiv ℝ (fun y => p (graphMap k m y)) x := by
    exact ((hg.comp x (graphMap k m).differentiableAt).hasFDerivAt.const_smul κ).fderiv
  rw [hd]
  simp only [smul_apply, real_inner_smul_left, graph_fderiv p k κ hκ m x a hg,
    graph_fderiv p k κ hκ m x b hg]
  rw [hclosed]

end EulerGraphPullback

end

section

namespace EulerBreakdownCriterion

open Filter Set EulerSmoothLimit
open scoped Topology

theorem no_escape_near_compact_trajectory
    {E : Type*} [NormedAddCommGroup E]
    (reference : ℝ → E) (samples : ℕ → E) (times errors : ℕ → ℝ) (S : ℝ)
    (hc : ContinuousOn reference (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S)
    (he : Tendsto errors atTop (nhds 0))
    (hd : ∀ᶠ n in atTop, ‖samples n - reference (times n)‖ ≤ errors n) :
    ¬ Tendsto (fun n => ‖samples n‖) atTop atTop := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  intro hg
  have hε : ∀ᶠ n in atTop, errors n < 1 := he.eventually (gt_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ n in atTop, C + 2 ≤ ‖samples n‖ :=
    hg.eventually (eventually_ge_atTop (C + 2))
  obtain ⟨n, hnε, hnlarge, hnd⟩ := (hε.and (hlarge.and hd)).exists
  have hnorm : ‖samples n‖ ≤ ‖samples n - reference (times n)‖ + ‖reference (times n)‖ := by
    calc
      _ = ‖(samples n - reference (times n)) + reference (times n)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have href := hC (times n) (ht n)
  have herr := hnd
  linarith

/-- The final gradient contradiction, expressed with actual Fréchet derivatives at the origin. -/
theorem no_gradient_escape_under_C1_comparison
    (u : ℝ → Space → Space) (U : ℕ → ℝ → Space → Space)
    (times errors : ℕ → ℝ) (S : ℝ)
    (hc : ContinuousOn (fun t => fderiv ℝ (u t) 0) (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S)
    (he : Tendsto errors atTop (nhds 0))
    (hd : ∀ n, ‖fderiv ℝ (U n (times n)) 0 - fderiv ℝ (u (times n)) 0‖ ≤ errors n) :
    ¬ Tendsto (fun n => ‖fderiv ℝ (U n (times n)) 0‖) atTop atTop :=
  no_escape_near_compact_trajectory (fun t => fderiv ℝ (u t) 0)
    (fun n => fderiv ℝ (U n (times n)) 0) times errors S hc ht he (Eventually.of_forall hd)

end EulerBreakdownCriterion

end

section

namespace EulerSobolevBreakdown

open EulerSmoothLimit EulerSobolev EulerSmoothSobolev EulerEnergyBootstrap
open Filter Set MeasureTheory
open scoped ContDiff Topology

/-- The final comparison argument, with an actual physical H³ norm. A quadratic
energy estimate and vanishing initial error rule out divergent origin gradients
against a smooth reference solution on a compact time interval. -/
theorem no_gradient_escape_from_sobolev_energy
    (u : ℝ → Space → Space) (U : ℕ → ℝ → Space → Space)
    (X X' : ℕ → ℝ → ℝ) (ε times : ℕ → ℝ) (C S : ℝ)
    (hC : 0 < C) (hS : 0 ≤ S) (hε : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (nhds 0))
    (hu : ∀ t ∈ Icc 0 S, ContDiff ℝ ∞ (u t))
    (hU : ∀ n t, t ∈ Icc 0 S → ContDiff ℝ ∞ (U n t))
    (hL2 : ∀ n t, t ∈ Icc 0 S → ∀ j ≤ 3,
      MemLp (iteratedFDeriv ℝ j (fun x => U n t x - u t x)) 2 volume)
    (hmajor : ∀ n t, t ∈ Icc 0 S →
      realTensorSobolevNorm 3 3 (fun x => U n t x - u t x) ≤ X n t)
    (hcont : ∀ n, ContinuousOn (X n) (Icc 0 S))
    (hinit : ∀ n, X n 0 ≤ ε n)
    (hder : ∀ n t, t ∈ Ico 0 S → HasDerivAt (X n) (X' n t) t)
    (hineq : ∀ n t, t ∈ Ico 0 S → X' n t ≤ C * (X n t + (X n t) ^ 2))
    (href : ContinuousOn (fun t => fderiv ℝ (u t) 0) (Icc 0 S))
    (ht : ∀ n, times n ∈ Icc 0 S) :
    ¬ Tendsto (fun n => ‖fderiv ℝ (U n (times n)) 0‖) atTop atTop := by
  let A : ℝ := 9 * smoothEmbeddingConstant
  let errors : ℕ → ℝ := fun n => A * (2 * ε n * Real.exp (3 * C * S))
  have hA : 0 ≤ A := mul_nonneg (by norm_num) smoothEmbeddingConstant_nonneg
  have hlim : Tendsto (fun n => 2 * ε n * Real.exp (3 * C * S)) atTop (nhds 0) := by
    simpa using (hεlim.const_mul 2).mul_const (Real.exp (3 * C * S))
  have helim : Tendsto errors atTop (nhds 0) := by
    simpa [errors] using hlim.const_mul A
  have hsmall : ∀ᶠ n in atTop, 2 * ε n * Real.exp (3 * C * S) ≤ 1 / 2 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply EulerBreakdownCriterion.no_escape_near_compact_trajectory
    (fun t => fderiv ℝ (u t) 0) (fun n => fderiv ℝ (U n (times n)) 0)
    times errors S href ht helim
  filter_upwards [hsmall] with n hn
  have hX := quadratic_stability (X n) (X' n) C (ε n) S hC (hε n) hS hn
    (hcont n) (hinit n) (hder n) (hineq n) (times n) (ht n)
  have hs : ContDiff ℝ ∞ (fun x => U n (times n) x - u (times n) x) :=
    (hU n (times n) (ht n)).sub (hu (times n) (ht n))
  have hsob := real_smooth_fderiv_le_H3 3 _ hs (hL2 n (times n) (ht n)) 0
  have hdiff : fderiv ℝ (fun x => U n (times n) x - u (times n) x) 0 =
      fderiv ℝ (U n (times n)) 0 - fderiv ℝ (u (times n)) 0 :=
    (((hU n (times n) (ht n)).differentiable (by simp) 0).hasFDerivAt.sub
      ((hu (times n) (ht n)).differentiable (by simp) 0).hasFDerivAt).fderiv
  rw [hdiff] at hsob
  exact hsob.trans (mul_le_mul_of_nonneg_left
    ((hmajor n (times n) (ht n)).trans hX) hA)

end EulerSobolevBreakdown

end

section

namespace EulerDeformationVolume

open Matrix Set MeasureTheory

/-- Jacobi's formula along the three-dimensional deformation equation, including
singular matrices; no inverse determinant is used. -/
theorem determinant_hasDerivAt (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (hF : ∀ i j, HasDerivAt (fun s => F s i j) ((M t * F t) i j) t) :
    HasDerivAt (fun s => (F s).det) ((M t).trace * (F t).det) t := by
  have h := (((((hF 0 0).mul (hF 1 1)).mul (hF 2 2)).sub
    (((hF 0 0).mul (hF 1 2)).mul (hF 2 1))).sub
    (((hF 0 1).mul (hF 1 0)).mul (hF 2 2))).add
    (((hF 0 1).mul (hF 1 2)).mul (hF 2 0))
  have h' := (h.add (((hF 0 2).mul (hF 1 0)).mul (hF 2 1))).sub
    (((hF 0 2).mul (hF 1 1)).mul (hF 2 0))
  have hd := h'.congr_deriv (g' := (M t).trace * (F t).det) (by
    simp only [Pi.mul_apply, mul_apply, Fin.sum_univ_three, trace, diag, det_fin_three]
    ring)
  convert hd using 1 <;> first | rfl | (funext s; exact det_fin_three (F s))

/-- A trace-free velocity gradient preserves the actual deformation determinant. -/
theorem determinant_eq_one (F M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ)
    (hF : ∀ t ∈ Icc a b, ∀ i j,
      HasDerivAt (fun s => F s i j) ((M t * F t) i j) t)
    (htrace : ∀ t ∈ Ico a b, (M t).trace = 0) (hinit : (F a).det = 1) :
    ∀ t ∈ Icc a b, (F t).det = 1 := by
  have hc : ContinuousOn (fun t => (F t).det) (Icc a b) :=
    fun t ht => (determinant_hasDerivAt F M t (hF t ht)).continuousAt.continuousWithinAt
  have hz : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => (F s).det) 0 (Ici t) t := by
    intro t ht
    have hd := determinant_hasDerivAt F M t (hF t ⟨ht.1, ht.2.le⟩)
    rw [htrace t ht, zero_mul] at hd
    exact hd.hasDerivWithinAt
  intro t ht
  exact (constant_of_has_deriv_right_zero hc hz t ht).trans hinit

section ChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bijective differentiable map with unit Jacobian preserves Lebesgue measure. -/
theorem measurePreserving_of_det_one (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E → E) (F : E → E →L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f (F x) x) (hbij : Function.Bijective f)
    (hdet : ∀ x, (F x).det = 1) : MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable, ?_⟩
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := (univ : Set E)) (f' := F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    image_univ, hbij.2.range_eq] at hm
  change Measure.map f (μ.withDensity 1) = μ at hm
  rwa [withDensity_one] at hm

end ChangeOfVariables

end EulerDeformationVolume

end

section

namespace EulerCylinderGraphTrace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open Set
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (0 < period)] [CompleteSpace F] in
theorem angular_hasDerivAt (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : Vector3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x, (s : AddCircle period)))
      (fieldDerivative period (0, 1) f (x, (t : AddCircle period))) t := by
  have hd := ((hf 0).differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have he := fderiv_localFieldLift_cover period f (x, t)
  change fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0 =
    fderiv ℝ (localFieldLift period f 0) (x, t) at he
  change HasDerivAt _ ((fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0) (0, 1)) t
  rw [he]
  simpa [Function.comp_def, localFieldLift] using hd

/-- Point evaluation in the periodic coordinate costs one angular derivative,
with a bound independent of the chosen phase. -/
theorem cylinder_pointwise_trace (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : Vector3) (θ : AddCircle period) :
    ‖f (x, θ)‖ ^ 2 ≤
      (2 / period) * (∫ s : AddCircle period, ‖f (x, s)‖ ^ 2) +
      (2 * period) * (∫ s : AddCircle period,
        ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2) := by
  have hT : 0 < period := Fact.out
  let θ₀ := AddCircle.equivIco period 0 θ
  have hθ : (θ₀ : ℝ) ∈ Icc 0 period := by
    have hh := θ₀.property
    simp only [zero_add] at hh
    exact ⟨hh.1, hh.2.le⟩
  have hcont : Continuous (fun s : ℝ => fieldDerivative period (0, 1) f
      (x, (s : AddCircle period))) := by
    exact (smoothField_continuous period _
      (fieldDerivative_smooth period (0, 1) f hf)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' period))
  have h := EulerIntervalTrace.pointwise_H1_trace
    (fun s : ℝ => f (x, (s : AddCircle period)))
    (fun s : ℝ => fieldDerivative period (0, 1) f (x, (s : AddCircle period)))
    0 period hT hcont.continuousOn (fun s _ => angular_hasDerivAt period f hf x s)
    θ₀ hθ
  have hcoe : ((θ₀ : ℝ) : AddCircle period) = θ := AddCircle.coe_equivIco
  rw [hcoe] at h
  have hfi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖f (x, s)‖ ^ 2)
  have hdi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2)
  simp only [zero_add] at hfi hdi
  simpa only [sub_zero, hfi, hdi] using h

/-- Pullback to any continuous phase graph preserves square integrability.
The estimate has no dependence on the phase frequency. -/
theorem graph_memLp_and_energy_bound (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : MemLp f 2 (liftMeasure period))
    (hdL2 : MemLp (fieldDerivative period (0, 1) f) 2 (liftMeasure period))
    (θ : Vector3 → AddCircle period) (hθ : Continuous θ) :
    MemLp (fun x => f (x, θ x)) 2 volume ∧
      (∫ x : Vector3, ‖f (x, θ x)‖ ^ 2) ≤
        (2 / period) * (∫ z, ‖f z‖ ^ 2 ∂liftMeasure period) +
        (2 * period) * (∫ z, ‖fieldDerivative period (0, 1) f z‖ ^ 2
          ∂liftMeasure period) := by
  have hfc : Continuous (fun x => f (x, θ x)) :=
    (smoothField_continuous period f hf).comp (continuous_id.prodMk hθ)
  have hfint := hfL2.norm.integrable_sq
  have hdint := hdL2.norm.integrable_sq
  have hi := (hfint.integral_prod_left.const_mul (2 / period)).add
    (hdint.integral_prod_left.const_mul (2 * period))
  have hgraph : Integrable (fun x => ‖f (x, θ x)‖ ^ 2) volume := by
    apply hi.mono' (hfc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖f (x, θ x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (x, θ x)‖)]
    exact cylinder_pointwise_trace period f hf x (θ x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr hgraph, ?_⟩
  have hbound := integral_mono hgraph hi (fun x => cylinder_pointwise_trace period f hf x (θ x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hfint.integral_prod_left.const_mul (2 / period))
    (hdint.integral_prod_left.const_mul (2 * period)), integral_const_mul, integral_const_mul,
    integral_integral hfint, integral_integral hdint] at hbound
  exact hbound

end EulerCylinderGraphTrace

end

section

namespace EulerLiftedEulerAlgebra

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Forget the angle while retaining time and the particle label. -/
def parameterProjection : (ℝ × (E × ℝ)) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)))

/-- The velocity in particle coordinates associated with the lifted unknown. -/
def liftedVelocity (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ)) : E :=
  κ • F (q.1, q.2.1) (z q)

omit [CompleteSpace E] in
theorem liftedVelocity_fderiv (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ))
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF (q.1, q.2.1)) (hz : HasFDerivAt z Dz q)
    (v : ℝ × (E × ℝ)) :
    fderiv ℝ (liftedVelocity κ F z) q v =
      κ • (DF (v.1, v.2.1) (z q) + F (q.1, q.2.1) (Dz v)) := by
  have hp : HasFDerivAt (fun r : ℝ × (E × ℝ) => F (r.1, r.2.1))
      (DF.comp parameterProjection) q := hF.comp q (parameterProjection (E := E)).hasFDerivAt
  have hd : HasFDerivAt (fun r => κ • F (r.1, r.2.1) (z r))
      (κ • ((F (q.1, q.2.1)).comp Dz + (DF.comp parameterProjection).flip (z q))) q :=
    (hp.clm_apply hz).const_smul κ
  rw [show liftedVelocity κ F z = (fun r => κ • F (r.1, r.2.1) (z r)) from rfl,
    hd.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, parameterProjection, ContinuousLinearMap.prod_apply]
  congr 1
  exact add_comm _ _

/-- Exact transformation of the normalized Euler residual into the lifted
equation (16), using the actual derivatives of F and z. -/
theorem lifted_euler_residual (κ : ℝ) (F : ℝ × E → E →L[ℝ] E)
    (z : ℝ × (E × ℝ) → E) (q : ℝ × (E × ℝ))
    (DF : (ℝ × E) →L[ℝ] (E →L[ℝ] E)) (Dz : (ℝ × (E × ℝ)) →L[ℝ] E)
    (hF : HasFDerivAt F DF (q.1, q.2.1)) (hz : HasFDerivAt z Dz q)
    (A : E ≃L[ℝ] E) (hA : F (q.1, q.2.1) = A.toContinuousLinearMap)
    (m p : E) :
    fderiv ℝ (liftedVelocity κ F z) q (1, (0, 0)) +
      DF (1, 0) (A.symm (liftedVelocity κ F z q)) +
      fderiv ℝ (liftedVelocity κ F z) q (0, (κ • z q, ⟪m, z q⟫_ℝ)) +
      κ • A.symm.toContinuousLinearMap.adjoint p =
    κ • A (Dz (1, (0, 0)) + (2 : ℝ) • A.symm (DF (1, 0) (z q)) +
      Dz (0, (κ • z q, ⟪m, z q⟫_ℝ)) +
      κ • A.symm (DF (0, z q) (z q)) +
      A.symm (A.symm.toContinuousLinearMap.adjoint p)) := by
  rw [liftedVelocity_fderiv κ F z q DF Dz hF hz,
    liftedVelocity_fderiv κ F z q DF Dz hF hz]
  have harg : ((0 : ℝ), κ • z q) = κ • ((0 : ℝ), z q) := by simp
  simp only [liftedVelocity, hA, ContinuousLinearEquiv.coe_coe, map_smul,
    ContinuousLinearEquiv.symm_apply_apply, harg, smul_apply, map_add,
    ContinuousLinearEquiv.apply_symm_apply]
  module

end EulerLiftedEulerAlgebra

end

section

namespace EulerWeightedPressure

open Finset EulerPacketWeights EulerWeightedConvolution EulerGevrey

theorem lower_triangle_sum_le_product (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, a (l + 1) * b (n - (l + 1))) ≤
      (∑ l ∈ range (N + 1), a l) * (∑ j ∈ range (N + 1), b j) := by
  let e : (Σ _n : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 + 1, p.1 - (p.2 + 1))
  have hinj : Set.InjOn e ((range (N + 1)).sigma range) := by
    rintro ⟨n, l⟩ hx ⟨n', l'⟩ hy h
    have hx' := mem_sigma.mp hx
    have hy' := mem_sigma.mp hy
    have hl : l < n := mem_range.mp hx'.2
    have hl' : l' < n' := mem_range.mp hy'.2
    have heq : l + 1 = l' + 1 ∧ n - (l + 1) = n' - (l' + 1) := Prod.mk.inj h
    have hll : l = l' := by omega
    have hnn : n = n' := by omega
    subst l'
    subst n'
    rfl
  have himg : Finset.image e ((range (N + 1)).sigma range) ⊆
      (range (N + 1)) ×ˢ (range (N + 1)) := by
    intro p hp
    obtain ⟨⟨n, l⟩, hx, rfl⟩ := mem_image.mp hp
    have hx' := mem_sigma.mp hx
    have hn := mem_range.mp hx'.1
    have hl := mem_range.mp hx'.2
    change n < N + 1 at hn
    change l < n at hl
    simp only [e, mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ p ∈ (range (N + 1)).sigma range, a (p.2 + 1) * b (p.1 - (p.2 + 1)) :=
      sum_sigma' _ _ _
    _ ≤ ∑ p ∈ (range (N + 1)) ×ˢ (range (N + 1)), a p.1 * b p.2 :=
      sum_le_sum_of_injOn e hinj himg (fun _ _ => le_rfl)
        (fun p _ _ => mul_nonneg (ha p.1) (hb p.2))
    _ = _ := by rw [sum_product, ← sum_mul_sum]

theorem geometric_lower_triangle (q : ℝ) (hq : 0 ≤ q) (hhalf : q ≤ 1 / 2)
    (N : ℕ) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) :
    (∑ n ∈ range (N + 1), ∑ l ∈ range n, q ^ (l + 1) * b (n - (l + 1))) ≤
      (2 * q) * ∑ j ∈ range (N + 1), b j := by
  let a : ℕ → ℝ := fun n => if n = 0 then 0 else q ^ n
  have ha : ∀ n, 0 ≤ a n := fun n => by dsimp [a]; split <;> positivity
  have h := lower_triangle_sum_le_product N a b ha hb
  have hsum : (∑ l ∈ range (N + 1), a l) ≤ 2 * q := by
    rw [sum_range_succ']
    simpa [a] using geometric_tail_le_two_mul q hq hhalf N
  simp only [a, Nat.add_one_ne_zero, ↓reduceIte] at h
  exact h.trans (mul_le_mul_of_nonneg_right hsum (sum_nonneg (fun j _ => hb j)))

theorem shifted_weight_kernel (ρ Rc : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (j l : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ((j + l + 1 : ℕ) : ℝ) * weight ρ (j + l + 1) * ((j + l).choose l : ℝ) *
      (Rc ^ l * (l.factorial : ℝ) ^ 2) * Z ≤
    (ρ * Rc) ^ l * (((j + 1 : ℕ) : ℝ) * weight ρ (j + 1) * Z) := by
  have h := shifted_source_term ρ hρ j l (Rc ^ l * (l.factorial : ℝ) ^ 2) Z
    (by positivity) hZ
  have hw : weight ρ l * (Rc ^ l * (l.factorial : ℝ) ^ 2) = (ρ * Rc) ^ l := by
    unfold weight
    rw [mul_pow]
    field_simp [factorial_cast_ne_zero]
  simpa only [hw] using h

/-- A shifted Gevrey inverse estimate whose constant is independent of truncation.
The positive-order coefficient terms are absorbed, rather than accumulated with order. -/
theorem shifted_weighted_inverse (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc)
    (hM : 1 ≤ M) (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (N : ℕ) (A F Z : ℕ → ℝ) (_hF : ∀ n, 0 ≤ F n) (hZ : ∀ n, 0 ≤ Z n)
    (hA : ∀ l, 1 ≤ l → l ≤ N → A l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hrec : ∀ n ≤ N, Z n ≤ M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)))) :
    (∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * Z n) ≤
      2 * M * ∑ n ∈ range (N + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) * F n := by
  let v : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1)
  have hv : ∀ n, 0 ≤ v n := fun n => mul_nonneg (Nat.cast_nonneg _) (weight_pos hρ _).le
  have hq : 0 ≤ ρ * Rc := mul_nonneg hρ.le hRc
  have hhalf : ρ * Rc ≤ 1 / 2 := by nlinarith
  have hcomm : (∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) ≤
      (2 * (ρ * Rc)) * ∑ j ∈ range (N + 1), v j * Z j := by
    calc
      _ = ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          v n * (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1)) := by
        simp only [mul_sum, mul_assoc]
      _ ≤ ∑ n ∈ range (N + 1), ∑ l ∈ range n,
          (ρ * Rc) ^ (l + 1) * (v (n - (l + 1)) * Z (n - (l + 1))) := by
        apply sum_le_sum
        intro n hn
        apply sum_le_sum
        intro l hl
        have hln := mem_range.mp hl
        have hnN : n ≤ N := by have := mem_range.mp hn; omega
        have hcoeff := hA (l + 1) (by omega) (by omega)
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoeff
            (mul_nonneg (hv n) (Nat.cast_nonneg (n.choose (l + 1))))) (hZ (n - (l + 1)))
        have h2 := shifted_weight_kernel ρ Rc hρ hRc (n - (l + 1)) (l + 1)
          (Z (n - (l + 1))) (hZ _)
        have he : n - (l + 1) + (l + 1) = n := by omega
        dsimp [v] at h1 ⊢
        exact h1.trans (by simpa only [he] using h2)
      _ ≤ _ := geometric_lower_triangle (ρ * Rc) hq hhalf N
        (fun j => v j * Z j) (fun j => mul_nonneg (hv j) (hZ j))
  have hs := sum_le_sum (s := range (N + 1)) (fun n hn =>
    mul_le_mul_of_nonneg_left (hrec n (by have := mem_range.mp hn; omega)) (hv n))
  have hsumid : (∑ n ∈ range (N + 1), v n * (M * (F n + ∑ l ∈ range n,
      (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))))) =
      M * ((∑ n ∈ range (N + 1), v n * F n) +
        ∑ n ∈ range (N + 1), v n * ∑ l ∈ range n,
          (n.choose (l + 1) : ℝ) * A (l + 1) * Z (n - (l + 1))) := by
    simp only [mul_add, sum_add_distrib, mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hsumid] at hs
  have hzsum : 0 ≤ ∑ n ∈ range (N + 1), v n * Z n :=
    sum_nonneg (fun n _ => mul_nonneg (hv n) (hZ n))
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hzsum
  have hcomm' := mul_le_mul_of_nonneg_left hcomm (show 0 ≤ M by linarith)
  change (∑ n ∈ range (N + 1), v n * Z n) ≤ 2 * M * ∑ n ∈ range (N + 1), v n * F n
  nlinarith

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerJetProductBounds

/-- The shifted weighted operator bound for the pressure actually constructed in L². -/
theorem pressure_shifted_weighted_bound (period : ℝ) [Fact (0 < period)]
    {directions : Fin 4 → LiftTangent} {s : ℕ}
    {A : SmoothCoefficient period} {f : LiftL2 period}
    (K : CoefficientJet period directions s A) (J : SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A.coefficient x v) v)
    (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hcM : c⁻¹ ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ s → boundLevel period K l ≤ majorant Rc 0 l) :
    (∑ n ∈ range (s + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) *
      levelNorm period (J.solvePressure K κ m c hc hpos) n) ≤
      2 * M * ∑ n ∈ range (s + 1), ((n + 1 : ℕ) : ℝ) * weight ρ (n + 1) *
        levelNorm period J n := by
  let P := J.solvePressure K κ m c hc hpos
  apply shifted_weighted_inverse ρ Rc M hρ hRc hM hsmall s
    (boundLevel period K) (levelNorm period J) (levelNorm period P)
    (fun _ => levelNorm_nonneg J) (fun _ => levelNorm_nonneg P)
  · intro l hl hs
    simpa only [majorant, Nat.add_zero] using hcoeff l hl hs
  · intro n hn
    apply (pressure_level_recurrence K J κ m c hc hpos hn).trans
    apply mul_le_mul_of_nonneg_right hcM
    apply add_nonneg (levelNorm_nonneg J)
    apply sum_nonneg
    intro l _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (boundLevel_nonneg K)) (levelNorm_nonneg P)

end EulerWeightedPressure

end

section

/-!
Partial verification of algebra in the sample's proposed Euler packet construction.
This file does not prove existence of an Euler packet or finite-time Euler blowup.
The equations assumed below are the finite-dimensional ODEs in the source, not
assumptions that assert the unproved PDE construction.
-/

namespace EulerPacketAlgebra

open Matrix

/-- The ray-amplitude pairing is conserved on the whole interval of the ODE. -/
theorem pairing_conserved {n : Type*} [Fintype n]
    (M : ℝ → Matrix n n ℝ) (m v : ℝ → n → ℝ) (a b : ℝ)
    (hm : ∀ t ∈ Set.Icc a b, m t ⬝ᵥ m t ≠ 0)
    (hmd : ∀ t ∈ Set.Icc a b, ∀ i, HasDerivAt (fun s => m s i)
      ((-(M t).transpose *ᵥ m t) i) t)
    (hvd : ∀ t ∈ Set.Icc a b, ∀ i, HasDerivAt (fun s => v s i)
      ((-(M t *ᵥ v t) + (2 * (m t ⬝ᵥ (M t *ᵥ v t)) /
        (m t ⬝ᵥ m t)) • m t) i) t) :
    ∀ t ∈ Set.Icc a b, m t ⬝ᵥ v t = m a ⬝ᵥ v a := by
  have hp : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => m s ⬝ᵥ v s) 0 t := by
    intro t ht
    apply (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hmd t ht i).mul (hvd t ht i))).congr_deriv
    rw [Finset.sum_add_distrib]
    change ((-(M t).transpose *ᵥ m t) ⬝ᵥ v t) +
      m t ⬝ᵥ (-(M t *ᵥ v t) + (2 * (m t ⬝ᵥ (M t *ᵥ v t)) /
        (m t ⬝ᵥ m t)) • m t) = 0
    rw [neg_mulVec, neg_dotProduct, dotProduct_add, dotProduct_neg, dotProduct_smul]
    rw [dotProduct_comm ((M t).transpose *ᵥ m t) (v t), dotProduct_transpose_mulVec]
    simp only [smul_eq_mul]
    field_simp [hm t ht]
    ring
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hp t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hp t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)

/-- Equation (30), derived from the ideal two-component ODE with its actual coefficients. -/
theorem scalar_equation (β : ℝ) (U V : ℝ → ℝ)
    (hU : ∀ t, HasDerivAt U
      (-2 * V t + 2 * (β * t ^ 2) *
        (((β * t ^ 2) + β) * V t + (-2 * β * t) * U t) /
          (1 + (β * t ^ 2) ^ 2)) t)
    (hV : ∀ t, HasDerivAt V (-U t) t) (t : ℝ) :
    HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * deriv V s)
      (2 * (1 - β * (β * t ^ 2)) * V t) t := by
  have hv : deriv V = fun s => -U s := funext fun s => (hV s).deriv
  rw [hv]
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2)
      (4 * β ^ 2 * t ^ 3) t := by
    apply (((((hasDerivAt_id t).fun_pow 2).const_mul β).fun_pow 2).const_add 1).congr_deriv
    dsimp
    ring
  have hd : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply (hD.mul (hU t).neg).congr_deriv
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- The inversion symmetry used after (30), including the derivative of the transformed solution. -/
theorem inversion_equation (β : ℝ) (V V₁ : ℝ → ℝ)
    (hV : ∀ x, x ≠ 0 → HasDerivAt V (V₁ x) x)
    (hV₁ : ∀ x, x ≠ 0 → HasDerivAt V₁
      (((2 / β - 2 * x ^ 2) * V x - 4 * x ^ 3 * V₁ x) / (1 + x ^ 4)) x)
    (y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun z => V z⁻¹ / z)
      (-V y⁻¹ / y ^ 2 - V₁ y⁻¹ / y ^ 3) y ∧
    HasDerivAt (fun z => (1 + z ^ 4) * (-V z⁻¹ / z ^ 2 - V₁ z⁻¹ / z ^ 3))
      ((2 / β - 2 * y ^ 2) * (V y⁻¹ / y)) y := by
  have hi := hasDerivAt_inv hy
  have h0 := (hV y⁻¹ (inv_ne_zero hy)).comp y hi
  have h1 := (hV₁ y⁻¹ (inv_ne_zero hy)).comp y hi
  have h2 := (hasDerivAt_id y).fun_pow 2
  have h3 := (hasDerivAt_id y).fun_pow 3
  have h4 := ((hasDerivAt_id y).fun_pow 4).const_add 1
  constructor
  · apply (h0.div (hasDerivAt_id y) hy).congr_deriv
    dsimp
    field_simp
    ring
  · apply (h4.mul ((h0.neg.div h2 (pow_ne_zero 2 hy)).sub
      (h1.div h3 (pow_ne_zero 3 hy)))).congr_deriv
    have hd : 1 + (y⁻¹) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    dsimp
    field_simp
    ring

end EulerPacketAlgebra

end

section

/-!
Order estimates for the scalar ODE occurring in equation (30) of the proposed
Euler packet argument.  These are finite-dimensional ODE results only.
-/

namespace EulerPacketGrowth

open Set Filter Real
open scoped Topology

private theorem eventually_nonneg_right
    {f : ℝ → ℝ} {x d : ℝ} (hd : HasDerivAt f d x)
    (hx : 0 ≤ f x) (hboundary : f x = 0 → 0 < d) :
    ∀ᶠ y in 𝓝[>] x, 0 ≤ f y := by
  rcases hx.eq_or_lt with hx | hx
  · have hpos : 0 < d := hboundary hx.symm
    have hslope : ∀ᶠ y in 𝓝[>] x, 0 < slope f x y :=
      (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)) (Ioi_mem_nhds hpos)
    filter_upwards [hslope, self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field, ← hx] at hy
    have : 0 < y - x := sub_pos.mpr hxy
    simpa using ((div_pos_iff_of_pos_right this).mp hy).le
  · exact ((hd.continuousAt.eventually (Ioi_mem_nhds hx)).filter_mono
      nhdsWithin_le_nhds).mono fun _ hy => hy.le

/-- Two differentiable functions remain nonnegative if every boundary point
of the nonnegative quadrant has a strictly inward derivative. -/
theorem pair_nonneg_of_strict_boundary
    {f g df dg : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (hboundary : ∀ t ∈ Ico 0 T, 0 ≤ f t → 0 ≤ g t →
      (f t = 0 → 0 < df t) ∧ (g t = 0 → 0 < dg t)) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  let s : Set ℝ := {t | 0 ≤ f t ∧ 0 ≤ g t}
  have hfc : ContinuousOn f (Icc 0 T) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hs : IsClosed (s ∩ Icc 0 T) := by
    have hpair : ContinuousOn (fun t => (f t, g t)) (Icc 0 T) := hfc.prodMk hgc
    have hc : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
      (isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_const continuous_snd)
    simpa [s, inter_comm] using
      hpair.preimage_isClosed_of_isClosed isClosed_Icc hc
  apply hs.Icc_subset_of_forall_exists_gt ⟨hf0, hg0⟩
  intro t ht y hy
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht.2
  have hb := hboundary t ht.2 ht.1.1 ht.1.2
  have he := (eventually_nonneg_right (hf t hti) ht.1.1 hb.1).and
    (eventually_nonneg_right (hg t hti) ht.1.2 hb.2)
  exact nonempty_of_mem (inter_mem he (Ioc_mem_nhdsGT hy))

/-- Positivity for a cooperative pair of differential inequalities.  The
nonnegative quadrant is invariant; positivity is not an additional hypothesis. -/
theorem cooperative_nonneg_of_bounded
    {f g df dg a b : ℝ → ℝ} {T K : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ K)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ K)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t := by
  have hpert : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc 0 T,
      0 ≤ f t + ε * exp ((K + 1) * t) ∧
        0 ≤ g t + ε * exp ((K + 1) * t) := by
    intro ε hε
    have hed : ∀ t : ℝ, HasDerivAt (fun s => ε * exp ((K + 1) * s))
        ((K + 1) * ε * exp ((K + 1) * t)) t := by
      intro t
      apply ((((hasDerivAt_id t).const_mul (K + 1)).exp).const_mul ε).congr_deriv
      dsimp
      ring
    apply pair_nonneg_of_strict_boundary
      (fun t ht => (hf t ht).add (hed t))
      (fun t ht => (hg t ht).add (hed t))
    · simpa using add_nonneg hf0 hε.le
    · simpa using add_nonneg hg0 hε.le
    · intro t ht hft hgt
      dsimp only [Pi.add_apply] at hft hgt ⊢
      have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
      have hat := ha t hti
      have hbt := hb t hti
      have hεE : 0 < ε * exp ((K + 1) * t) := mul_pos hε (exp_pos _)
      constructor
      · intro _
        have hmul : a t * (-(ε * exp ((K + 1) * t))) ≤ a t * g t :=
          mul_le_mul_of_nonneg_left (by linarith) hat.1
        have hpos : 0 < (K + 1 - a t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith [hat.2]) hεE
        linarith [hdf t hti]
      · intro _
        have hmul : b t * (-(ε * exp ((K + 1) * t))) ≤ b t * f t :=
          mul_le_mul_of_nonneg_left (by linarith) hbt.1
        have hpos : 0 < (K + 1 - b t) * (ε * exp ((K + 1) * t)) :=
          mul_pos (by linarith [hbt.2]) hεE
        linarith [hdg t hti]
  intro t ht
  have hE : exp ((K + 1) * t) ≠ 0 := ne_of_gt (exp_pos _)
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [div_mul_cancel₀ _ hE] using
      (hpert (ε / exp ((K + 1) * t)) (div_pos hε (exp_pos _)) t ht).2

/-- A specialization of cooperative positivity with coefficient bound `2`. -/
theorem cooperative_nonneg
    {f g df dg a b : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (df t) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (dg t) t)
    (hf0 : 0 ≤ f 0) (hg0 : 0 ≤ g 0)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t ∧ a t ≤ 2)
    (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t ∧ b t ≤ 2)
    (hdf : ∀ t ∈ Icc 0 T, a t * g t ≤ df t)
    (hdg : ∀ t ∈ Icc 0 T, b t * f t ≤ dg t) :
    ∀ t ∈ Icc 0 T, 0 ≤ f t ∧ 0 ≤ g t :=
  cooperative_nonneg_of_bounded hf hg hf0 hg0 ha hb hdf hdg

/-- The flux system `V' = F/D`, `F' = c V` dominates the constant-coefficient
system with `D = 2` and `c = 1`.  In particular, its solution is positive and
has a hyperbolic-cosine lower bound, for every nonnegative initial flux. -/
theorem cosh_lower_of_flux_system
    {V F D c : ℝ → ℝ} {T : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : V 0 = 1) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 1 ≤ D t ∧ D t ≤ 2)
    (hc : ∀ t ∈ Icc 0 T, 1 ≤ c t ∧ c t ≤ 2) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧ √2 * sinh (t / √2) ≤ F t := by
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsne : (√2 : ℝ) ≠ 0 := ne_of_gt hspos
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcd : ∀ t : ℝ, HasDerivAt (fun s => cosh (s / √2))
      (sinh (t / √2) / √2) t := by
    intro t
    convert (((hasDerivAt_id t).div_const (√2 : ℝ)).cosh) using 1 <;> simp [div_eq_mul_inv]
  have hsd : ∀ t : ℝ, HasDerivAt (fun s => √2 * sinh (s / √2))
      (cosh (t / √2)) t := by
    intro t
    apply ((((hasDerivAt_id t).div_const (√2 : ℝ)).sinh).const_mul (√2 : ℝ)).congr_deriv
    dsimp
    field_simp
  have hcompare := cooperative_nonneg
    (f := fun t => V t - cosh (t / √2))
    (g := fun t => F t - √2 * sinh (t / √2))
    (df := fun t => F t / D t - sinh (t / √2) / √2)
    (dg := fun t => c t * V t - cosh (t / √2))
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub (hcd t))
    (fun t ht => (hF t ht).sub (hsd t))
    (by simp [hV0]) (by simpa using hF0)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      constructor
      · positivity
      · have : 1 / D t ≤ 1 := (div_le_one hdpos).mpr hdt.1
        linarith)
    (fun t ht => ⟨le_trans zero_le_one (hc t ht).1, (hc t ht).2⟩)
    (fun t ht => by
      have hdt := hD t ht
      have hdpos : 0 < D t := lt_of_lt_of_le zero_lt_one hdt.1
      have hsinh : 0 ≤ sinh (t / √2) :=
        sinh_nonneg_iff.mpr (div_nonneg ht.1 hspos.le)
      have hinv : 1 / (√2 : ℝ) ≤ √2 / D t := by
        apply (div_le_div_iff₀ hspos hdpos).mpr
        nlinarith [hdt.2]
      have hmul := mul_nonneg hsinh (sub_nonneg.mpr hinv)
      simp only [div_eq_mul_inv] at hmul ⊢
      nlinarith)
    (fun t ht => by
      have hmul := mul_nonneg (sub_nonneg.mpr (hc t ht).1)
        (cosh_pos (t / √2)).le
      nlinarith)
  intro t ht
  exact ⟨sub_nonneg.mp (hcompare t ht).1, sub_nonneg.mp (hcompare t ht).2⟩

/-- The precise cosine-hyperbolic growth comparison used after equation (30).
The initial derivative is allowed to be arbitrarily large and nonnegative. -/
theorem equation30_cosh_lower
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T,
      cosh (t / √2) ≤ V t ∧
      √2 * sinh (t / √2) ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := by
  have hcoeff : ∀ t ∈ Icc 0 T,
      0 ≤ β * t ^ 2 ∧ β * t ^ 2 ≤ 1 := by
    intro t ht
    have ht2 : t ^ 2 ≤ T ^ 2 := (sq_le_sq₀ ht.1 hT).mpr ht.2
    exact ⟨mul_nonneg hβ (sq_nonneg _),
      le_trans (mul_le_mul_of_nonneg_left ht2 hβ) hscale⟩
  apply cosh_lower_of_flux_system
    (D := fun t => 1 + (β * t ^ 2) ^ 2)
    (c := fun t => 2 * (1 - β * (β * t ^ 2)))
    (F := fun t => (1 + (β * t ^ 2) ^ 2) * V₁ t)
  · intro t ht
    apply (hV t ht).congr_deriv
    have hD : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  · exact hflux
  · exact hV0
  · simpa using hV₁0
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    constructor <;> nlinarith [sq_nonneg (β * t ^ 2)]
  · intro t ht
    obtain ⟨hl, hu⟩ := hcoeff t ht
    have hp : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hl
    have hq : β * (β * t ^ 2) ≤ β := by nlinarith
    constructor <;> nlinarith

/-- Equation (30) gives positivity and a nonnegative derivative from the
initial conditions alone, throughout the pre-inversion interval. -/
theorem equation30_positive
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Icc 0 T, 0 < V t ∧ 0 ≤ V₁ t := by
  intro t ht
  obtain ⟨hcosh, hfluxlower⟩ :=
    equation30_cosh_lower hβ hβsmall hT hscale hV hflux hV0 hV₁0 t ht
  constructor
  · exact lt_of_lt_of_le (cosh_pos _) hcosh
  · have hsinh : 0 ≤ √2 * sinh (t / √2) :=
      mul_nonneg (sqrt_nonneg _)
        (sinh_nonneg_iff.mpr (div_nonneg ht.1 (sqrt_nonneg _)))
    have hprod : 0 ≤ (1 + (β * t ^ 2) ^ 2) * V₁ t := hsinh.trans hfluxlower
    exact nonneg_of_mul_nonneg_right hprod (by positivity)

/-- A convenient pure exponential consequence of the hyperbolic-cosine bound. -/
theorem exp_quarter_le_cosh {t : ℝ} (ht : 4 ≤ t) :
    exp (t / 4) ≤ cosh (t / √2) := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hspos : (0 : ℝ) < √2 := by positivity
  have hsq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : (√2 : ℝ) ≤ 2 := by nlinarith [sqrt_nonneg (2 : ℝ)]
  have hexp : 2 ≤ exp (t / 4) := by linarith [add_one_le_exp (t / 4)]
  have harg : t / 4 + t / 4 ≤ t / √2 := by
    apply (le_div_iff₀ hspos).mpr
    have := mul_le_mul_of_nonneg_left hsle ht0
    nlinarith
  have hprod : exp (t / 4) * exp (t / 4) ≤ exp (t / √2) := by
    rw [← exp_add]
    exact exp_le_exp.mpr harg
  rw [cosh_eq]
  nlinarith [exp_pos (-(t / √2))]

/-- At `T = 1 / sqrt β`, equation (30) amplifies by at least
`exp (1 / (4 sqrt β))`, uniformly over every nonnegative initial derivative. -/
theorem equation30_endpoint_exponential
    {β : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1 / 16)
    (hV : ∀ t ∈ Icc 0 (1 / √β), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / √β),
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    exp (1 / (4 * √β)) ≤ V (1 / √β) := by
  have hspos : 0 < √β := sqrt_pos.mpr hβ
  have hsne : √β ≠ 0 := ne_of_gt hspos
  have hsq : (√β) ^ 2 = β := sq_sqrt hβ.le
  have hT : 0 ≤ 1 / √β := by positivity
  have hscale : β * (1 / √β) ^ 2 ≤ 1 := by
    have : β * (1 / √β) ^ 2 = 1 := by
      field_simp
      exact hsq.symm
    exact this.le
  have hT4 : 4 ≤ 1 / √β := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  have hg := (equation30_cosh_lower hβ.le (by linarith) hT hscale hV hflux hV0 hV₁0
    (1 / √β) ⟨hT, le_rfl⟩).1
  have he := exp_quarter_le_cosh hT4
  have heq : (1 / √β) / 4 = 1 / (4 * √β) := by ring
  rw [heq] at he
  exact he.trans hg

/-- Nonnegative initial values give componentwise lower bounds for a
cooperative flux system, with no smallness restriction on the coefficients. -/
theorem flux_lower_initial
    {V F D c : ℝ → ℝ} {T K : ℝ}
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (F t / D t) t)
    (hF : ∀ t ∈ Icc 0 T, HasDerivAt F (c t * V t) t)
    (hV0 : 0 ≤ V 0) (hF0 : 0 ≤ F 0)
    (hD : ∀ t ∈ Icc 0 T, 0 ≤ 1 / D t ∧ 1 / D t ≤ K)
    (hc : ∀ t ∈ Icc 0 T, 0 ≤ c t ∧ c t ≤ K) :
    ∀ t ∈ Icc 0 T, V 0 ≤ V t ∧ F 0 ≤ F t := by
  have hp := cooperative_nonneg_of_bounded
    (f := fun t => V t - V 0) (g := fun t => F t - F 0)
    (df := fun t => F t / D t) (dg := fun t => c t * V t)
    (a := fun t => 1 / D t) (b := c)
    (fun t ht => (hV t ht).sub_const (V 0))
    (fun t ht => (hF t ht).sub_const (F 0))
    (by simp) (by simp) hD hc
    (fun t ht => by
      have hp := mul_nonneg (hD t ht).1 hF0
      simp only [div_eq_mul_inv] at hp ⊢
      nlinarith)
    (fun t ht => by nlinarith [mul_nonneg (hc t ht).1 hV0])
  intro t ht
  exact ⟨sub_nonneg.mp (hp t ht).1, sub_nonneg.mp (hp t ht).2⟩

/-- The inverted equation preserves positive `f` and negative `f'` when it is
integrated from `y = 1` towards smaller nonnegative `y`. -/
theorem inversion_positive
    {β a : ℝ} {f f₁ : ℝ → ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 1) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0) :
    ∀ y ∈ Icc a 1, f 1 ≤ f y ∧ 0 < f y ∧ f₁ y < 0 := by
  have htwo : (2 : ℝ) ≤ 2 / β := (le_div_iff₀ hβ).mpr (by nlinarith)
  have hmirror : ∀ t ∈ Icc 0 (1 - a), 1 - t ∈ Icc a 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hp := flux_lower_initial
    (V := fun t => f (1 - t))
    (F := fun t => -((1 + (1 - t) ^ 4) * f₁ (1 - t)))
    (D := fun t => 1 + (1 - t) ^ 4)
    (c := fun t => 2 / β - 2 * (1 - t) ^ 2)
    (T := 1 - a) (K := 2 / β + 1)
    (fun t ht => by
      apply ((hf (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).congr_deriv
      have hd : 1 + (1 - t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
      field_simp)
    (fun t ht => by
      apply (((hflux (1 - t) (hmirror t ht)).comp t
        ((hasDerivAt_id t).const_sub 1)).neg).congr_deriv
      ring)
    (by simpa using hf1.le)
    (by norm_num; linarith)
    (fun t ht => by
      have hdpos : 0 < 1 + (1 - t) ^ 4 := by positivity
      have hdinv : 1 / (1 + (1 - t) ^ 4) ≤ 1 :=
        (div_le_one hdpos).mpr (by
          have : 0 ≤ (1 - t) ^ 4 := by positivity
          linarith)
      exact ⟨by positivity, by linarith⟩)
    (fun t ht => by
      obtain ⟨hyl, hyu⟩ := hmirror t ht
      have hy0 : 0 ≤ 1 - t := le_trans ha hyl
      have hy2 : (1 - t) ^ 2 ≤ 1 := by nlinarith
      constructor <;> nlinarith [sq_nonneg (1 - t)])
  intro y hy
  have htime : 1 - y ∈ Icc 0 (1 - a) := by constructor <;> linarith [hy.1, hy.2]
  have hp' := hp (1 - y) htime
  have hrefl : 1 - (1 - y) = y := by ring
  simp only [sub_zero, hrefl, one_pow, one_add_one_eq_two] at hp'
  refine ⟨hp'.1, hf1.trans_le hp'.1, ?_⟩
  have hpositive : 0 < -((1 + y ^ 4) * f₁ y) := lt_of_lt_of_le (by linarith) hp'.2
  have hnegative : (1 + y ^ 4) * f₁ y < 0 := by linarith
  exact neg_of_mul_neg_right hnegative (by positivity)

/-- A uniform Riccati upper bound that does not depend on the finite initial
value: a solution of `l' ≤ 2 - l²` obeys `l(t) ≤ 2 + 1/t` for `t > 0`. -/
theorem riccati_upper_bound
    {l dl : ℝ → ℝ} {T : ℝ}
    (hl : ∀ t ∈ Icc 0 T, HasDerivAt l (dl t) t)
    (hineq : ∀ t ∈ Ico 0 T, dl t ≤ 2 - (l t) ^ 2) :
    ∀ t ∈ Ioc 0 T, l t ≤ 2 + 1 / t := by
  have hp : ∀ t ∈ Icc 0 T, t * l t ≤ 1 + 2 * t := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => t * l t) (f' := fun t => l t + t * dl t)
      (B := fun t => 1 + 2 * t) (B' := fun _ => 2)
    · intro t ht
      exact ((hasDerivAt_id t).mul (hl t ht)).continuousAt.continuousWithinAt
    · intro t ht
      convert! ((hasDerivAt_id t).mul (hl t (Ico_subset_Icc_self ht))).hasDerivWithinAt using 1
      simp
    · norm_num
    · intro t
      simpa using ((hasDerivAt_id t).const_mul 2).const_add 1
    · intro t ht hboundary
      have htpos : 0 < t := by
        rcases ht.1.eq_or_lt with htzero | htpos
        · rw [← htzero] at hboundary
          norm_num at hboundary
        · exact htpos
      have hmul := mul_le_mul_of_nonneg_left (hineq t ht) (sq_nonneg t)
      have hsq := congrArg (fun x : ℝ => x ^ 2) hboundary
      apply (mul_lt_mul_iff_right₀ htpos).mp
      nlinarith
  intro t ht
  have htp := hp t ⟨ht.1.le, ht.2⟩
  calc
    l t = (t * l t) / t := by field_simp [ne_of_gt ht.1]
    _ ≤ (1 + 2 * t) / t := div_le_div_of_nonneg_right htp ht.1.le
    _ = 2 + 1 / t := by field_simp [ne_of_gt ht.1]; ring

/-- Recovering the ordinary second derivative from the differentiated flux. -/
theorem equation30_second_derivative
    {β t : ℝ} {V V₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - β * (β * t ^ 2)) * V t) t) :
    HasDerivAt V₁
      ((2 * (1 - β * (β * t ^ 2)) * V t - 4 * β ^ 2 * t ^ 3 * V₁ t) /
        (1 + (β * t ^ 2) ^ 2)) t := by
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2)
      (4 * β ^ 2 * t ^ 3) t := by
    apply (((((hasDerivAt_id t).fun_pow 2).const_mul β).fun_pow 2).const_add 1).congr_deriv
    dsimp
    ring
  have hDne : ∀ s : ℝ, 1 + (β * s ^ 2) ^ 2 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne t)
  convert! hq using 1
  · ext s
    change V₁ s = ((1 + (β * s ^ 2) ^ 2) * V₁ s) / (1 + (β * s ^ 2) ^ 2)
    field_simp [hDne s]
  · field_simp

/-- The logarithmic derivative in equation (30) is uniformly bounded away
from the initial time, independently of the initial nonnegative slope. -/
theorem equation30_log_derivative_upper
    {β T : ℝ} {V V₁ : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβsmall : β ≤ 1 / 2) (hT : 0 ≤ T)
    (hscale : β * T ^ 2 ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t ∈ Ioc 0 T, V₁ t / V t ≤ 2 + 1 / t := by
  have hp := equation30_positive hβ hβsmall hT hscale hV hflux hV0 hV₁0
  let dl : ℝ → ℝ := fun t =>
    2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) -
      (4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2)) * (V₁ t / V t) -
      (V₁ t / V t) ^ 2
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun t => V₁ t / V t) (dl t) t := by
    intro t ht
    have hVne : V t ≠ 0 := ne_of_gt (hp t ht).1
    have hDne : 1 + (β * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    apply ((equation30_second_derivative (hflux t ht)).div (hV t ht) hVne).congr_deriv
    dsimp [dl]
    field_simp
  apply riccati_upper_bound hd
  intro t ht
  have hti : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hDpos : 0 < 1 + (β * t ^ 2) ^ 2 := by positivity
  have hDge : 1 ≤ 1 + (β * t ^ 2) ^ 2 := by nlinarith [sq_nonneg (β * t ^ 2)]
  have hcub : 2 * (1 - β * (β * t ^ 2)) ≤ 2 := by
    nlinarith [mul_nonneg hβ (mul_nonneg hβ (sq_nonneg t))]
  have hquot : 2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2) ≤ 2 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  have ht0 : 0 ≤ t := ht.1
  have hcoef : 0 ≤ 4 * β ^ 2 * t ^ 3 / (1 + (β * t ^ 2) ^ 2) := by positivity
  have hlog : 0 ≤ V₁ t / V t := div_nonneg (hp t hti).2 (hp t hti).1.le
  dsimp [dl]
  nlinarith [mul_nonneg hcoef hlog]

/-- A coarse Riccati upper barrier for the inverted equation. -/
theorem riccati_le_four
    {z a b : ℝ → ℝ} {T : ℝ}
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (a t - (z t) ^ 2 + b t * z t) t)
    (hz0 : z 0 ≤ 4)
    (ha : ∀ t ∈ Ico 0 T, a t ≤ 2)
    (hb : ∀ t ∈ Ico 0 T, b t ≤ 1) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := z) (f' := fun t => a t - (z t) ^ 2 + b t * z t)
    (B := fun _ => 4) (B' := fun _ => 0)
    (fun t ht => (hz t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hz0 (fun t => hasDerivAt_const t 4)
  intro t ht hboundary
  rw [hboundary]
  linarith [ha t ht, hb t ht]

/-- Quantitative tracking of the stable positive Riccati branch.  This
abstract estimate is applied below with `μ = sqrt(2/(1+y^4))`; all constants
are explicit and do not involve the initial nonnegative slope. -/
theorem riccati_tracking
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, |z t - μ t| ≤ 6 * exp (-t) + 48 * ε := by
  have hBd : ∀ t : ℝ, HasDerivAt (fun s => 6 * exp (-s) + 48 * ε)
      (-6 * exp (-t)) t := by
    intro t
    apply (((hasDerivAt_id t).neg.exp.const_mul 6).add_const (48 * ε)).congr_deriv
    dsimp
    ring
  have hBpos : ∀ t : ℝ, 0 ≤ 6 * exp (-t) + 48 * ε := by
    intro t
    positivity
  by_cases hT : 0 ≤ T
  · have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hupper : ∀ t ∈ Icc 0 T, z t - μ t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => z t - μ t) (f' := fun t => dz t - dμ t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hz t ht).sub (hμ t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hz t (Ico_subset_Icc_self ht)).sub
          (hμ t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith [(hzrange 0 hzero).2, (hμrange 0 hzero).1]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith [(hzrange t hti).1, (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      nlinarith
    have hlower : ∀ t ∈ Icc 0 T, μ t - z t ≤ 6 * exp (-t) + 48 * ε := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun t => μ t - z t) (f' := fun t => dμ t - dz t)
        (B := fun t => 6 * exp (-t) + 48 * ε) (B' := fun t => -6 * exp (-t))
        (fun t ht => ((hμ t ht).sub (hz t ht)).continuousAt.continuousWithinAt)
        (fun t ht => ((hμ t (Ico_subset_Icc_self ht)).sub
          (hz t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
        (by norm_num; linarith [(hzrange 0 hzero).1, (hμrange 0 hzero).2]) hBd
      intro t ht hboundary
      have hti := Ico_subset_Icc_self ht
      have hsum : 1 ≤ z t + μ t := by linarith [(hzrange t hti).1, (hμrange t hti).1]
      have hprod := mul_nonneg (sub_nonneg.mpr hsum) (hBpos t)
      obtain ⟨hrlo, hrhi⟩ := abs_le.mp (hres t ht)
      obtain ⟨hμlo, hμhi⟩ := abs_le.mp (hμderiv t ht)
      nlinarith
    intro t ht
    exact abs_le.mpr ⟨by linarith [hlower t ht], hupper t ht⟩
  · intro t ht
    exact False.elim (hT (le_trans ht.1 ht.2))

/-- After time `1/(2ε)` the Riccati tracking error is at most `60ε`. -/
theorem riccati_tracking_after_layer
    {z μ dz dμ : ℝ → ℝ} {T ε : ℝ}
    (hε : 0 < ε)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (dz t) t)
    (hμ : ∀ t ∈ Icc 0 T, HasDerivAt μ (dμ t) t)
    (hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4)
    (hμrange : ∀ t ∈ Icc 0 T, 1 ≤ μ t ∧ μ t ≤ 2)
    (hres : ∀ t ∈ Ico 0 T, |dz t - ((μ t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε)
    (hμderiv : ∀ t ∈ Ico 0 T, |dμ t| ≤ 4 * ε) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t → |z t - μ t| ≤ 60 * ε := by
  intro t ht hlayer
  have htime : 1 ≤ 2 * ε * t := by
    have := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hlayer
    nlinarith
  have hexp : exp (-t) ≤ 2 * ε := by
    rw [exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hm := mul_le_mul_of_nonneg_left (add_one_le_exp t) (show 0 ≤ 2 * ε by positivity)
    nlinarith
  have htrack := riccati_tracking hε hz hμ hzrange hμrange hres hμderiv t ht
  linarith

/-- The positive stationary branch of the rescaled inverted Riccati equation. -/
noncomputable def riccatiRoot (ε t : ℝ) : ℝ :=
  sqrt (2 / (1 + (1 - ε * t) ^ 4))

/-- Its derivative as the spatial coordinate `y = 1 - εt` decreases. -/
noncomputable def riccatiRootDeriv (ε t : ℝ) : ℝ :=
  4 * ε * (1 - ε * t) ^ 3 /
    ((1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t)

theorem hasDerivAt_riccatiRoot (ε t : ℝ) :
    HasDerivAt (riccatiRoot ε) (riccatiRootDeriv ε t) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hdne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hqpos : 0 < 2 / (1 + (1 - ε * t) ^ 4) := by positivity
  have hq : HasDerivAt (fun s => 2 / (1 + (1 - ε * s) ^ 4))
      (8 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ^ 2) t := by
    apply ((hasDerivAt_const t 2).div ((hy.fun_pow 4).const_add 1) hdne).congr_deriv
    dsimp
    field_simp
    ring
  apply (hq.sqrt (ne_of_gt hqpos)).congr_deriv
  dsimp [riccatiRootDeriv, riccatiRoot]
  field_simp [hdne, ne_of_gt (sqrt_pos.mpr hqpos)]
  ring

theorem riccatiRoot_bounds {ε t : ℝ}
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    1 ≤ riccatiRoot ε t ∧ riccatiRoot ε t ≤ 2 := by
  have hy4 : (1 - ε * t) ^ 4 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy.1 hy.2 4
  have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith
  constructor
  · apply one_le_sqrt.mpr
    apply (le_div_iff₀ hdpos).mpr
    linarith
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ hdpos).mpr
      nlinarith

theorem riccatiRootDeriv_bounds {ε t : ℝ} (hε : 0 ≤ ε)
    (hy : 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1) :
    0 ≤ riccatiRootDeriv ε t ∧ riccatiRootDeriv ε t ≤ 4 * ε := by
  have hμ := riccatiRoot_bounds hy
  have hy0 := hy.1
  have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hy.1 hy.2 3
  have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
    have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
    linarith
  have hDsq : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 := by nlinarith
  have hden : 1 ≤ (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t :=
    hDsq.trans (le_mul_of_one_le_right (sq_nonneg _) hμ.1)
  have hdenpos : 0 < (1 + (1 - ε * t) ^ 4) ^ 2 * riccatiRoot ε t := by linarith
  constructor
  · exact div_nonneg (by positivity) hdenpos.le
  · apply (div_le_iff₀ hdenpos).mpr
    exact mul_le_mul_of_nonneg_left (hy3.trans hden) (by positivity)

/-- Right-hand side of the inverted Riccati equation in the fast coordinate
`t = (1-y)/ε`, where `ε = sqrt β`. -/
noncomputable def invertedRiccati (ε t z : ℝ) : ℝ :=
  (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) - z ^ 2 +
    (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z

/-- Explicit form of the uniform `O(sqrt β)` Riccati estimate in (31).
This theorem uses the exact rescaled ODE and an initial bound of `4`; the
preceding logarithmic-derivative estimate supplies that bound independently
of the nonnegative initial slope. -/
theorem inverted_riccati_squared_error
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) (hzn : ∀ t ∈ Icc 0 T, 0 ≤ z t) :
    ∀ t ∈ Icc 0 T, 1 / (2 * ε) ≤ t →
      |(z t) ^ 2 - 2 / (1 + (1 - ε * t) ^ 4)| ≤ 360 * ε := by
  have hy : ∀ t ∈ Icc 0 T, 0 ≤ 1 - ε * t ∧ 1 - ε * t ≤ 1 := by
    intro t ht
    have hu := mul_le_mul_of_nonneg_left ht.2 hε.le
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hcoeff : ∀ t ∈ Icc 0 T,
      (2 - 2 * ε ^ 2 * (1 - ε * t) ^ 2) / (1 + (1 - ε * t) ^ 4) ≤ 2 ∧
      0 ≤ 4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ∧
      4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4) ≤ 4 * ε := by
    intro t ht
    have hyt := hy t ht
    have hy0 := hyt.1
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ hyt.1 hyt.2 3
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
      have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
      linarith
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    refine ⟨?_, by positivity, ?_⟩
    · apply (div_le_iff₀ hdpos).mpr
      nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t))]
    · apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy3.trans hdge) (by positivity)
  have hzfour : ∀ t ∈ Icc 0 T, z t ≤ 4 := by
    apply riccati_le_four hz hz0
    · intro t ht
      exact (hcoeff t (Ico_subset_Icc_self ht)).1
    · intro t ht
      linarith [(hcoeff t (Ico_subset_Icc_self ht)).2.2]
  have hzrange : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ 4 :=
    fun t ht => ⟨hzn t ht, hzfour t ht⟩
  have hres : ∀ t ∈ Ico 0 T,
      |invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2)| ≤ 20 * ε := by
    intro t ht
    have hti := Ico_subset_Icc_self ht
    have hyt := hy t hti
    have hy0 := hyt.1
    have hy2 : (1 - ε * t) ^ 2 ≤ 1 := by nlinarith [hyt.1, hyt.2]
    have hdge : 1 ≤ 1 + (1 - ε * t) ^ 4 := by
      have : 0 ≤ (1 - ε * t) ^ 4 := by positivity
      linarith
    have hdpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    have hqnonneg : 0 ≤ 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) := by positivity
    have hqupper : 2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4) ≤ 2 * ε ^ 2 := by
      apply (div_le_iff₀ hdpos).mpr
      exact mul_le_mul_of_nonneg_left (hy2.trans hdge) (by positivity)
    have hbn := (hcoeff t hti).2.1
    have hbu := (hcoeff t hti).2.2
    have hmulnonneg := mul_nonneg hbn (hzn t hti)
    have hmulupper :
        (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t ≤ 16 * ε := by
      have hm := mul_le_mul hbu (hzfour t hti) (hzn t hti) (show 0 ≤ 4 * ε by positivity)
      nlinarith
    have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
      sq_sqrt (by positivity)
    have heq : invertedRiccati ε t (z t) - ((riccatiRoot ε t) ^ 2 - (z t) ^ 2) =
        -(2 * ε ^ 2 * (1 - ε * t) ^ 2 / (1 + (1 - ε * t) ^ 4)) +
          (4 * ε * (1 - ε * t) ^ 3 / (1 + (1 - ε * t) ^ 4)) * z t := by
      rw [hsquare]
      unfold invertedRiccati
      field_simp
      ring
    rw [heq]
    apply abs_le.mpr
    constructor <;> nlinarith
  have hμderiv : ∀ t ∈ Ico 0 T, |riccatiRootDeriv ε t| ≤ 4 * ε := by
    intro t ht
    have hp := riccatiRootDeriv_bounds hε.le (hy t (Ico_subset_Icc_self ht))
    rw [abs_of_nonneg hp.1]
    exact hp.2
  intro t ht hlayer
  have htrack := riccati_tracking_after_layer hε hz
    (fun s _ => hasDerivAt_riccatiRoot ε s) hzrange
    (fun s hs => riccatiRoot_bounds (hy s hs)) hres hμderiv t ht hlayer
  have hμrange := riccatiRoot_bounds (hy t ht)
  have hsum : |z t + riccatiRoot ε t| ≤ 6 := by
    rw [abs_of_nonneg (by linarith [hzn t ht])]
    linarith [hzfour t ht]
  have hsquare : (riccatiRoot ε t) ^ 2 = 2 / (1 + (1 - ε * t) ^ 4) :=
    sq_sqrt (by positivity)
  rw [← hsquare, sq_sub_sq, abs_mul]
  have hm := mul_le_mul htrack hsum (abs_nonneg _) (show 0 ≤ 60 * ε by positivity)
  nlinarith

/-- The second derivative of a solution of the inverted scalar equation. -/
theorem inversion_second_derivative
    {β y : ℝ} {f f₁ : ℝ → ℝ}
    (hflux : HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / β - 2 * y ^ 2) * f y) y) :
    HasDerivAt f₁ (((2 / β - 2 * y ^ 2) * f y - 4 * y ^ 3 * f₁ y) /
      (1 + y ^ 4)) y := by
  have hD : HasDerivAt (fun z : ℝ => 1 + z ^ 4) (4 * y ^ 3) y := by
    convert! ((hasDerivAt_id y).fun_pow 4).const_add 1 using 1
    norm_num
  have hDne : ∀ z : ℝ, 1 + z ^ 4 ≠ 0 := fun _ => ne_of_gt (by positivity)
  have hq := hflux.div hD (hDne y)
  convert! hq using 1
  · ext z
    change f₁ z = ((1 + z ^ 4) * f₁ z) / (1 + z ^ 4)
    field_simp [hDne z]
  · field_simp

/-- The exact Riccati equation after the substitutions
`y = 1-εt` and `z = -ε f'/f`. -/
theorem hasDerivAt_inverted_logderivative
    {ε t : ℝ} {f f₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hfpos : f (1 - ε * t) ≠ 0)
    (hf : HasDerivAt f (f₁ (1 - ε * t)) (1 - ε * t))
    (hflux : HasDerivAt (fun y => (1 + y ^ 4) * f₁ y)
      ((2 / ε ^ 2 - 2 * (1 - ε * t) ^ 2) * f (1 - ε * t)) (1 - ε * t)) :
    HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
      (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
  have hy : HasDerivAt (fun s : ℝ => 1 - ε * s) (-ε) t := by
    simpa using ((hasDerivAt_id t).const_mul ε).const_sub 1
  have hDne : 1 + (1 - ε * t) ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hd := (((inversion_second_derivative hflux).comp t hy).const_mul (-ε)).div
    (hf.comp t hy) hfpos
  apply hd.congr_deriv
  dsimp [invertedRiccati]
  field_simp
  ring

/-- The uniform Riccati estimate directly for solutions of the inverted
scalar equation.  Positivity on the interval follows from the endpoint
conditions; it is not assumed. -/
theorem inversion_riccati_error
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a (1 / 2),
      |(-ε * f₁ y / f y) ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      nlinarith
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by
    field_simp
    linarith
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hznonneg : ∀ t ∈ Icc 0 ((1 - a) / ε),
      0 ≤ -ε * f₁ (1 - ε * t) / f (1 - ε * t) := by
    intro t ht
    have hpt := hp (1 - ε * t) (hmirror t ht)
    apply div_nonneg _ hpt.2.1.le
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) hpt.2.2.le
  have herr := inverted_riccati_squared_error hε hεsmall hscale hz
    (by simpa using hinit) hznonneg
  intro y hy
  have hy1 : y ≤ 1 := by linarith [hy.2]
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hy1) hε.le
    · exact div_le_div_of_nonneg_right (by linarith [hy.1]) hε.le
  have hlayer : 1 / (2 * ε) ≤ (1 - y) / ε := by
    apply (div_le_div_iff₀ (show 0 < 2 * ε by positivity) hε).mpr
    nlinarith [hy.2]
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  simpa only [heq] using herr ((1 - y) / ε) ht hlayer

/-- Inversion of a solution in the original time variable, including the
rescaling `x = ετ`. -/
noncomputable def invertedScalar (ε : ℝ) (V : ℝ → ℝ) (y : ℝ) : ℝ :=
  V (y⁻¹ / ε) / y

/-- The exact derivative of `invertedScalar`, away from `y = 0`. -/
noncomputable def invertedScalarDeriv (ε : ℝ) (V V₁ : ℝ → ℝ) (y : ℝ) : ℝ :=
  -V (y⁻¹ / ε) / y ^ 2 - V₁ (y⁻¹ / ε) / (ε * y ^ 3)

/-- Both differential equations for the rescaled inversion, derived
algebraically from equation (30). -/
theorem invertedScalar_equations
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : HasDerivAt V (V₁ (y⁻¹ / ε)) (y⁻¹ / ε))
    (hflux : HasDerivAt (fun t => (1 + (ε ^ 2 * t ^ 2) ^ 2) * V₁ t)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * (y⁻¹ / ε) ^ 2)) * V (y⁻¹ / ε)) (y⁻¹ / ε)) :
    HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y ∧
    HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * invertedScalar ε V y) y := by
  have harg := (hasDerivAt_inv hy).div_const ε
  have h0 := hV.comp y harg
  have h1 := (equation30_second_derivative hflux).comp y harg
  have h2 := (hasDerivAt_id y).fun_pow 2
  have h3 := ((hasDerivAt_id y).fun_pow 3).const_mul ε
  have h4 := ((hasDerivAt_id y).fun_pow 4).const_add 1
  have hDne : 1 + (ε ^ 2 * (y⁻¹ / ε) ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  constructor
  · apply (h0.div (hasDerivAt_id y) hy).congr_deriv
    dsimp [invertedScalarDeriv]
    field_simp
    ring
  · apply (h4.mul ((h0.neg.div h2 (pow_ne_zero 2 hy)).sub
      (h1.div h3 (mul_ne_zero hε (pow_ne_zero 3 hy))))).congr_deriv
    dsimp [invertedScalar]
    field_simp
    ring

/-- At the start of inversion the Riccati variable has an absolute bound,
independent of the original initial nonnegative slope. -/
theorem invertedScalar_initial_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t ∈ Icc 0 (1 / ε), HasDerivAt V (V₁ t) t)
    (hflux : ∀ t ∈ Icc 0 (1 / ε),
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    0 < invertedScalar ε V 1 ∧ invertedScalarDeriv ε V V₁ 1 < 0 ∧
      -ε * invertedScalarDeriv ε V V₁ 1 / invertedScalar ε V 1 ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hT : 0 ≤ 1 / ε := by positivity
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hβsmall : ε ^ 2 ≤ 1 / 2 := by nlinarith
  have hp := equation30_positive (sq_nonneg ε) hβsmall hT hscale hV hflux hV0 hV₁0
    (1 / ε) ⟨hT, le_rfl⟩
  have hl := equation30_log_derivative_upper (sq_nonneg ε) hβsmall hT hscale
    hV hflux hV0 hV₁0 (1 / ε) ⟨by positivity, le_rfl⟩
  have hVne : V (1 / ε) ≠ 0 := ne_of_gt hp.1
  dsimp [invertedScalar, invertedScalarDeriv]
  simp only [inv_one, one_pow, div_one, mul_one, neg_mul]
  refine ⟨hp.1, ?_, ?_⟩
  · have hquot : 0 ≤ V₁ (1 / ε) / ε := div_nonneg hp.2 hε.le
    linarith
  · have heq : -(ε * (-(V (1 / ε)) - V₁ (1 / ε) / ε)) / V (1 / ε) =
        ε + V₁ (1 / ε) / V (1 / ε) := by field_simp; ring
    rw [heq]
    rw [one_div_one_div] at hl
    linarith

/-- The full uniform estimate (31) for the scalar equation, including the
rescaling, inversion, positivity, and removal of all dependence on the
original nonnegative initial slope. -/
theorem equation30_inverted_riccati_error
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      |(-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) ^ 2 -
        2 / (1 + y ^ 4)| ≤ 360 * ε := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hyhalf
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_error hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hyhalf⟩

/-- The Wronskian flux of two solutions of `(D u')' = c u` is conserved. -/
theorem flux_wronskian_constant
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    ∀ t ∈ Icc a b,
      u t * (D t * v₁ t) - (D t * u₁ t) * v t =
        u a * (D a * v₁ a) - (D a * u₁ a) * v a := by
  have hw : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => u s * (D s * v₁ s) - (D s * u₁ s) * v s) 0 t := by
    intro t ht
    apply (((hu t ht).mul (hfv t ht)).sub ((hfu t ht).mul (hv t ht))).congr_deriv
    ring
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hw t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-- The derivative of the quotient of two scalar solutions, expressed using
their initial Wronskian rather than either exponentially large solution. -/
theorem quotient_derivative_of_flux
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      HasDerivAt (fun s => v s / u s)
        ((u a * (D a * v₁ a) - (D a * u₁ a) * v a) / (D t * (u t) ^ 2)) t := by
  intro t ht
  apply ((hv t ht).div (hu t ht) (hupos t ht)).congr_deriv
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  calc
    (v₁ t * u t - v t * u₁ t) / (u t) ^ 2 =
        (u t * (D t * v₁ t) - (D t * u₁ t) * v t) / (D t * (u t) ^ 2) := by
      field_simp [hD t ht, hupos t ht]
    _ = _ := by rw [hw]

/-- The exact reduction-of-order formula on a closed interval.  Its integral
contains the reciprocal square of the positive reference solution. -/
theorem reduction_of_order
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = u t * (v a / u a +
        (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
          ∫ s in a..t, 1 / (D s * (u s) ^ 2)) := by
  intro t ht
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have huc : ContinuousOn u (Icc a b) :=
    fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / (D s * (u s) ^ 2)) (Icc a b) :=
    continuousOn_const.div (hDc.mul (huc.pow 2))
      (fun s hs => mul_ne_zero (hD s hs) (pow_ne_zero 2 (hupos s hs)))
  have hii : IntervalIntegrable (fun s => 1 / (D s * (u s) ^ 2))
      MeasureTheory.volume a t := (hic.mono hsubset).intervalIntegrable
  have hdi := hii.const_mul (u a * (D a * v₁ a) - (D a * u₁ a) * v a)
  have hd := quotient_derivative_of_flux hu hv hfu hfv hD hupos
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => (hd s (hsubset hs)).congr_deriv
      (by simp only [div_eq_mul_inv]; ring)) hdi
  rw [intervalIntegral.integral_const_mul] at hint
  have hune : u t ≠ 0 := hupos t ht
  have hratio : v t / u t = v a / u a +
      (u a * (D a * v₁ a) - (D a * u₁ a) * v a) *
        ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by linarith
  rw [← hratio]
  field_simp

/-- Positivity and decrease of the inverted scalar solution for every
positive inversion coordinate. -/
theorem invertedScalar_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      invertedScalar ε V 1 ≤ invertedScalar ε V y ∧
      0 < invertedScalar ε V y ∧ invertedScalarDeriv ε V V₁ y < 0 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1) hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 y ⟨le_rfl, hy1⟩

/-- Growth remains at least the value at `x=1` divided by `x` after
inversion.  This is the lower bound used in the exponential gain estimate. -/
theorem equation30_post_inversion_lower
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ x, 1 ≤ x → V (1 / ε) / x ≤ V (x / ε) ∧ 0 < V (x / ε) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : 0 < 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := (div_le_one hxpos).mpr hx
  have hp := invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 (1 / x) hypos hy1
  have hid : invertedScalar ε V (1 / x) = x * V (x / ε) := by
    simp [invertedScalar, one_div, div_inv_eq_mul, mul_comm]
  have hid1 : invertedScalar ε V 1 = V (1 / ε) := by simp [invertedScalar]
  rw [hid, hid1] at hp
  constructor
  · apply (div_le_iff₀ hxpos).mpr
    nlinarith [hp.1]
  · exact pos_of_mul_pos_right hp.2.1 hxpos.le

/-- A solution with the source's initial conditions stays positive for every
nonnegative original time, including beyond the inversion point. -/
theorem equation30_global_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → 0 < V t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    exact (equation30_positive (sq_nonneg ε) (by nlinarith) hT hscale
      (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩).1
  · have hx : 1 ≤ ε * t := by
      have := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      nlinarith
    have hp := (equation30_post_inversion_lower hε hεsmall hV hflux hV0 hV₁0 (ε * t) hx).2
    simpa only [mul_div_cancel_left₀ t hεne] using hp

/-- Reduction of order in the source's normalization `V₀(0)=1`,
`V₀'(0)=0`, `Vλ(0)=1`, `Vλ'(0)=λ`. -/
theorem equation30_reduction_of_order
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 0 ≤ t → V t = U t *
      (1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2)) := by
  have hup := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have hr := reduction_of_order
    (a := 0) (b := t)
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2)
    (c := fun s => 2 * (1 - ε ^ 2 * (ε ^ 2 * s ^ 2)))
    (fun s hs => hU s hs.1) (fun s hs => hV s hs.1)
    (fun s hs => hfluxU s hs.1) (fun s hs => hfluxV s hs.1)
    (by fun_prop) (fun _ _ => ne_of_gt (by positivity))
    (fun s hs => ne_of_gt (hup s hs.1)) t ⟨ht, le_rfl⟩
  simpa [hU0, hU₁0, hV0, hV₁0] using hr

/-- A fixed upper bound for the zero-slope reference solution on `[0,1]`. -/
theorem equation30_zero_slope_prefix_upper
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t ∈ Icc 0 1, U t ≤ exp 3 := by
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith) (by norm_num : (0 : ℝ) ≤ 1)
    (by simp only [one_pow, mul_one]; nlinarith : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hsum : ∀ t ∈ Icc 0 1,
      U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t ≤ exp (3 * t) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := fun t => U t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t)
      (f' := fun t => U₁ t + 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t)
      (B := fun t => exp (3 * t)) (B' := fun t => 3 * exp (3 * t))
      (fun t ht => ((hU t ht).add (hfluxU t ht)).continuousAt.continuousWithinAt)
      (fun t ht => ((hU t (Ico_subset_Icc_self ht)).add
        (hfluxU t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (by simp [hU0, hU₁0])
      (fun t => by
        apply (((hasDerivAt_id t).const_mul 3).exp).congr_deriv
        dsimp
        ring)
    intro t ht hboundary
    have hti := Ico_subset_Icc_self ht
    have hpt := hp t hti
    have hD : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := by nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
    have hfirst := mul_le_mul_of_nonneg_right hD hpt.2
    have hc : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) ≤ 2 := by
      nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t))]
    have hsecond := mul_le_mul_of_nonneg_right hc hpt.1.le
    have hFn : 0 ≤ (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t := mul_nonneg (by positivity) hpt.2
    nlinarith [exp_pos (3 * t)]
  intro t ht
  have hpt := hp t ht
  have hFn : 0 ≤ (1 + (ε ^ 2 * t ^ 2) ^ 2) * U₁ t := mul_nonneg (by positivity) hpt.2
  have he : exp (3 * t) ≤ exp 3 := exp_le_exp.mpr (by linarith [ht.2])
  linarith [hsum t ht]

/-- The reduction-of-order integral at time `1` has a positive absolute
lower bound.  No numerical approximations occur in the constant. -/
theorem equation30_reduction_integral_one_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t ∈ Icc 0 1, HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t ∈ Icc 0 1,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..1, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith) (by norm_num : (0 : ℝ) ≤ 1)
    (by simp only [one_pow, mul_one]; nlinarith : ε ^ 2 * (1 : ℝ) ^ 2 ≤ 1)
    hU hfluxU hU0 (by rw [hU₁0])
  have hu := equation30_zero_slope_prefix_upper hε hεsmall hU hfluxU hU0 hU₁0
  have huc : ContinuousOn U (Icc 0 1) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 1) := by
    apply continuousOn_const.div
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => 1 + (ε ^ 2 * s ^ 2) ^ 2) (Icc 0 1)).mul
        (huc.pow 2)
    · intro t ht
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hp t ht).1))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hic
  have hbound : ∀ t ∈ Icc 0 1,
      1 / (2 * exp 6) ≤ 1 / ((1 + (ε ^ 2 * t ^ 2) ^ 2) * (U t) ^ 2) := by
    intro t ht
    have hpt := hp t ht
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have heps : ε ^ 2 ≤ 1 := by nlinarith
    have hinside : 0 ≤ ε ^ 2 * t ^ 2 ∧ ε ^ 2 * t ^ 2 ≤ 1 := by
      constructor
      · positivity
      · nlinarith [mul_nonneg (sub_nonneg.mpr heps) (sq_nonneg t)]
    have hD : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≤ 2 := by nlinarith [hinside.1, hinside.2]
    have hUsq : (U t) ^ 2 ≤ (exp 3) ^ 2 := (sq_le_sq₀ hpt.1.le (exp_pos 3).le).mpr (hu t ht)
    have hprod := mul_le_mul hD hUsq (sq_nonneg (U t)) (by norm_num : (0 : ℝ) ≤ 2)
    have he : (exp (3 : ℝ)) ^ 2 = exp 6 := by
      rw [pow_two, ← exp_add]
      norm_num
    rw [he] at hprod
    exact one_div_le_one_div_of_le
      (mul_pos (by positivity) (sq_pos_of_pos hpt.1)) hprod
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / (2 * exp 6))
      MeasureTheory.volume 0 1) hint hbound
  simpa using hi

/-- The same absolute lower bound holds for the reduction integral at every
later time, because its integrand is nonnegative. -/
theorem equation30_reduction_integral_lower
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 1 ≤ t → 1 / (2 * exp 6) ≤
      ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hI1 := equation30_reduction_integral_one_lower hε hεsmall
    (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 hU₁0
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have huc : ContinuousOn U (Icc 0 t) := fun s hs => (hU s hs.1).continuousAt.continuousWithinAt
  have hic : ContinuousOn (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      (Icc 0 t) := by
    apply continuousOn_const.div
    · exact (by fun_prop : ContinuousOn (fun s : ℝ => 1 + (ε ^ 2 * s ^ 2) ^ 2) (Icc 0 t)).mul
        (huc.pow 2)
    · intro s hs
      exact ne_of_gt (mul_pos (by positivity) (sq_pos_of_pos (hpos s hs.1)))
  have hint : IntervalIntegrable (fun s => 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2))
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ht0] using hic
  have hmono := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := 1)
    (c := (0 : ℝ)) (d := t) le_rfl zero_le_one ht
    (Filter.Eventually.of_forall (fun s : ℝ => by positivity)) hint
  exact hI1.trans hmono

/-- The solution with slope `lam ≥ 0` dominates the zero-slope reference
solution by a fixed multiple of `(1+lam)` after time `1`. -/
theorem equation30_slope_uniform_lower
    {ε lam : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV0 : V 0 = 1) (hV₁0 : V₁ 0 = lam) :
    ∀ t, 1 ≤ t → ((1 + lam) / (2 * exp 6)) * U t ≤ V t := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  rw [equation30_reduction_of_order hε hεsmall hU hV hfluxU hfluxV hU0 hU₁0 hV0 hV₁0 t ht0]
  have hI := equation30_reduction_integral_lower hε hεsmall hU hfluxU hU0 hU₁0 t ht
  have hc : 1 / (2 * exp 6) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * exp 6)).mpr
    linarith [add_one_le_exp (6 : ℝ)]
  have hi : (1 + lam) / (2 * exp 6) ≤
      1 + lam * ∫ s in (0 : ℝ)..t, 1 / ((1 + (ε ^ 2 * s ^ 2) ^ 2) * (U s) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hI hlam
    simp only [div_eq_mul_inv] at hc hm ⊢
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hi (hpos t ht0).le]

/-- Before `x=1`, the original scalar solution is nondecreasing. -/
theorem equation30_prefix_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn V (Icc 0 (1 / ε)) := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
  have hp := equation30_positive (sq_nonneg ε) (by nlinarith)
    (by positivity : 0 ≤ 1 / ε) hscale
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) (1 / ε))
    (fun t ht => (hV t ht.1).continuousAt.continuousWithinAt)
    (fun t ht => (hV t (interior_subset ht).1).hasDerivWithinAt)
  intro t ht
  exact (hp t (interior_subset ht)).2

/-- In inversion coordinates the scalar solution is nonincreasing. -/
theorem invertedScalar_antitone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    AntitoneOn (invertedScalar ε V) (Ioc 0 1) := by
  have hd : ∀ y ∈ Ioc 0 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ y) y := by
    intro y hy
    have harg : 0 ≤ y⁻¹ / ε := div_nonneg (inv_nonneg.mpr hy.1.le) hε.le
    exact (invertedScalar_equations (ne_of_gt hε) (ne_of_gt hy.1)
      (hV _ harg) (hflux _ harg)).1
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc (0 : ℝ) 1)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
  intro y hy
  have hyy := interior_subset hy
  exact (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0 y hyy.1 hyy.2).2.2.le

/-- After `x=1`, the product `t V(t)` is nondecreasing. -/
theorem equation30_weighted_monotone
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    MonotoneOn (fun t => t * V t) (Ici (1 / ε)) := by
  have hanti := invertedScalar_antitone hε hεsmall hV hflux hV0 hV₁0
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hcalc : ∀ r : ℝ, invertedScalar ε V (1 / (ε * r)) = ε * (r * V r) := by
    intro r
    have harg : (1 / (ε * r))⁻¹ / ε = r := by rw [one_div, inv_inv]; field_simp
    rw [invertedScalar, harg, one_div, div_inv_eq_mul]
    ring
  intro s hs t ht hst
  have hthreshold : 0 < 1 / ε := by positivity
  have hspos : 0 < s := hthreshold.trans_le hs
  have htpos : 0 < t := hthreshold.trans_le ht
  have hεs : 1 ≤ ε * s := by have := (div_le_iff₀ hε).mp hs; nlinarith
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; nlinarith
  have hys : 1 / (ε * s) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεs⟩
  have hyt : 1 / (ε * t) ∈ Ioc 0 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr hεt⟩
  have hyorder : 1 / (ε * t) ≤ 1 / (ε * s) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hst hε.le)
  have hm := hanti hyt hys hyorder
  rw [hcalc s, hcalc t] at hm
  exact (mul_le_mul_iff_right₀ hε).mp hm

/-- The reference solution can decrease only by a polynomial factor on a
bounded time interval.  This is the ratio estimate used in the relative
propagator argument. -/
theorem equation30_relative_ratio
    {ε Θ : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ → V s ≤ Θ * V t := by
  have hpos := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0
  have hpre := equation30_prefix_monotone hε hεsmall hV hflux hV0 hV₁0
  have hpost := equation30_weighted_monotone hε hεsmall hV hflux hV0 hV₁0
  have hthreshold : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hthreshold0 : 0 ≤ 1 / ε := by positivity
  intro s t hs hst ht
  have ht0 : 0 ≤ t := hs.trans hst
  have htpos := hpos t ht0
  by_cases htp : t ≤ 1 / ε
  · have hm := hpre ⟨hs, hst.trans htp⟩ ⟨ht0, htp⟩ hst
    nlinarith
  · have htpost : 1 / ε ≤ t := le_of_not_ge htp
    by_cases hsp : s ≤ 1 / ε
    · have hbefore := hpre ⟨hs, hsp⟩ ⟨hthreshold0, le_rfl⟩ hsp
      have hafter := hpost (show 1 / ε ∈ Ici (1 / ε) by simp) htpost htpost
      have hmidpos := hpos (1 / ε) hthreshold0
      nlinarith
    · have hspost : 1 / ε ≤ s := le_of_not_ge hsp
      have hm := hpost hspost htpost hst
      have hspos := hpos s hs
      nlinarith

/-- The exact logarithmic-derivative equation wherever the scalar solution
does not vanish. -/
theorem equation30_hasDerivAt_logderivative
    {ε t : ℝ} {V V₁ : ℝ → ℝ}
    (hV : HasDerivAt V (V₁ t) t)
    (hflux : HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hVne : V t ≠ 0) :
    HasDerivAt (fun s => V₁ s / V s)
      (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
        (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (V₁ t / V t) -
        (V₁ t / V t) ^ 2) t := by
  have hDne : 1 + (ε ^ 2 * t ^ 2) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  apply ((equation30_second_derivative hflux).div hV hVne).congr_deriv
  field_simp

/-- The derivative of `t V(t)` is strictly positive after inversion. -/
theorem equation30_post_inversion_positive_derivative
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 / ε ≤ t → 0 < V t + t * V₁ t := by
  intro t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : 0 < 1 / ε) ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hεt : 1 ≤ ε * t := by have := (div_le_iff₀ hε).mp ht; nlinarith
  have hypos : 0 < 1 / (ε * t) := by positivity
  have hy1 : 1 / (ε * t) ≤ 1 := (div_le_one (by positivity)).mpr hεt
  have hp := (invertedScalar_positive hε hεsmall hV hflux hV0 hV₁0
    (1 / (ε * t)) hypos hy1).2.2
  have harg : (1 / (ε * t))⁻¹ / ε = t := by rw [one_div, inv_inv]; field_simp
  have heq : invertedScalarDeriv ε V V₁ (1 / (ε * t)) =
      -((ε * t) ^ 2 * (V t + t * V₁ t)) := by
    rw [invertedScalarDeriv, harg]
    field_simp
    ring
  rw [heq] at hp
  have hprod : 0 < (ε * t) ^ 2 * (V t + t * V₁ t) := by linarith
  exact pos_of_mul_pos_right hprod (sq_nonneg _)

/-- A uniform absolute logarithmic-derivative bound for the zero-slope
reference solution, valid on the whole forward interval. -/
theorem equation30_zero_slope_logderivative_bound
    {ε : ℝ} {U U₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) :
    ∀ t, 0 ≤ t → |U₁ t / U t| ≤ 2 := by
  have hpos := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hupper : ∀ t, 0 ≤ t → U₁ t / U t ≤ 2 := by
    intro T hT
    have hd : ∀ t ∈ Icc 0 T,
        HasDerivAt (fun s => U₁ s / U s)
          (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) / (1 + (ε ^ 2 * t ^ 2) ^ 2) -
            (4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2)) * (U₁ t / U t) -
            (U₁ t / U t) ^ 2) t :=
      fun t ht => equation30_hasDerivAt_logderivative (hU t ht.1) (hfluxU t ht.1)
        (ne_of_gt (hpos t ht.1))
    have hfence := image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := fun _ => 2) (B' := fun _ => 0)
      (by simp [hU0, hU₁0]) (fun t => hasDerivAt_const t 2)
      (fun t ht hboundary => by
        have ht0 := ht.1
        have hDpos : 0 < 1 + (ε ^ 2 * t ^ 2) ^ 2 := by positivity
        have hDge : 1 ≤ 1 + (ε ^ 2 * t ^ 2) ^ 2 := by
          nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
        have hquo : 2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) /
            (1 + (ε ^ 2 * t ^ 2) ^ 2) ≤ 2 := by
          apply (div_le_iff₀ hDpos).mpr
          nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg (sq_nonneg ε) (sq_nonneg t))]
        have hcoef : 0 ≤ 4 * (ε ^ 2) ^ 2 * t ^ 3 / (1 + (ε ^ 2 * t ^ 2) ^ 2) := by positivity
        rw [hboundary]
        nlinarith)
    exact hfence ⟨hT, le_rfl⟩
  intro t ht
  apply abs_le.mpr
  refine ⟨?_, hupper t ht⟩
  by_cases hpre : t ≤ 1 / ε
  · have hεne : ε ≠ 0 := ne_of_gt hε
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := (equation30_positive (sq_nonneg ε) (by nlinarith)
      (by positivity : 0 ≤ 1 / ε) hscale
      (fun s hs => hU s hs.1) (fun s hs => hfluxU s hs.1) hU0 (by rw [hU₁0]) t ⟨ht, hpre⟩).2
    have hq := div_nonneg hp (hpos t ht).le
    linarith
  · have htpost : 1 / ε ≤ t := le_of_not_ge hpre
    have ht1 : 1 ≤ t := by
      have hbase : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by linarith)
      exact hbase.trans htpost
    have hcomb := equation30_post_inversion_positive_derivative hε hεsmall hU hfluxU hU0
      (by rw [hU₁0]) t htpost
    have hprod : 0 < t * (U₁ t + U t) := by nlinarith [hpos t ht]
    have hsum := pos_of_mul_pos_right hprod ht
    apply (le_div_iff₀ (hpos t ht)).mpr
    linarith [hpos t ht]

/-- Reduction of order normalized by the reference value at the initial
time.  This is the form used for relative, rather than absolute, stability. -/
theorem reduction_of_order_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v t = (u t / u a) * (v a + D a * (v₁ a - (u₁ a / u a) * v a) *
        ∫ s in a..t, (u a / u s) ^ 2 / D s) := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hint : (∫ s in a..t, (u a / u s) ^ 2 / D s) =
      (u a) ^ 2 * ∫ s in a..t, 1 / (D s * (u s) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext s
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hint, reduction_of_order hu hv hfu hfv hDc hD hupos t ht]
  field_simp

/-- The derivative counterpart of normalized reduction of order. -/
theorem reduction_of_order_derivative_relative
    {D c u u₁ v v₁ : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hD : ∀ t ∈ Icc a b, D t ≠ 0) (hupos : ∀ t ∈ Icc a b, u t ≠ 0) :
    ∀ t ∈ Icc a b,
      v₁ t = (u₁ t / u t) * v t +
        (u a / u t) * D a * (v₁ a - (u₁ a / u a) * v a) / D t := by
  intro t ht
  have hane : u a ≠ 0 := hupos a ⟨le_rfl, ht.1.trans ht.2⟩
  have hw := flux_wronskian_constant hu hv hfu hfv t ht
  field_simp [hupos t ht, hD t ht]
  nlinarith [hw]

/-- A polynomial bound for the normalized reduction integral. -/
theorem relative_reduction_integral_bound
    {D u : ℝ → ℝ} {a b Θ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hDc : ContinuousOn D (Icc a b)) (huc : ContinuousOn u (Icc a b))
    (hD : ∀ s ∈ Icc a b, 1 ≤ D s)
    (hu : ∀ s ∈ Icc a b, 0 < u s)
    (hratio : ∀ s ∈ Icc a b, u a ≤ Θ * u s) :
    0 ≤ (∫ s in a..b, (u a / u s) ^ 2 / D s) ∧
      (∫ s in a..b, (u a / u s) ^ 2 / D s) ≤ Θ ^ 3 := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcont : ContinuousOn (fun s => (u a / u s) ^ 2 / D s) (Icc a b) :=
    ((continuousOn_const.div huc (fun s hs => ne_of_gt (hu s hs))).pow 2).div hDc
      (fun s hs => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD s hs)))
  have hint : IntervalIntegrable (fun s => (u a / u s) ^ 2 / D s) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hcont
  have hbound : ∀ s ∈ Icc a b, (u a / u s) ^ 2 / D s ≤ Θ ^ 2 := by
    intro s hs
    have hq0 : 0 ≤ u a / u s := div_nonneg (hu a haI).le (hu s hs).le
    have hq : u a / u s ≤ Θ := (div_le_iff₀ (hu s hs)).mpr (hratio s hs)
    have hΘ0 : 0 ≤ Θ := hq0.trans hq
    have hq2 : (u a / u s) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD s hs))).mpr
    have hm := mul_le_mul_of_nonneg_left (hD s hs) (sq_nonneg Θ)
    nlinarith
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro s hs
    exact div_nonneg (sq_nonneg _) (le_trans zero_le_one (hD s hs))
  · have hi := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Θ ^ 2) MeasureTheory.volume a b) hbound
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    have hm := mul_le_mul_of_nonneg_right (show b - a ≤ Θ by linarith) (sq_nonneg Θ)
    nlinarith

/-- A relative propagator estimate with an explicit polynomial loss.
The large reference amplitude enters only through `u b / u a`. -/
theorem relative_propagator_bound
    {D c u u₁ v v₁ : ℝ → ℝ} {a b Θ : ℝ}
    (hΘ : 1 ≤ Θ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Icc a b, 1 ≤ D t ∧ D t ≤ 2 * Θ ^ 4)
    (hupos : ∀ t ∈ Icc a b, 0 < u t)
    (hlog : ∀ t ∈ Icc a b, |u₁ t / u t| ≤ 2)
    (hratio : ∀ t ∈ Icc a b, u a ≤ Θ * u t) :
    |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * (u b / u a) * (|v a| + |v₁ a|) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have huane : u a ≠ 0 := ne_of_gt (hupos a haI)
  have hubne : u b ≠ 0 := ne_of_gt (hupos b hbI)
  have hDne : ∀ t ∈ Icc a b, D t ≠ 0 :=
    fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one (hD t ht).1)
  have huc : ContinuousOn u (Icc a b) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  let N : ℝ := |v a| + |v₁ a|
  let E : ℝ := v₁ a - (u₁ a / u a) * v a
  let R : ℝ := u b / u a
  let J : ℝ := ∫ s in a..b, (u a / u s) ^ 2 / D s
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hR : 0 < R := div_pos (hupos b hbI) (hupos a haI)
  have hJ := relative_reduction_integral_bound ha hab hb hDc huc
    (fun t ht => (hD t ht).1) hupos hratio
  change 0 ≤ J ∧ J ≤ Θ ^ 3 at hJ
  have hE : |E| ≤ 2 * N := by
    calc
      |E| ≤ |v₁ a| + |(u₁ a / u a) * v a| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (v₁ a) ((u₁ a / u a) * v a)
      _ = |v₁ a| + |u₁ a / u a| * |v a| := by rw [abs_mul]
      _ ≤ |v₁ a| + 2 * |v a| := by
        linarith [mul_le_mul_of_nonneg_right (hlog a haI) (abs_nonneg (v a))]
      _ ≤ 2 * N := by dsimp [N]; linarith [abs_nonneg (v₁ a)]
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow78 : Θ ^ 7 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow68 : Θ ^ 6 ≤ Θ ^ 8 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow8 : 1 ≤ Θ ^ 8 := one_le_pow₀ hΘ
  have hDNJ : D a * |E| * J ≤ 4 * Θ ^ 8 * N := by
    have hm := mul_le_mul
      (mul_le_mul (hD a haI).2 hE (abs_nonneg _) (by positivity)) hJ.2 hJ.1 (by positivity)
    have hp := mul_le_mul_of_nonneg_right hpow78 (show 0 ≤ 4 * N by positivity)
    nlinarith
  have hval := reduction_of_order_relative hu hv hfu hfv hDc hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  change v b = R * (v a + D a * E * J) at hval
  have hvbound : |v b| ≤ R * (5 * Θ ^ 8 * N) := by
    rw [hval, abs_mul, abs_of_pos hR]
    apply mul_le_mul_of_nonneg_left _ hR.le
    have htri := abs_add_le (v a) (D a * E * J)
    have hDan : 0 ≤ D a := le_trans zero_le_one (hD a haI).1
    rw [abs_mul, abs_mul, abs_of_nonneg hDan, abs_of_nonneg hJ.1] at htri
    have hn : |v a| ≤ N := by dsimp [N]; linarith [abs_nonneg (v₁ a)]
    have hp := mul_le_mul_of_nonneg_right hpow8 hN
    nlinarith
  have hq0 : 0 ≤ u a / u b := div_nonneg (hupos a haI).le (hupos b hbI).le
  have hq : u a / u b ≤ Θ := (div_le_iff₀ (hupos b hbI)).mpr (hratio b hbI)
  have hq2 : (u a / u b) ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hq0 hΘ0).mpr hq
  have hsecond : (u a / u b) ^ 2 * D a * |E| / D b ≤ 4 * Θ ^ 8 * N := by
    have hnum : (u a / u b) ^ 2 * D a * |E| ≤ 4 * Θ ^ 8 * N := by
      have hm := mul_le_mul
        (mul_le_mul hq2 (hD a haI).2 (le_trans zero_le_one (hD a haI).1) (sq_nonneg Θ))
        hE (abs_nonneg _) (by positivity)
      have hp := mul_le_mul_of_nonneg_right hpow68 (show 0 ≤ 4 * N by positivity)
      nlinarith
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hD b hbI).1)).mpr
    have hm := mul_le_mul_of_nonneg_left (hD b hbI).1 (show 0 ≤ 4 * Θ ^ 8 * N by positivity)
    nlinarith
  have hder := reduction_of_order_derivative_relative hu hv hfu hfv hDne
    (fun t ht => ne_of_gt (hupos t ht)) b hbI
  have heq : (u a / u b) * D a * E / D b = R * ((u a / u b) ^ 2 * D a * E / D b) := by
    dsimp [R]
    field_simp
  change v₁ b = (u₁ b / u b) * v b + (u a / u b) * D a * E / D b at hder
  rw [heq] at hder
  have hv₁bound : |v₁ b| ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
    rw [hder]
    calc
      |(u₁ b / u b) * v b + R * ((u a / u b) ^ 2 * D a * E / D b)|
          ≤ |(u₁ b / u b) * v b| + |R * ((u a / u b) ^ 2 * D a * E / D b)| := abs_add_le _ _
      _ = |u₁ b / u b| * |v b| + R * ((u a / u b) ^ 2 * D a * |E| / D b) := by
        simp only [abs_mul, abs_div, abs_pow, abs_of_pos hR,
          abs_of_pos (hupos a haI), abs_of_pos (hupos b hbI),
          abs_of_nonneg (le_trans zero_le_one (hD a haI).1),
          abs_of_nonneg (le_trans zero_le_one (hD b hbI).1)]
      _ ≤ 2 * |v b| + R * (4 * Θ ^ 8 * N) := by
        exact add_le_add (mul_le_mul_of_nonneg_right (hlog b hbI) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsecond hR.le)
  change |v b| + |v₁ b| ≤ 20 * Θ ^ 8 * R * N
  have hRN : 0 ≤ Θ ^ 8 * R * N := by positivity
  nlinarith

/-- The ideal scalar propagator has only a polynomial loss relative to the
zero-slope growing solution.  This proves the reference propagator estimate
used before (32), with the explicit constant `20`. -/
theorem equation30_relative_propagator
    {ε Θ a b : ℝ} {U U₁ Y Y₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t) t) :
    |Y b| + |Y₁ b| ≤ 20 * Θ ^ 8 * (U b / U a) * (|Y a| + |Y₁ a|) := by
  have hp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hl := equation30_zero_slope_logderivative_bound hε hεsmall hU hfluxU hU0 hU₁0
  have hr := equation30_relative_ratio hε hεsmall hΘ hU hfluxU hU0 (by rw [hU₁0])
  apply relative_propagator_bound hΘ ha hab hb
    (fun t ht => hU t (ha.trans ht.1)) hY
    (fun t ht => hfluxU t (ha.trans ht.1)) hfluxY (by fun_prop)
  · intro t ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have htΘ : t ≤ Θ := ht.2.trans hb
    have heps4 : ε ^ 4 ≤ 1 := by
      simpa using pow_le_pow_left₀ hε.le (show ε ≤ 1 by linarith) 4
    have ht4 : t ^ 4 ≤ Θ ^ 4 := pow_le_pow_left₀ ht0 htΘ 4
    have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
    have hm := mul_le_mul heps4 ht4 (by positivity : 0 ≤ t ^ 4) (by norm_num : (0 : ℝ) ≤ 1)
    constructor <;> nlinarith [sq_nonneg (ε ^ 2 * t ^ 2)]
  · intro t ht
    exact hp t (ha.trans ht.1)
  · intro t ht
    exact hl t (ha.trans ht.1)
  · intro t ht
    exact hr a t ha ht.1 (ht.2.trans hb)

/-- The coarse upper barrier for the exact inverted Riccati equation. -/
theorem inverted_riccati_le_four
    {ε T : ℝ} {z : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hscale : ε * T ≤ 1)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (invertedRiccati ε t (z t)) t)
    (hz0 : z 0 ≤ 4) :
    ∀ t ∈ Icc 0 T, z t ≤ 4 := by
  apply riccati_le_four hz hz0
  · intro t ht
    have ht0 := ht.1
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    nlinarith [mul_nonneg (sq_nonneg ε) (sq_nonneg (1 - ε * t)),
      show 0 ≤ (1 - ε * t) ^ 4 by positivity]
  · intro t ht
    have hprod := mul_le_mul_of_nonneg_left ht.2.le hε.le
    have hprod0 := mul_nonneg hε.le ht.1
    have hy0 : 0 ≤ 1 - ε * t := by linarith
    have hy1 : 1 - ε * t ≤ 1 := by linarith
    have hy3 : (1 - ε * t) ^ 3 ≤ 1 := by
      simpa using pow_le_pow_left₀ hy0 hy1 3
    have hDpos : 0 < 1 + (1 - ε * t) ^ 4 := by positivity
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 4 * ε by positivity)
    nlinarith [show 0 ≤ (1 - ε * t) ^ 4 by positivity]

/-- The inverted logarithmic derivative remains in `[0,4]`, derived
directly from the scalar equation and its endpoint conditions. -/
theorem inversion_riccati_range
    {ε a : ℝ} {f f₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (ha : 0 ≤ a)
    (hf : ∀ y ∈ Icc a 1, HasDerivAt f (f₁ y) y)
    (hflux : ∀ y ∈ Icc a 1, HasDerivAt (fun z => (1 + z ^ 4) * f₁ z)
      ((2 / ε ^ 2 - 2 * y ^ 2) * f y) y)
    (hf1 : 0 < f 1) (hf₁1 : f₁ 1 < 0)
    (hinit : -ε * f₁ 1 / f 1 ≤ 4) :
    ∀ y ∈ Icc a 1, 0 ≤ -ε * f₁ y / f y ∧ -ε * f₁ y / f y ≤ 4 := by
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hp := inversion_positive (sq_pos_of_pos hε) (by nlinarith : ε ^ 2 ≤ 1)
    ha hf hflux hf1 hf₁1
  have hmirror : ∀ t ∈ Icc 0 ((1 - a) / ε), 1 - ε * t ∈ Icc a 1 := by
    intro t ht
    have hu : ε * t ≤ 1 - a := by
      have := (le_div_iff₀ hε).mp ht.2
      nlinarith
    have hl := mul_nonneg hε.le ht.1
    constructor <;> linarith
  have hscale : ε * ((1 - a) / ε) ≤ 1 := by field_simp; linarith
  have hz : ∀ t ∈ Icc 0 ((1 - a) / ε),
      HasDerivAt (fun s => -ε * f₁ (1 - ε * s) / f (1 - ε * s))
        (invertedRiccati ε t (-ε * f₁ (1 - ε * t) / f (1 - ε * t))) t := by
    intro t ht
    exact hasDerivAt_inverted_logderivative hεne
      (ne_of_gt (hp (1 - ε * t) (hmirror t ht)).2.1)
      (hf _ (hmirror t ht)) (hflux _ (hmirror t ht))
  have hbound := inverted_riccati_le_four hε hεsmall hscale hz (by simpa using hinit)
  intro y hy
  have ht : (1 - y) / ε ∈ Icc 0 ((1 - a) / ε) :=
    ⟨div_nonneg (sub_nonneg.mpr hy.2) hε.le,
      div_le_div_of_nonneg_right (by linarith [hy.1]) hε.le⟩
  have heq : 1 - ε * ((1 - y) / ε) = y := by field_simp; ring
  constructor
  · exact div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hε.le) (hp y hy).2.2.le) (hp y hy).2.1.le
  · simpa only [heq] using hbound ((1 - y) / ε) ht

/-- The absolute Riccati range for the original scalar initial value problem. -/
theorem equation30_inverted_riccati_range
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 →
      0 ≤ -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ∧
      -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y ≤ 4 := by
  have hinit := invertedScalar_initial_bound hε hεsmall
    (fun t ht => hV t ht.1) (fun t ht => hflux t ht.1) hV0 hV₁0
  intro y hy hy1
  have heqs : ∀ s ∈ Icc y 1,
      HasDerivAt (invertedScalar ε V) (invertedScalarDeriv ε V V₁ s) s ∧
      HasDerivAt (fun z => (1 + z ^ 4) * invertedScalarDeriv ε V V₁ z)
        ((2 / ε ^ 2 - 2 * s ^ 2) * invertedScalar ε V s) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hy hs.1
    have harg : 0 ≤ s⁻¹ / ε := by positivity
    exact invertedScalar_equations (ne_of_gt hε) (ne_of_gt hspos)
      (hV _ harg) (hflux _ harg)
  exact inversion_riccati_range hε hεsmall hy.le
    (fun s hs => (heqs s hs).1) (fun s hs => (heqs s hs).2)
    hinit.1 hinit.2.1 hinit.2.2 y ⟨le_rfl, hy1⟩

/-- The ideal next-frame numerator in inversion coordinates. -/
def idealFrameNumerator (ε y z : ℝ) : ℝ :=
  -1 + (1 + y ^ 4) * z ^ 2 + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3

/-- The ideal next-frame denominator divided by `x²`, where `y=1/x`. -/
def idealFrameDenominator (ε y z : ℝ) : ℝ :=
  1 - ε ^ 2 * y ^ 2 + 2 * ε * z * y ^ 3

/-- The two exact algebraic identities used for the ideal frame renewal. -/
theorem ideal_frame_identities {ε y z : ℝ} (hy : y ≠ 0) :
    (y⁻¹) ^ 2 + ε ^ 2 + (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) =
      idealFrameDenominator ε y z / y ^ 2 ∧
    -1 + ε ^ 2 * (y⁻¹) ^ 2 + (1 + (y⁻¹) ^ 4) * (ε * y - z * y ^ 2) ^ 2 +
      (y⁻¹) ^ 2 * (-2 * ε * y⁻¹) * (ε * y - z * y ^ 2) = idealFrameNumerator ε y z := by
  constructor <;> simp only [idealFrameDenominator, idealFrameNumerator] <;> field_simp <;> ring

/-- Explicit ideal frame-renewal bounds obtained from the Riccati estimate.
The constants are deliberately generous absolute constants. -/
theorem ideal_frame_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4)
    (herr : |z ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε) :
    1 / 2 ≤ idealFrameDenominator ε y z ∧
      |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
      |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  have hy1 : y ≤ 1 := by linarith
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have hy3 : y ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hy hy1 3
  have hy4 : y ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ hy hy1 4
  have hy3n : 0 ≤ y ^ 3 := by positivity
  have hy4n : 0 ≤ y ^ 4 := by positivity
  have hDpos : 0 < 1 + y ^ 4 := by positivity
  have hDn : 0 ≤ 1 + y ^ 4 := hDpos.le
  have hTn : 0 ≤ ε ^ 2 * y ^ 2 := by positivity
  have hTsmall : ε ^ 2 * y ^ 2 ≤ 1 / 16 := by
    have hm := mul_le_mul_of_nonneg_left hy2 (sq_nonneg ε)
    nlinarith
  have hTε : ε ^ 2 * y ^ 2 ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hy2 (sq_nonneg ε)
    nlinarith
  have hUn : 0 ≤ 2 * ε * z * y ^ 3 := by positivity
  have hUlocal : 2 * ε * z * y ^ 3 ≤ 8 * ε * y ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hzupper (show 0 ≤ 2 * ε * y ^ 3 by positivity)
    nlinarith
  have hUε : 2 * ε * z * y ^ 3 ≤ 8 * ε := by
    have hm := mul_le_mul_of_nonneg_left hy3 (show 0 ≤ 8 * ε by positivity)
    nlinarith
  have hB : 1 / 2 ≤ idealFrameDenominator ε y z := by
    unfold idealFrameDenominator
    nlinarith only [hTsmall, hUn]
  have hroot : 1 ≤ sqrt (1 + y ^ 4) := one_le_sqrt.mpr (by linarith)
  have hrootpos : 0 < sqrt (1 + y ^ 4) := by linarith
  have hrootupper : sqrt (1 + y ^ 4) ≤ 1 + y ^ 4 :=
    sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hDerr : |(1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4))| ≤ 720 * ε := by
    rw [abs_mul, abs_of_nonneg hDn]
    have hm := mul_le_mul_of_nonneg_left herr hDn
    have hu := mul_le_mul_of_nonneg_right (show 1 + y ^ 4 ≤ 2 by linarith)
      (show 0 ≤ 360 * ε by positivity)
    nlinarith only [hm, hu]
  have hNrewrite : idealFrameNumerator ε y z - 1 =
      (1 + y ^ 4) * (z ^ 2 - 2 / (1 + y ^ 4)) + ε ^ 2 * y ^ 2 - 2 * ε * z * y ^ 3 := by
    unfold idealFrameNumerator
    field_simp
    ring
  have hN : |idealFrameNumerator ε y z - 1| ≤ 730 * ε := by
    rw [hNrewrite]
    obtain ⟨hl, hu⟩ := abs_le.mp hDerr
    apply abs_le.mpr
    constructor <;> nlinarith only [hl, hu, hTn, hTε, hUn, hUε, hε]
  have hA : |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
    have heq : idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1 =
        (idealFrameDenominator ε y z - sqrt (1 + y ^ 4)) / sqrt (1 + y ^ 4) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hrootpos]
    apply (div_le_iff₀ hrootpos).mpr
    have hsmall : |idealFrameDenominator ε y z - sqrt (1 + y ^ 4)| ≤
        y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 := by
      unfold idealFrameDenominator
      apply abs_le.mpr
      have h8 : 0 ≤ 8 * ε * y ^ 3 := by positivity
      constructor <;> nlinarith only [hroot, hrootupper, hUlocal, hTn, hUn, hy4n, h8]
    have hm := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 by positivity)
    nlinarith only [hsmall, hm]
  refine ⟨hB, hN, hA, ?_⟩
  have hBpos : 0 < idealFrameDenominator ε y z := by linarith
  have heq : idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1 =
      (idealFrameNumerator ε y z - idealFrameDenominator ε y z) / idealFrameDenominator ε y z := by
    field_simp
  rw [heq, abs_div, abs_of_pos hBpos]
  apply (div_le_iff₀ hBpos).mpr
  have hdiff : |idealFrameNumerator ε y z - idealFrameDenominator ε y z| ≤ 739 * ε := by
    obtain ⟨hl, hu⟩ := abs_le.mp hN
    unfold idealFrameDenominator
    apply abs_le.mpr
    constructor <;> nlinarith only [hl, hu, hTn, hTε, hUn, hUε]
  have hm := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1500 * ε by positivity)
  nlinarith only [hdiff, hm, hε]

/-- Ideal frame renewal follows from the scalar initial value problem;
the Riccati range and approximation are proved upstream in this file. -/
theorem equation30_ideal_frame_bounds
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ y, 0 < y → y ≤ 1 / 2 →
      let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
      1 / 2 ≤ idealFrameDenominator ε y z ∧
        |idealFrameNumerator ε y z - 1| ≤ 730 * ε ∧
        |idealFrameDenominator ε y z / sqrt (1 + y ^ 4) - 1| ≤
          y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
        |idealFrameNumerator ε y z / idealFrameDenominator ε y z - 1| ≤ 1500 * ε := by
  intro y hy hysmall
  have hr := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith)
  have he := equation30_inverted_riccati_error hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  exact ideal_frame_bounds hε.le hεsmall hy.le hysmall hr.1 hr.2 he

/-- The ideal shear contribution to the target-frame compression has the
required negative sign and reciprocal target-scale lower magnitude. -/
theorem ideal_target_compression
    {H ε x : ℝ} (hH : 0 ≤ H) (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    -2 * H * ε * x ^ 3 / (1 + x ^ 4) ≤ -H * ε / x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hDpos : 0 < 1 + x ^ 4 := by positivity
  apply (div_le_div_iff₀ hDpos hxpos).mpr
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hp := mul_nonneg (mul_nonneg hH hε) (sub_nonneg.mpr hx4)
  nlinarith

end EulerPacketGrowth

end

section

/-!
Relative perturbation estimates for the finite-dimensional scalar ODE in the
Euler packet proposal.  These results do not assert the PDE packet lemma.
-/

namespace EulerPacketPerturbation

open Set Filter Real EulerPacketGrowth
open scoped Topology

/-- A compact-interval Volterra absorption estimate with an explicit factor
of two and no exponential loss. -/
theorem integral_absorb
    {g : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hgn : ∀ t ∈ Icc a b, 0 ≤ g t) (hK : 0 ≤ K)
    (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b, g t ≤ A + K * ∫ s in a..t, g s) :
    ∀ t ∈ Icc a b, g t ≤ 2 * A := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_rfl, hab⟩⟩ hg
  have hsubset : uIcc a c ⊆ Icc a b := by
    rw [uIcc_of_le hc.1]
    exact Icc_subset_Icc le_rfl hc.2
  have hgi : IntervalIntegrable g MeasureTheory.volume a c :=
    (hg.mono hsubset).intervalIntegrable
  have hi := intervalIntegral.integral_mono_on hc.1 hgi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => g c) MeasureTheory.volume a c)
    (fun t ht => hmax (Icc_subset_Icc le_rfl hc.2 ht))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hKi := mul_le_mul_of_nonneg_left hi hK
  have hKc : K * (c - a) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hc.2 hK
    nlinarith
  have hmaxn : 0 ≤ g c := hgn c hc
  have hscaled := mul_le_mul_of_nonneg_right hKc hmaxn
  have hgc : g c ≤ 2 * A := by nlinarith [hineq c hc]
  intro t ht
  exact (hmax ht).trans hgc

/-- Absorbing a Duhamel inequality after division by a positive reference
solution.  This preserves relative rather than absolute control. -/
theorem relative_integral_absorb
    {f U : ℝ → ℝ} {a b A K : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hU : ContinuousOn U (Icc a b))
    (hfn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hUp : ∀ t ∈ Icc a b, 0 < U t)
    (hK : 0 ≤ K) (hsmall : K * (b - a) ≤ 1 / 2)
    (hineq : ∀ t ∈ Icc a b,
      f t ≤ U t * (A + K * ∫ s in a..t, f s / U s)) :
    ∀ t ∈ Icc a b, f t ≤ 2 * A * U t := by
  have hg := integral_absorb (g := fun t => f t / U t) (A := A) (K := K) hab
    (hf.div hU (fun t ht => ne_of_gt (hUp t ht)))
    (fun t ht => div_nonneg (hfn t ht) (hUp t ht).le) hK hsmall
    (fun t ht => by
      apply (div_le_iff₀ (hUp t ht)).mpr
      convert! hineq t ht using 1
      ring)
  intro t ht
  exact (div_le_iff₀ (hUp t ht)).mp (hg t ht)

/-- The Wronskian of a homogeneous solution and a forced solution obeys an
exact first-order forcing identity. -/
theorem forced_wronskian_derivative
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : HasDerivAt Y (Y₁ t + f t) t)
    (hfY : HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t) :
    HasDerivAt (fun s => u s * (D s * Y₁ s) - (D s * u₁ s) * Y s)
      (D t * (u t * g t - u₁ t * f t)) t := by
  apply ((hu.mul hfY).sub (hfu.mul hY)).congr_deriv
  ring

/-- The integrated forced Wronskian identity. -/
theorem forced_wronskian_integral
    {D c u u₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      u t * (D t * Y₁ t) - (D t * u₁ t) * Y t =
        u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
          ∫ s in a..t, D s * (u s * g s - u₁ s * f s) := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hcont := hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (hcont.mono hsubset).intervalIntegrable (μ := MeasureTheory.volume)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => forced_wronskian_derivative (hu s (hsubset hs)) (hfu s (hsubset hs))
      (hY s (hsubset hs)) (hfY s (hsubset hs))) hint
  linarith

/-- Variation of constants from two homogeneous solutions whose Wronskian
flux is normalized to one.  This handles forcing in both state components. -/
theorem forced_variation_of_constants
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      let A := u a * (D a * Y₁ a) - (D a * u₁ a) * Y a +
        ∫ s in a..t, D s * (u s * g s - u₁ s * f s)
      let B := v a * (D a * Y₁ a) - (D a * v₁ a) * Y a +
        ∫ s in a..t, D s * (v s * g s - v₁ s * f s)
      Y t = v t * A - u t * B ∧ Y₁ t = v₁ t * A - u₁ t * B := by
  intro t ht
  have hWu := forced_wronskian_integral hu hfu hY hfY hDc hu₁c hfc hgc t ht
  have hWv := forced_wronskian_integral hv hfv hY hfY hDc hv₁c hfc hgc t ht
  have hW := flux_wronskian_constant hu hv hfu hfv t ht
  rw [hW0] at hW
  dsimp only
  rw [← hWu, ← hWv]
  constructor
  · nlinarith [congrArg (fun r : ℝ => r * Y t) hW]
  · nlinarith [congrArg (fun r : ℝ => r * Y₁ t) hW]

/-- First displacement component of the scalar fundamental propagator. -/
def kernel11 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u t * v₁ s - v t * u₁ s)

/-- First velocity component of the scalar fundamental propagator. -/
def kernel12 (D u v : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v t * u s - u t * v s)

/-- Second displacement component of the scalar fundamental propagator. -/
def kernel21 (D u₁ v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (u₁ t * v₁ s - v₁ t * u₁ s)

/-- Second velocity component of the scalar fundamental propagator. -/
def kernel22 (D u u₁ v v₁ : ℝ → ℝ) (t s : ℝ) : ℝ :=
  D s * (v₁ t * u s - u₁ t * v s)

/-- Duhamel's formula in component form, with an explicitly defined
fundamental kernel. -/
theorem forced_kernel_formula
    {D c u u₁ v v₁ Y Y₁ f g : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u₁ t) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (v₁ t) t)
    (hfu : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : ∀ t ∈ Icc a b, HasDerivAt (fun s => D s * v₁ s) (c t * v t) t)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => D s * Y₁ s) (c t * Y t + D t * g t) t)
    (hDc : ContinuousOn D (Icc a b)) (hu₁c : ContinuousOn u₁ (Icc a b))
    (hv₁c : ContinuousOn v₁ (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hW0 : u a * (D a * v₁ a) - (D a * u₁ a) * v a = 1) :
    ∀ t ∈ Icc a b,
      Y t = kernel11 D u u₁ v v₁ t a * Y a + kernel12 D u v t a * Y₁ a +
        ∫ s in a..t, kernel11 D u u₁ v v₁ t s * f s + kernel12 D u v t s * g s ∧
      Y₁ t = kernel21 D u₁ v₁ t a * Y a + kernel22 D u u₁ v v₁ t a * Y₁ a +
        ∫ s in a..t, kernel21 D u₁ v₁ t s * f s + kernel22 D u u₁ v v₁ t s * g s := by
  intro t ht
  have huc : ContinuousOn u (Icc a b) := fun s hs => (hu s hs).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun s hs => (hv s hs).continuousAt.continuousWithinAt
  have hsubset : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hIu := ((hDc.mul ((huc.mul hgc).sub (hu₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  have hIv := ((hDc.mul ((hvc.mul hgc).sub (hv₁c.mul hfc))).mono hsubset).intervalIntegrable
    (μ := MeasureTheory.volume)
  change IntervalIntegrable (fun s => D s * (u s * g s - u₁ s * f s)) MeasureTheory.volume a t at hIu
  change IntervalIntegrable (fun s => D s * (v s * g s - v₁ s * f s)) MeasureTheory.volume a t at hIv
  have hInt (A B : ℝ) :
      (∫ s in a..t, D s * (A * v₁ s - B * u₁ s) * f s +
        D s * (B * u s - A * v s) * g s) =
      B * (∫ s in a..t, D s * (u s * g s - u₁ s * f s)) -
        A * (∫ s in a..t, D s * (v s * g s - v₁ s * f s)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hIu.const_mul B) (hIv.const_mul A)]
    congr 1
    ext s
    ring
  have hvar := forced_variation_of_constants hu hv hfu hfv hY hfY hDc hu₁c hv₁c hfc hgc hW0 t ht
  dsimp only at hvar
  constructor
  · unfold kernel11 kernel12
    rw [hInt (u t) (v t), hvar.1]
    ring
  · unfold kernel21 kernel22
    rw [hInt (u₁ t) (v₁ t), hvar.2]
    ring

/-- Linear combinations of homogeneous scalar solutions are homogeneous. -/
theorem linear_combination_solution
    {D c u u₁ v v₁ : ℝ → ℝ} {t A B : ℝ}
    (hu : HasDerivAt u (u₁ t) t) (hv : HasDerivAt v (v₁ t) t)
    (hfu : HasDerivAt (fun s => D s * u₁ s) (c t * u t) t)
    (hfv : HasDerivAt (fun s => D s * v₁ s) (c t * v t) t) :
    HasDerivAt (fun s => A * u s + B * v s) (A * u₁ t + B * v₁ t) t ∧
    HasDerivAt (fun s => D s * (A * u₁ s + B * v₁ s))
      (c t * (A * u t + B * v t)) t := by
  constructor
  · exact (hu.const_mul A).add (hv.const_mul B)
  · convert! (hfu.const_mul A).add (hfv.const_mul B) using 1
    · ext s
      dsimp only [Pi.add_apply]
      ring
    · ring

/-- The ideal fundamental kernel inherits the relative propagator bound
in each column. -/
theorem equation30_kernel_bound
    {ε Θ : ℝ} {U U₁ V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1) :
    ∀ s t, 0 ≤ s → s ≤ t → t ≤ Θ →
      let D := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
      |kernel11 D U U₁ V V₁ t s| + |kernel21 D U₁ V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) ∧
      |kernel12 D U V t s| + |kernel22 D U U₁ V V₁ t s| ≤
        20 * Θ ^ 8 * (U t / U s) := by
  intro s t hs hst ht
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hW : U s * (D s * V₁ s) - (D s * U₁ s) * V s = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := s) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) s ⟨hs, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hlin (A B : ℝ) :
      |A * U t + B * V t| + |A * U₁ t + B * V₁ t| ≤
        20 * Θ ^ 8 * (U t / U s) *
          (|A * U s + B * V s| + |A * U₁ s + B * V₁ s|) := by
    exact equation30_relative_propagator hε hεsmall hΘ hs hst ht hU hfluxU hU0 hU₁0
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).1)
      (fun r hr => (linear_combination_solution (A := A) (B := B) (D := D) (c := c)
        (hU r (hs.trans hr.1)) (hV r (hs.trans hr.1))
        (hfluxU r (hs.trans hr.1)) (hfluxV r (hs.trans hr.1))).2)
  constructor
  · have hb := hlin (D s * V₁ s) (-(D s * U₁ s))
    have hfirst : D s * V₁ s * U s + -(D s * U₁ s) * V s = 1 := by nlinarith [hW]
    have hsecond : D s * V₁ s * U₁ s + -(D s * U₁ s) * V₁ s = 0 := by ring
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel11, kernel21, D] <;> ring
  · have hb := hlin (-(D s * V s)) (D s * U s)
    have hfirst : -(D s * V s) * U s + D s * U s * V s = 0 := by ring
    have hsecond : -(D s * V s) * U₁ s + D s * U s * V₁ s = 1 := by nlinarith [hW]
    rw [hfirst, hsecond] at hb
    norm_num at hb
    convert! hb using 1
    congr 2 <;> dsimp [kernel12, kernel22, D] <;> ring

/-- The induced sum-of-absolute-values bound from two column bounds. -/
theorem two_column_bound {a b c d x y C : ℝ}
    (h1 : |a| + |c| ≤ C) (h2 : |b| + |d| ≤ C) :
    |a * x + b * y| + |c * x + d * y| ≤ C * (|x| + |y|) := by
  have hfirst := abs_add_le (a * x) (b * y)
  have hsecond := abs_add_le (c * x) (d * y)
  simp only [abs_mul] at hfirst hsecond
  have hx := mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
  have hy := mul_le_mul_of_nonneg_right h2 (abs_nonneg y)
  nlinarith

/-- Passing from Duhamel's formula and relative kernel bounds to a scalar
relative integral inequality, with the forcing in both components. -/
theorem kernel_integral_bound
    {K11 K12 K21 K22 f g U : ℝ → ℝ} {a b y0 y₁0 y y₁ C : ℝ}
    (hab : a ≤ b)
    (h11 : ContinuousOn K11 (Icc a b)) (h12 : ContinuousOn K12 (Icc a b))
    (h21 : ContinuousOn K21 (Icc a b)) (h22 : ContinuousOn K22 (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hUc : ContinuousOn U (Icc a b)) (hUp : ∀ s ∈ Icc a b, 0 < U s)
    (hcol1 : ∀ s ∈ Icc a b, |K11 s| + |K21 s| ≤ C * (U b / U s))
    (hcol2 : ∀ s ∈ Icc a b, |K12 s| + |K22 s| ≤ C * (U b / U s))
    (hy : y = K11 a * y0 + K12 a * y₁0 + ∫ s in a..b, K11 s * f s + K12 s * g s)
    (hy₁ : y₁ = K21 a * y0 + K22 a * y₁0 + ∫ s in a..b, K21 s * f s + K22 s * g s) :
    |y| + |y₁| ≤ C * (U b / U a) * (|y0| + |y₁0|) +
      C * U b * ∫ s in a..b, (|f s| + |g s|) / U s := by
  have hc1 := (h11.mul hfc).add (h12.mul hgc)
  have hc2 := (h21.mul hfc).add (h22.mul hgc)
  have hi1 : IntervalIntegrable (fun s => |K11 s * f s + K12 s * g s|)
      MeasureTheory.volume a b := hc1.abs.intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun s => |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hc2.abs.intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun s => |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s|)
      MeasureTheory.volume a b := hi1.add hi2
  have hquot : ContinuousOn (fun s => (|f s| + |g s|) / U s) (Icc a b) :=
    (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s hs))
  have hmajor : IntervalIntegrable (fun s => (C * U b) * ((|f s| + |g s|) / U s))
      MeasureTheory.volume a b :=
    (hquot.intervalIntegrable_of_Icc hab).const_mul (C * U b)
  have hpoint : ∀ s ∈ Icc a b,
      |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| ≤
        C * U b * ((|f s| + |g s|) / U s) := by
    intro s hs
    convert! two_column_bound (x := f s) (y := g s) (hcol1 s hs) (hcol2 s hs) using 1
    ring
  have hmono := intervalIntegral.integral_mono_on hab hsum hmajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI : |∫ s in a..b, K11 s * f s + K12 s * g s| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| ≤
      ∫ s in a..b, |K11 s * f s + K12 s * g s| + |K21 s * f s + K22 s * g s| := by
    rw [intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (intervalIntegral.abs_integral_le_integral_abs hab)
      (intervalIntegral.abs_integral_le_integral_abs hab)
  have hbase := two_column_bound (x := y0) (y := y₁0)
    (hcol1 a ⟨le_rfl, hab⟩) (hcol2 a ⟨le_rfl, hab⟩)
  have hfirst : |y| ≤ |K11 a * y0 + K12 a * y₁0| +
      |∫ s in a..b, K11 s * f s + K12 s * g s| := by rw [hy]; exact abs_add_le _ _
  have hsecond : |y₁| ≤ |K21 a * y0 + K22 a * y₁0| +
      |∫ s in a..b, K21 s * f s + K22 s * g s| := by rw [hy₁]; exact abs_add_le _ _
  linarith

/-- Duhamel's inequality for the exact scalar ODE, measured relative to the
zero-slope reference solution.  The forcing may occur in both components. -/
theorem equation30_forced_bound
    {ε Θ a b : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hb : b ≤ Θ)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
        20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := by
  let D : ℝ → ℝ := fun r => 1 + (ε ^ 2 * r ^ 2) ^ 2
  let c : ℝ → ℝ := fun r => 2 * (1 - ε ^ 2 * (ε ^ 2 * r ^ 2))
  have hUc : ContinuousOn U (Icc a b) :=
    fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc a b) :=
    fun t ht => (hV t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hU₁c : ContinuousOn U₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxU t (ha.trans ht.1))).continuousAt.continuousWithinAt
  have hV₁c : ContinuousOn V₁ (Icc a b) :=
    fun t ht => (equation30_second_derivative (hfluxV t (ha.trans ht.1))).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc a b) := by fun_prop
  have hW : U a * (D a * V₁ a) - (D a * U₁ a) * V a = 1 := by
    have hw := flux_wronskian_constant
      (a := 0) (b := a) (D := D) (c := c)
      (fun r hr => hU r hr.1) (fun r hr => hV r hr.1)
      (fun r hr => hfluxU r hr.1) (fun r hr => hfluxV r hr.1) a ⟨ha, le_rfl⟩
    simpa [D, hU0, hU₁0, hV₁0] using hw
  have hformula := forced_kernel_formula
    (D := D) (c := c)
    (fun r hr => hU r (ha.trans hr.1)) (fun r hr => hV r (ha.trans hr.1))
    (fun r hr => hfluxU r (ha.trans hr.1)) (fun r hr => hfluxV r (ha.trans hr.1))
    hY hfluxY hDc hU₁c hV₁c hfc hgc hW
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hkernel := equation30_kernel_bound hε hεsmall hΘ hU hV hfluxU hfluxV hU0 hU₁0 hV₁0
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hUc' := hUc.mono hsub
  have hVc' := hVc.mono hsub
  have hU₁c' := hU₁c.mono hsub
  have hV₁c' := hV₁c.mono hsub
  have hDc' := hDc.mono hsub
  have h11 : ContinuousOn (kernel11 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel11
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h12 : ContinuousOn (kernel12 D U V t) (Icc a t) := by
    unfold kernel12
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  have h21 : ContinuousOn (kernel21 D U₁ V₁ t) (Icc a t) := by
    unfold kernel21
    exact hDc'.mul ((continuousOn_const.mul hV₁c').sub (continuousOn_const.mul hU₁c'))
  have h22 : ContinuousOn (kernel22 D U U₁ V V₁ t) (Icc a t) := by
    unfold kernel22
    exact hDc'.mul ((continuousOn_const.mul hUc').sub (continuousOn_const.mul hVc'))
  exact kernel_integral_bound ht.1 h11 h12 h21 h22 (hfc.mono hsub) (hgc.mono hsub) hUc'
    (fun s hs => hUp s (ha.trans hs.1))
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).1)
    (fun s hs => (hkernel s t (ha.trans hs.1) hs.2 (ht.2.trans hb)).2)
    (hformula t ht).1 (hformula t ht).2

/-- Continuity of the second state component follows from continuity of its
nonvanishing flux coefficient and of the flux. -/
theorem continuousOn_of_flux
    {D f : ℝ → ℝ} {S : Set ℝ}
    (hD : ContinuousOn D S) (hf : ContinuousOn (fun t => D t * f t) S)
    (hDn : ∀ t ∈ S, D t ≠ 0) : ContinuousOn f S := by
  apply (hf.div hD hDn).congr
  intro t ht
  change f t = D t * f t / D t
  field_simp [hDn t ht]

/-- A sufficiently small perturbation grows by at most twice the ideal
relative propagator bound.  Smallness is an explicit interval inequality. -/
theorem equation30_perturbed_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ 40 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hYc : ContinuousOn Y (Icc a b) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hY₁c : ContinuousOn Y₁ (Icc a b) := continuousOn_of_flux
    (D := fun s => 1 + (ε ^ 2 * s ^ 2) ^ 2) (by fun_prop)
    (fun t ht => (hfluxY t ht).continuousAt.continuousWithinAt)
    (fun _ _ => ne_of_gt (by positivity))
  have hNc := hYc.abs.add hY₁c.abs
  have hforcingBound := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hY hfluxY hfc hgc
  have hineq : ∀ t ∈ Icc a b,
      |Y t| + |Y₁ t| ≤ U t *
        (20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a +
          (20 * Θ ^ 8 * δ) * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) := by
    intro t ht
    have hsub : uIcc a t ⊆ Icc a b := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hNcont := hNc.div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
    have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
      (hFcont.mono hsub).intervalIntegrable
    have hNi : IntervalIntegrable (fun s => δ * ((|Y s| + |Y₁ s|) / U s))
        MeasureTheory.volume a t := ((hNcont.mono hsub).intervalIntegrable).const_mul δ
    have hpoint : ∀ s ∈ Icc a t,
        (|f s| + |g s|) / U s ≤ δ * ((|Y s| + |Y₁ s|) / U s) := by
      intro s hs
      have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
      have hm := div_le_div_of_nonneg_right (hforcing s hsab) (hUp s (ha.trans hs.1)).le
      convert! hm using 1
      ring
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hNi hpoint
    rw [intervalIntegral.integral_const_mul] at hi
    have hUt : 0 < U t := hUp t (ha.trans ht.1)
    have hscaled := mul_le_mul_of_nonneg_left hi
      (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
    calc
      |Y t| + |Y₁ t| ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * ∫ s in a..t, (|f s| + |g s|) / U s := hforcingBound t ht
      _ ≤ 20 * Θ ^ 8 * (U t / U a) * (|Y a| + |Y₁ a|) +
          20 * Θ ^ 8 * U t * (δ * ∫ s in a..t, (|Y s| + |Y₁ s|) / U s) :=
        add_le_add le_rfl hscaled
      _ = _ := by ring
  have hresult := relative_integral_absorb
    (f := fun t => |Y t| + |Y₁ t|) (U := U)
    (A := 20 * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) (K := 20 * Θ ^ 8 * δ)
    hab hNc hUc (fun _ _ => by positivity) (fun t ht => hUp t (ha.trans ht.1))
    (by positivity) hsmall hineq
  intro t ht
  convert! hresult t ht using 1
  ring

/-- Quantitative difference from an ideal solution.  A perturbation of
size `δ = O(e Θ^12)` produces the source's `O(e Θ^29)` relative error. -/
theorem equation30_perturbed_difference_bound
    {ε Θ a b δ : ℝ} {U U₁ V V₁ Y Y₁ Z Z₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Θ) (hδ : 0 ≤ δ)
    (hsmall : 20 * Θ ^ 8 * δ * (b - a) ≤ 1 / 2)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc a b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hZ : ∀ t ∈ Icc a b, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hforcing : ∀ t ∈ Icc a b, |f t| + |g t| ≤ δ * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc a b,
      |Y t - Z t| + |Y₁ t - Z₁ t| ≤
        20 * Θ ^ 8 * (U t / U a) * (|Y a - Z a| + |Y₁ a - Z₁ a|) +
          800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
  have hUp := equation30_global_positive hε hεsmall hU hfluxU hU0 (by rw [hU₁0])
  have hUa : 0 < U a := hUp a ha
  have hUc : ContinuousOn U (Icc a b) := fun t ht => (hU t (ha.trans ht.1)).continuousAt.continuousWithinAt
  have hpert := equation30_perturbed_bound hε hεsmall hΘ ha hab hb hδ hsmall
    hU hV hfluxU hfluxV hU0 hU₁0 hV₁0 hY hfluxY hfc hgc hforcing
  have hE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => Y s - Z s) ((Y₁ t - Z₁ t) + f t) t := by
    intro t ht
    apply ((hY t ht).sub (hZ t ht)).congr_deriv
    ring
  have hfluxE : ∀ t ∈ Icc a b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * (Y₁ s - Z₁ s))
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * (Y t - Z t) +
          (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t := by
    intro t ht
    convert! (hfluxY t ht).sub (hfluxZ t ht) using 1
    · ext s
      dsimp only [Pi.sub_apply]
      ring
    · ring
  have hforced := equation30_forced_bound hε hεsmall hΘ ha hb hU hV hfluxU hfluxV
    hU0 hU₁0 hV₁0 hE hfluxE hfc hgc
  intro t ht
  have hUt : 0 < U t := hUp t (ha.trans ht.1)
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFcont := (hfc.abs.add hgc.abs).div hUc (fun s hs => ne_of_gt (hUp s (ha.trans hs.1)))
  have hFi : IntervalIntegrable (fun s => (|f s| + |g s|) / U s) MeasureTheory.volume a t :=
    (hFcont.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc a t,
      (|f s| + |g s|) / U s ≤ 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a := by
    intro s hs
    have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    have hspos := hUp s (ha.trans hs.1)
    apply (div_le_iff₀ hspos).mpr
    have hm := (hforcing s hsab).trans (mul_le_mul_of_nonneg_left (hpert s hsab) hδ)
    convert! hm using 1
    ring
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => 40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a) MeasureTheory.volume a t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hscaled := mul_le_mul_of_nonneg_left hi (show 0 ≤ 20 * Θ ^ 8 * U t by positivity)
  have hduration : t - a ≤ Θ := by linarith [ht.2]
  have hlast : 20 * Θ ^ 8 * U t *
      ((t - a) * (40 * δ * Θ ^ 8 * (|Y a| + |Y₁ a|) / U a)) ≤
      800 * δ * Θ ^ 17 * (U t / U a) * (|Y a| + |Y₁ a|) := by
    have hm := mul_le_mul_of_nonneg_left hduration
      (show 0 ≤ 800 * δ * Θ ^ 16 * (U t / U a) * (|Y a| + |Y₁ a|) by positivity)
    convert! hm using 1 <;> ring
  exact (hforced t ht).trans (add_le_add le_rfl (hscaled.trans hlast))

/-- The explicit `Θ^29` relative error bound in the source's normalization.
Its `Θ^21` smallness condition follows from the exact Duhamel argument above. -/
theorem equation30_relative_error_order29
    {ε Θ b e lam : ℝ} {U U₁ V V₁ Y Y₁ Z Z₁ f g : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hb0 : 0 ≤ b) (hb : b ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam)
    (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hU : ∀ t, 0 ≤ t → HasDerivAt U (U₁ t) t)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hfluxU : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * U₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * U t) t)
    (hfluxV : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hU0 : U 0 = 1) (hU₁0 : U₁ 0 = 0) (hV₁0 : V₁ 0 = 1)
    (hY : ∀ t ∈ Icc 0 b, HasDerivAt Y (Y₁ t + f t) t)
    (hfluxY : ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Y₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Y t + (1 + (ε ^ 2 * t ^ 2) ^ 2) * g t) t)
    (hZ : ∀ t ∈ Icc 0 b, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 b,
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hY0 : Y 0 = 1) (hY₁0 : Y₁ 0 = lam) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (hfc : ContinuousOn f (Icc 0 b)) (hgc : ContinuousOn g (Icc 0 b))
    (hforcing : ∀ t ∈ Icc 0 b, |f t| + |g t| ≤ (e * Θ ^ 12) * (|Y t| + |Y₁ t|)) :
    ∀ t ∈ Icc 0 b,
      |Y t - Z t| + |Y₁ t - Z₁ t| ≤ 800 * e * Θ ^ 29 * (1 + lam) * U t := by
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hδ : 0 ≤ e * Θ ^ 12 := by positivity
  have hsmall' : 20 * Θ ^ 8 * (e * Θ ^ 12) * (b - 0) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 20 * e * Θ ^ 20 by positivity)
    nlinarith
  have hdiff := equation30_perturbed_difference_bound hε hεsmall hΘ
    (by norm_num : (0 : ℝ) ≤ 0) hb0 hb hδ hsmall'
    hU hV hfluxU hfluxV hU0 hU₁0 hV₁0 hY hfluxY hZ hfluxZ hfc hgc hforcing
  intro t ht
  have hd := hdiff t ht
  simp only [hY0, hY₁0, hZ0, hZ₁0, hU0, sub_self, abs_zero, zero_add,
    mul_zero, add_zero, div_one, abs_one, abs_of_nonneg hlam] at hd
  convert! hd using 1
  ring

end EulerPacketPerturbation

end

section

/-!
The triangular ray system and its perturbation estimates.  These results
derive ray closeness from the differential equations and coefficient errors.
-/

namespace EulerPacketRay

open Set Filter Real EulerPacketGrowth EulerPacketPerturbation
open scoped Topology

/-- The sum norm of three scalar coordinates. -/
def norm3 (p q n : ℝ) : ℝ := |p| + |q| + |n|

/-- Exact Duhamel formulas for the triangular ray system. -/
theorem triangular_ray_formula
    {β T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T,
      P t = P 0 - t * Q 0 + β * t ^ 2 * N 0 +
        ∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s ∧
      Q t = Q 0 - 2 * β * t * N 0 +
        ∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s ∧
      N t = N 0 + ∫ s in (0 : ℝ)..t, h s := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hPc : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hQc : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hPi : IntervalIntegrable (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
      MeasureTheory.volume 0 t := (hPc.mono hsub).intervalIntegrable
  have hQi : IntervalIntegrable (fun s => g s - 2 * β * (t - s) * h s)
      MeasureTheory.volume 0 t := (hQc.mono hsub).intervalIntegrable
  have hNi : IntervalIntegrable h MeasureTheory.volume 0 t := (hhc.mono hsub).intervalIntegrable
  have hdP : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => P r - (t - r) * Q r + β * (t - r) ^ 2 * N r)
        (f s - (t - s) * g s + β * (t - s) ^ 2 * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := (hasDerivAt_id s).const_sub t
    apply (((hP s hsab).sub (hd.mul (hQ s hsab))).add
      (((hd.fun_pow 2).const_mul β).mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hdQ : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun r => Q r - 2 * β * (t - r) * N r)
        (g s - 2 * β * (t - s) * h s) s := by
    intro s hs
    have hsab := hsub hs
    have hd := ((hasDerivAt_id s).const_sub t).const_mul (2 * β)
    apply ((hQ s hsab).sub (hd.mul (hN s hsab))).congr_deriv
    dsimp
    ring
  have hFP := intervalIntegral.integral_eq_sub_of_hasDerivAt hdP hPi
  have hFQ := intervalIntegral.integral_eq_sub_of_hasDerivAt hdQ hQi
  have hFN := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hN s (hsub hs)) hNi
  simp only [sub_self, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] at hFP hFQ
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The triangular ray propagator has a polynomial norm bound. -/
theorem triangular_ray_kernel_bound
    {β Θ d p q n : ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hd : 0 ≤ d) (hdΘ : d ≤ Θ) :
    norm3 (p - d * q + β * d ^ 2 * n) (q - 2 * β * d * n) n ≤
      4 * Θ ^ 2 * norm3 p q n := by
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hd2 : d ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ hd hΘ0).mpr hdΘ
  have h1 := abs_add_le (p - d * q) (β * d ^ 2 * n)
  have h2 : |p - d * q| ≤ |p| + |d * q| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le p (d * q)
  have h3 : |q - 2 * β * d * n| ≤ |q| + |2 * β * d * n| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le q (2 * β * d * n)
  simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg hd, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg d)] at h1 h2 h3
  have hcol1 : 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hcol2 : d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hβd2 : β * d ^ 2 ≤ Θ ^ 2 :=
    (mul_le_mul_of_nonneg_right hβupper (sq_nonneg d)).trans (by simpa using hd2)
  have hβd : β * d ≤ Θ :=
    (mul_le_mul_of_nonneg_right hβupper hd).trans (by simpa using hdΘ)
  have hcol3 : β * d ^ 2 + 2 * β * d + 1 ≤ 4 * Θ ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hcol1 (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hcol2 (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hcol3 (abs_nonneg n)
  unfold norm3
  nlinarith

/-- The exact triangular ray equations imply a polynomial Duhamel bound. -/
theorem triangular_ray_forced_bound
    {β Θ T : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        4 * Θ ^ 2 * ∫ s in (0 : ℝ)..t, norm3 (f s) (g s) (h s) := by
  intro t ht
  have hformula := triangular_ray_formula hP hQ hN hfc hgc hhc t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have htc : ContinuousOn (fun s : ℝ => t - s) (Icc 0 T) := by fun_prop
  have hc1 : ContinuousOn (fun s => f s - (t - s) * g s + β * (t - s) ^ 2 * h s) (Icc 0 T) :=
    (hfc.sub (htc.mul hgc)).add ((continuousOn_const.mul (htc.pow 2)).mul hhc)
  have hc2 : ContinuousOn (fun s => g s - 2 * β * (t - s) * h s) (Icc 0 T) :=
    hgc.sub ((continuousOn_const.mul htc).mul hhc)
  have hi1 : IntervalIntegrable (fun s => |f s - (t - s) * g s + β * (t - s) ^ 2 * h s|)
      MeasureTheory.volume 0 t := (hc1.abs.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s => |g s - 2 * β * (t - s) * h s|)
      MeasureTheory.volume 0 t := (hc2.abs.mono hsub).intervalIntegrable
  have hi3 : IntervalIntegrable (fun s => |h s|) MeasureTheory.volume 0 t :=
    (hhc.abs.mono hsub).intervalIntegrable
  have himajor : IntervalIntegrable (fun s => (4 * Θ ^ 2) * norm3 (f s) (g s) (h s))
      MeasureTheory.volume 0 t :=
    (((hfc.abs.add hgc.abs).add hhc.abs).mono hsub).intervalIntegrable.const_mul (4 * Θ ^ 2)
  have hpoint : ∀ s ∈ Icc 0 t,
      norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) ≤ 4 * Θ ^ 2 * norm3 (f s) (g s) (h s) := by
    intro s hs
    apply triangular_ray_kernel_bound hβ hβupper hΘ
    · linarith [hs.2]
    · linarith [hs.1, ht.2]
  have hmono := intervalIntegral.integral_mono_on ht.1 ((hi1.add hi2).add hi3) himajor hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hI :
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| + |∫ s in (0 : ℝ)..t, h s| ≤
      ∫ s in (0 : ℝ)..t, norm3 (f s - (t - s) * g s + β * (t - s) ^ 2 * h s)
        (g s - 2 * β * (t - s) * h s) (h s) := by
    unfold norm3
    rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2]
    exact add_le_add (add_le_add (intervalIntegral.abs_integral_le_integral_abs ht.1)
      (intervalIntegral.abs_integral_le_integral_abs ht.1)) (intervalIntegral.abs_integral_le_integral_abs ht.1)
  have hbase := triangular_ray_kernel_bound (p := P 0) (q := Q 0) (n := N 0)
    hβ hβupper hΘ ht.1 (ht.2.trans hT)
  have hPt : |P t| ≤ |P 0 - t * Q 0 + β * t ^ 2 * N 0| +
      |∫ s in (0 : ℝ)..t, f s - (t - s) * g s + β * (t - s) ^ 2 * h s| := by
    rw [hformula.1]
    exact abs_add_le _ _
  have hQt : |Q t| ≤ |Q 0 - 2 * β * t * N 0| +
      |∫ s in (0 : ℝ)..t, g s - 2 * β * (t - s) * h s| := by
    rw [hformula.2.1]
    exact abs_add_le _ _
  have hNt : |N t| ≤ |N 0| + |∫ s in (0 : ℝ)..t, h s| := by
    rw [hformula.2.2]
    exact abs_add_le _ _
  unfold norm3 at hbase hI hmono ⊢
  linarith

/-- A small perturbation of the triangular ray system remains polynomially
bounded on the whole interval. -/
theorem triangular_ray_perturbed_bound
    {β Θ T δ : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t)) :
    ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤ 8 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) := by
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hstate : ContinuousOn (fun t => norm3 (P t) (Q t) (N t)) (Icc 0 T) :=
    (hPc.abs.add hQc.abs).add hNc.abs
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  have hforced := triangular_ray_forced_bound hβ hβupper hΘ hT hP hQ hN hfc hgc hhc
  have hineq : ∀ t ∈ Icc 0 T, norm3 (P t) (Q t) (N t) ≤
      4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0) +
        (4 * Θ ^ 2 * δ) * ∫ s in (0 : ℝ)..t, norm3 (P s) (Q s) (N s) := by
    intro t ht
    have hsub : uIcc 0 t ⊆ Icc 0 T := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
      (hforce.mono hsub).intervalIntegrable
    have hSi : IntervalIntegrable (fun s => δ * norm3 (P s) (Q s) (N s)) MeasureTheory.volume 0 t :=
      ((hstate.mono hsub).intervalIntegrable).const_mul δ
    have hi := intervalIntegral.integral_mono_on ht.1 hFi hSi
      (fun s hs => hforcing s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const_mul] at hi
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
    nlinarith [hforced t ht]
  have hresult := integral_absorb
    (g := fun t => norm3 (P t) (Q t) (N t))
    (A := 4 * Θ ^ 2 * norm3 (P 0) (Q 0) (N 0)) (K := 4 * Θ ^ 2 * δ)
    hT0 hstate (fun _ _ => by unfold norm3; positivity) (by positivity)
    (by simpa using hsmall) hineq
  intro t ht
  nlinarith [hresult t ht]

/-- Ray closeness is derived from the ODE and the forcing bound, with a
polynomial loss and arbitrary small initial ray error. -/
theorem triangular_ray_difference_bound
    {β Θ T δ η : ℝ} {P Q N f g h : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hsmall : 4 * Θ ^ 2 * δ * T ≤ 1 / 2)
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hhc : ContinuousOn h (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ δ * norm3 (P t) (Q t) (N t))
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ η) :
    ∀ t ∈ Icc 0 T, norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤
      4 * Θ ^ 2 * η + 32 * δ * Θ ^ 5 * (1 + η) := by
  have hnorm0 : norm3 (P 0) (Q 0) (N 0) ≤ 1 + η := by
    have hn : |N 0| ≤ |N 0 - 1| + 1 := by
      have := abs_add_le (N 0 - 1) 1
      simpa using this
    unfold norm3 at hinitial ⊢
    linarith
  have hstate := triangular_ray_perturbed_bound hβ hβupper hΘ hT0 hT hδ hsmall
    hP hQ hN hfc hgc hhc hforcing
  have hPe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => P s - β * s ^ 2) (-(Q t + 2 * β * t) + f t) t := by
    intro t ht
    apply ((hP t ht).sub (((hasDerivAt_id t).fun_pow 2).const_mul β)).congr_deriv
    dsimp
    ring
  have hQe : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => Q s + 2 * β * s) (-2 * β * (N t - 1) + g t) t := by
    intro t ht
    apply ((hQ t ht).add ((hasDerivAt_id t).const_mul (2 * β))).congr_deriv
    ring
  have hNe : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => N s - 1) (h t) t :=
    fun t ht => (hN t ht).sub_const 1
  have herror := triangular_ray_forced_bound hβ hβupper hΘ hT hPe hQe hNe hfc hgc hhc
  have hforce : ContinuousOn (fun t => norm3 (f t) (g t) (h t)) (Icc 0 T) :=
    (hfc.abs.add hgc.abs).add hhc.abs
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hFi : IntervalIntegrable (fun s => norm3 (f s) (g s) (h s)) MeasureTheory.volume 0 t :=
    (hforce.mono hsub).intervalIntegrable
  have hpoint : ∀ s ∈ Icc 0 t, norm3 (f s) (g s) (h s) ≤ δ * (8 * Θ ^ 2 * (1 + η)) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hm := mul_le_mul_of_nonneg_left hnorm0 (show 0 ≤ 8 * Θ ^ 2 by positivity)
    have hbound : norm3 (P s) (Q s) (N s) ≤ 8 * Θ ^ 2 * (1 + η) := (hstate s hsT).trans hm
    exact (hforcing s hsT).trans (mul_le_mul_of_nonneg_left hbound hδ)
  have hi := intervalIntegral.integral_mono_on ht.1 hFi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ * (8 * Θ ^ 2 * (1 + η)))
      MeasureTheory.volume 0 t) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hi
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have htΘ : t ≤ Θ := ht.2.trans hT
  have htime := mul_le_mul_of_nonneg_left htΘ (show 0 ≤ 32 * δ * Θ ^ 4 * (1 + η) by positivity)
  have hinit := mul_le_mul_of_nonneg_left hinitial (show 0 ≤ 4 * Θ ^ 2 by positivity)
  have herr := herror t ht
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, add_zero] at herr
  nlinarith

/-- Entries of the triangular ideal ray generator. -/
def idealRayEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 2 then -2 * β else 0

theorem three_term_bound {a b c p q n e : ℝ}
    (ha : |a| ≤ e) (hb : |b| ≤ e) (hc : |c| ≤ e) :
    |a * p + b * q + c * n| ≤ e * norm3 p q n := by
  have h1 := abs_add_le (a * p + b * q) (c * n)
  have h2 := abs_add_le (a * p) (b * q)
  simp only [abs_mul] at h1 h2
  have hp := mul_le_mul_of_nonneg_right ha (abs_nonneg p)
  have hq := mul_le_mul_of_nonneg_right hb (abs_nonneg q)
  have hn := mul_le_mul_of_nonneg_right hc (abs_nonneg n)
  unfold norm3
  nlinarith

/-- The ray closeness estimate follows from entrywise coefficient error.
No closeness of the ray itself is assumed.  The third component stays away
from zero, as required to eliminate the third velocity coordinate. -/
theorem ray_closeness_of_coefficient_error
    {β Θ T e : ℝ} {A : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hsmall : 400 * e * Θ ^ 5 ≤ 1)
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (A t 0 0 * P t + A t 0 1 * Q t + A t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (A t 1 0 * P t + A t 1 1 * Q t + A t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t) t)
    (hclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealRayEntry β i j| ≤ e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T,
      norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 ∧
        1 / 2 ≤ N t := by
  let f : ℝ → ℝ := fun t => A t 0 0 * P t + (A t 0 1 + 1) * Q t + A t 0 2 * N t
  let g : ℝ → ℝ := fun t => A t 1 0 * P t + A t 1 1 * Q t + (A t 1 2 + 2 * β) * N t
  let h : ℝ → ℝ := fun t => A t 2 0 * P t + A t 2 1 * Q t + A t 2 2 * N t
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := by unfold f; fun_prop
  have hgc : ContinuousOn g (Icc 0 T) := by unfold g; fun_prop
  have hhc : ContinuousOn h (Icc 0 T) := by unfold h; fun_prop
  have hPf : ∀ t ∈ Icc 0 T, HasDerivAt P (-Q t + f t) t := by
    intro t ht
    apply (hP t ht).congr_deriv
    dsimp [f]
    ring
  have hQg : ∀ t ∈ Icc 0 T, HasDerivAt Q (-2 * β * N t + g t) t := by
    intro t ht
    apply (hQ t ht).congr_deriv
    dsimp [g]
    ring
  have hNh : ∀ t ∈ Icc 0 T, HasDerivAt N (h t) t := hN
  have hforcing : ∀ t ∈ Icc 0 T, norm3 (f t) (g t) (h t) ≤ (3 * e) * norm3 (P t) (Q t) (N t) := by
    intro t ht
    have hf : |f t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 0 0
      · simpa [idealRayEntry] using hclose t ht 0 1
      · simpa [idealRayEntry] using hclose t ht 0 2
    have hg : |g t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 1 0
      · simpa [idealRayEntry] using hclose t ht 1 1
      · simpa [idealRayEntry] using hclose t ht 1 2
    have hh : |h t| ≤ e * norm3 (P t) (Q t) (N t) := by
      apply three_term_bound
      · simpa [idealRayEntry] using hclose t ht 2 0
      · simpa [idealRayEntry] using hclose t ht 2 1
      · simpa [idealRayEntry] using hclose t ht 2 2
    unfold norm3
    unfold norm3 at hf hg hh
    nlinarith
  have hΘ0 : 0 ≤ Θ := le_trans zero_le_one hΘ
  have hpow35 : Θ ^ 3 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow25 : Θ ^ 2 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by norm_num)
  have hpow5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have he1 : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow5 he
    nlinarith
  have hsm : 4 * Θ ^ 2 * (3 * e) * T ≤ 1 / 2 := by
    have ht := mul_le_mul_of_nonneg_left hT (show 0 ≤ 12 * e * Θ ^ 2 by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow35 (show 0 ≤ 12 * e by positivity)
    nlinarith
  have hdiff := triangular_ray_difference_bound hβ hβupper hΘ hT0 hT
    (by positivity : 0 ≤ 3 * e) he hsm hPf hQg hNh hfc hgc hhc hforcing hinitial
  intro t ht
  have hbound : norm3 (P t - β * t ^ 2) (Q t + 2 * β * t) (N t - 1) ≤ 200 * e * Θ ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hpow25 (show 0 ≤ 4 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show 1 + e ≤ 2 by linarith)
      (show 0 ≤ 96 * e * Θ ^ 5 by positivity)
    have hp : 0 ≤ e * Θ ^ 5 := by positivity
    nlinarith [hdiff t ht]
  refine ⟨hbound, ?_⟩
  have hNabs : |N t - 1| ≤ 200 * e * Θ ^ 5 := by
    unfold norm3 at hbound
    linarith [abs_nonneg (P t - β * t ^ 2), abs_nonneg (Q t + 2 * β * t)]
  have hn := (abs_le.mp hNabs).1
  nlinarith

/-- The skew matrix of the moving orthonormal frame in the source. -/
def frameSkew (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then B 0 1 else if j = 2 then B 0 2 else 0)
  else if i = 1 then (if j = 0 then -B 0 1 else if j = 2 then B 2 1 else 0)
  else if j = 0 then -B 0 2 else if j = 1 then -B 2 1 else 0

/-- The older gradient plus rank-one parent shear and error. -/
def parentEntry (B E : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) : ℝ :=
  B i j + E i j + (if i = 1 ∧ j = 0 then h else 0)

/-- Coordinate scaling for the normalized ray. -/
def rayScale (ε : ℝ) (i : Fin 3) : ℝ := if i = 1 then ε else 1

/-- Coefficients after the moving-frame transformation and the scaling
`m/s₀=(P,εQ,N)`, `dt/dτ=ε/a`. -/
noncomputable def scaledRayEntry (a ε : ℝ) (M S : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  -(ε / a) * (rayScale ε j / rayScale ε i) * (M j i - S j i)

/-- The scaled moving-frame ray entries in normalized coefficients. -/
def normalizedRayEntry (ε H κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then -B 0 0 - ε * E 0 0
      else if j = 1 then -H - ε * B 1 0 - ε * B 0 1 - ε ^ 2 * E 1 0
      else -B 2 0 - B 0 2 - ε * E 2 0)
  else if i = 1 then
    (if j = 0 then -E 0 1 else if j = 1 then -B 1 1 - ε * E 1 1 else -2 * κ - E 2 1)
  else if j = 0 then -ε * E 0 2
    else if j = 1 then -ε * B 1 2 + ε * B 2 1 - ε ^ 2 * E 1 2
    else -B 2 2 - ε * E 2 2

/-- Exact entries of the scaled moving-frame ray matrix. -/
theorem scaled_ray_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) :
    ∀ i j, scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j =
      normalizedRayEntry ε (ε ^ 2 * h / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledRayEntry, parentEntry, frameSkew, rayScale, normalizedRayEntry,
      Fin.ext_iff] <;>
    field_simp <;> ring

/-- Each scaled matrix entry is close to the triangular ideal matrix when
the normalized older-gradient, error, shear, and coupling coefficients are
small. -/
theorem normalized_ray_entry_error
    {ε H κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedRayEntry ε H κ B E i j - idealRayEntry β i j| ≤ 4 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    have hm := mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hm := mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
    simpa using hm
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε01 := abs_le.mp (hεBn 0 1)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedRayEntry, idealRayEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε01, bε12, bε21,
      e01, e21, eε00, eε11, eε20, eε02, eε22, eε210, eε212, hHb, hκb]

/-- The original moving-frame entries imply the coefficient hypothesis of
`ray_closeness_of_coefficient_error`. -/
theorem scaled_ray_entry_error
    {a ε h β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hκ : |B 2 1 / a - β| ≤ e) :
    ∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 * e := by
  intro i j
  rw [scaled_ray_entry_identity ha (ne_of_gt hε)]
  exact normalized_ray_entry_error hε.le hεupper he hB hE hH hκ i j

/-- A product difference estimate used to control the projection denominator. -/
theorem abs_product_difference
    {a b c d ea eb A B : ℝ}
    (ha : |a - c| ≤ ea) (hb : |b - d| ≤ eb)
    (hc : |c| ≤ A) (hd : |b| ≤ B) :
    |a * b - c * d| ≤ ea * B + A * eb := by
  have hea : 0 ≤ ea := le_trans (abs_nonneg _) ha
  have hA : 0 ≤ A := le_trans (abs_nonneg _) hc
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |a - c| * |b| + |c| * |b - d| := by
      simpa only [abs_mul] using abs_add_le ((a - c) * b) (c * (b - d))
    _ ≤ ea * B + A * eb := add_le_add
      (mul_le_mul ha hd (abs_nonneg _) hea)
      (mul_le_mul hc hb (abs_nonneg _) hA)

/-- The third velocity coordinate imposed by ray orthogonality. -/
noncomputable def velocityThird (P Q N U V : ℝ) : ℝ := -(P * U + Q * V) / N

/-- Squared norm of the scaled ray. -/
def rayDenominator (ε P Q N : ℝ) : ℝ := P ^ 2 + ε ^ 2 * Q ^ 2 + N ^ 2

/-- Elimination of the third velocity component and the denominator estimate
are consequences of the proved ray error. -/
theorem ray_geometric_bounds
    {Θ ρ ε P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρupper : ρ ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ) :
    1 / 2 ≤ N ∧ |P| ≤ 2 * Θ ^ 2 ∧ |Q| ≤ 3 * Θ ^ 2 ∧ |N| ≤ 2 ∧
      |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) ∧
      1 / 4 ≤ rayDenominator ε P Q N ∧
      |rayDenominator ε P Q N - (1 + P₀ ^ 2)| ≤
        6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hn : 1 / 2 ≤ N := by have := (abs_le.mp hN).1; linarith
  have hnpos : 0 < N := by linarith
  have hp : |P| ≤ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) P₀
    have hh' : |P| ≤ ρ + Θ ^ 2 := by
      calc
        |P| = |(P - P₀) + P₀| := by congr 1; ring
        _ ≤ |P - P₀| + |P₀| := hh
        _ ≤ ρ + Θ ^ 2 := add_le_add hP hP₀
    linarith
  have hq : |Q| ≤ 3 * Θ ^ 2 := by
    have hh' : |Q| ≤ ρ + 2 * Θ ^ 2 := by
      calc
        |Q| = |(Q - Q₀) + Q₀| := by congr 1; ring
        _ ≤ |Q - Q₀| + |Q₀| := abs_add_le _ _
        _ ≤ ρ + 2 * Θ ^ 2 := add_le_add hQ hQ₀
    linarith
  have hnabs : |N| ≤ 2 := by rw [abs_of_pos hnpos]; have := (abs_le.mp hN).2; linarith
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : |velocityThird P Q N U V| ≤ 6 * Θ ^ 2 * (|U| + |V|) := by
    unfold velocityThird
    rw [abs_div, abs_neg, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have hb : |P * U + Q * V| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
      calc
        |P * U + Q * V| ≤ |P| * |U| + |Q| * |V| := by simpa only [abs_mul] using abs_add_le (P * U) (Q * V)
        _ ≤ (2 * Θ ^ 2) * |U| + (3 * Θ ^ 2) * |V| :=
          add_le_add (mul_le_mul_of_nonneg_right hp (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hq (abs_nonneg _))
        _ ≤ 3 * Θ ^ 2 * (|U| + |V|) := by nlinarith [sq_nonneg Θ, abs_nonneg U]
    have hmul := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 6 * Θ ^ 2 * (|U| + |V|))
    nlinarith only [hb, hmul]
  have hD : 1 / 4 ≤ rayDenominator ε P Q N := by
    unfold rayDenominator
    nlinarith [sq_nonneg P, mul_nonneg (sq_nonneg ε) (sq_nonneg Q)]
  have hPsum : |P + P₀| ≤ 3 * Θ ^ 2 := by linarith [abs_add_le P P₀]
  have hNsum : |N + 1| ≤ 3 := by have hh := abs_add_le N 1; norm_num at hh; linarith
  have hPsq : |P ^ 2 - P₀ ^ 2| ≤ 3 * ρ * Θ ^ 2 := by
    calc
      |P ^ 2 - P₀ ^ 2| = |P - P₀| * |P + P₀| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * (3 * Θ ^ 2) := mul_le_mul hP hPsum (abs_nonneg _) hρ
      _ = 3 * ρ * Θ ^ 2 := by ring
  have hNsq : |N ^ 2 - 1| ≤ 3 * ρ := by
    calc
      |N ^ 2 - 1| = |N - 1| * |N + 1| := by rw [← abs_mul]; congr 1; ring
      _ ≤ ρ * 3 := mul_le_mul hN hNsum (abs_nonneg _) hρ
      _ = 3 * ρ := by ring
  have hQsq : Q ^ 2 ≤ 9 * Θ ^ 4 := by
    have hsq := sq_le_sq₀ (abs_nonneg Q) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hh := hsq.mpr hq
    rw [sq_abs] at hh
    nlinarith only [hh]
  refine ⟨hn, hp, hq, hnabs, hw, hD, ?_⟩
  calc
    |rayDenominator ε P Q N - (1 + P₀ ^ 2)| =
        |(P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1) + ε ^ 2 * Q ^ 2| := by
      unfold rayDenominator; congr 1; ring
    _ ≤ |P ^ 2 - P₀ ^ 2| + |N ^ 2 - 1| + ε ^ 2 * Q ^ 2 := by
      have h₁ := abs_add_le (P ^ 2 - P₀ ^ 2) (N ^ 2 - 1)
      have h₂ := abs_add_le ((P ^ 2 - P₀ ^ 2) + (N ^ 2 - 1)) (ε ^ 2 * Q ^ 2)
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg Q))] at h₂
      linarith
    _ ≤ 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4 := by
      have hqq := mul_le_mul_of_nonneg_left hQsq (sq_nonneg ε)
      have hrr := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 3 * ρ)
      nlinarith only [hPsq, hNsq, hqq, hrr]

/-- The three rows entering `J_v`, with the middle row multiplied by ε. -/
def normalizedVelocityEntry (ε H α κ : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then α + E 0 1
      else B 0 2 + ε * E 0 2)
  else if i = 1 then
    (if j = 0 then H + ε * B 1 0 + ε ^ 2 * E 1 0
      else if j = 1 then B 1 1 + ε * E 1 1 else ε * B 1 2 + ε ^ 2 * E 1 2)
  else if j = 0 then B 2 0 + ε * E 2 0
    else if j = 1 then κ + E 2 1 else B 2 2 + ε * E 2 2

/-- The ideal scaled parent action on velocity coordinates. -/
def idealVelocityEntry (β : ℝ) (i j : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1
  else if i = 2 ∧ j = 1 then β else 0

/-- Parent-gradient entries after ray and velocity rescaling. -/
noncomputable def scaledVelocityEntry (a ε : ℝ) (M : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  (if i = 1 then ε else 1) * (if j = 1 then 1 else ε) * M i j / a

theorem scaled_velocity_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ i j, scaledVelocityEntry a ε (parentEntry B E h) i j =
      normalizedVelocityEntry ε (ε ^ 2 * h / a) (B 0 1 / a) (B 2 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, normalizedVelocityEntry, Fin.ext_iff] <;>
    field_simp
  all_goals ring

theorem normalized_velocity_entry_error
    {ε H α κ β e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεupper : ε ≤ 1) (he : 0 ≤ e)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) (hκ : |κ - β| ≤ e) :
    ∀ i j, |normalizedVelocityEntry ε H α κ B E i j - idealVelocityEntry β i j| ≤ 3 * e := by
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have b20 := abs_le.mp (hB 2 0)
  have b22 := abs_le.mp (hB 2 2)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have e01 := abs_le.mp (hE 0 1)
  have e21 := abs_le.mp (hE 2 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε20 := abs_le.mp (hεEn 2 0)
  have eε22 := abs_le.mp (hεEn 2 2)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hκb := abs_le.mp hκ
  intro i j
  fin_cases i <;> fin_cases j <;> apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedVelocityEntry, idealVelocityEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, b20, b22, bε10, bε12,
      e01, e21, eε00, eε02, eε11, eε20, eε22, eε210, eε212, hHb, hαb, hκb]

/-- The scalar pressure numerator in the scaled coordinates. -/
def velocityNumerator (A : Fin 3 → Fin 3 → ℝ) (P Q N U V W : ℝ) : ℝ :=
  P * (A 0 0 * U + A 0 1 * V + A 0 2 * W) +
  Q * (A 1 0 * U + A 1 1 * V + A 1 2 * W) +
  N * (A 2 0 * U + A 2 1 * V + A 2 2 * W)

theorem velocity_numerator_error
    {A : Fin 3 → Fin 3 → ℝ} {Θ ρ e β P Q N P₀ Q₀ U V W : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2) (hn : |N| ≤ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hw : |W| ≤ 6 * Θ ^ 2 * (|U| + |V|)) :
    |velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U)| ≤
      (49 * e * Θ ^ 4 + 2 * ρ) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [hw, hm]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * U +
      (A i 1 - idealVelocityEntry β i 1) * V +
      (A i 2 - idealVelocityEntry β i 2) * W| ≤
      7 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    nlinarith only [hh, hm]
  have hrow0 := hrow 0
  have hrow1 := hrow 1
  have hrow2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at hrow0 hrow1 hrow2
  have hJnear : |velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V)| ≤
      49 * e * Θ ^ 4 * (|U| + |V|) := by
    let r0 := A 0 0 * U + (A 0 1 - 1) * V + A 0 2 * W
    let r1 := (A 1 0 - 1) * U + A 1 1 * V + A 1 2 * W
    let r2 := A 2 0 * U + (A 2 1 - β) * V + A 2 2 * W
    have htri : |P * r0 + Q * r1 + N * r2| ≤
        (|P| + |Q| + |N|) * (7 * e * Θ ^ 2 * (|U| + |V|)) := by
      have h0 := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg P)
      have h1 := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg Q)
      have h2 := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg N)
      have ht0 := abs_add_le (P * r0) (Q * r1)
      have ht1 := abs_add_le (P * r0 + Q * r1) (N * r2)
      simp only [abs_mul] at ht0 ht1
      dsimp [r0, r1, r2] at *
      nlinarith only [h0, h1, h2, ht0, ht1]
    have hs : |P| + |Q| + |N| ≤ 7 * Θ ^ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_right hs
      (by positivity : 0 ≤ 7 * e * Θ ^ 2 * (|U| + |V|))
    have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) =
        P * r0 + Q * r1 + N * r2 := by unfold velocityNumerator r0 r1 r2; ring
    rw [hid]
    nlinarith only [htri, hm]
  have hRay : |P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)| ≤
      2 * ρ * (|U| + |V|) := by
    have hNb : |(N - 1) * β| ≤ ρ := by
      rw [abs_mul]
      exact (mul_le_mul hN hβ (abs_nonneg _) hρ).trans_eq (mul_one ρ)
    have hv : |P - P₀ + (N - 1) * β| ≤ 2 * ρ := by linarith [abs_add_le (P - P₀) ((N - 1) * β)]
    have hu : |Q - Q₀| ≤ 2 * ρ := by linarith
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hv hu
      (show |(0 : ℝ)| ≤ 2 * ρ by simpa using (show 0 ≤ 2 * ρ by positivity))
    have hid : P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U) =
        (P - P₀ + (N - 1) * β) * V + (Q - Q₀) * U + 0 * 0 := by ring
    rw [hid]
    simpa only [norm3, abs_zero, add_zero, add_comm] using hh
  have ht := abs_add_le
    (velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V))
    (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U))
  have hid : velocityNumerator A P Q N U V W - (P * V + Q * U + N * β * V) +
      (P * V + Q * U + N * β * V - ((P₀ + β) * V + Q₀ * U)) =
      velocityNumerator A P Q N U V W - ((P₀ + β) * V + Q₀ * U) := by ring
  rw [hid] at ht
  nlinarith only [ht, hJnear, hRay]

/-- The first two velocity rows before pressure projection. -/
def normalizedUnprojectedEntry (ε H α : ℝ) (B E : Fin 3 → Fin 3 → ℝ)
    (i j : Fin 3) : ℝ :=
  if i = 0 then
    (if j = 0 then B 0 0 + ε * E 0 0 else if j = 1 then 2 * α + E 0 1
      else 2 * B 0 2 + ε * E 0 2)
  else if j = 0 then H + ε * B 1 0 - ε ^ 2 * α + ε ^ 2 * E 1 0
    else if j = 1 then B 1 1 + ε * E 1 1
    else ε * B 1 2 + ε * B 2 1 + ε ^ 2 * E 1 2

/-- Ideal entries of the unprojected two-component velocity equation. -/
def idealUnprojectedEntry (i j : Fin 3) : ℝ :=
  if i = 0 then (if j = 1 then 2 else 0) else if j = 0 then 1 else 0

/-- Exact first and second rows of the moving-frame velocity operator. -/
theorem scaled_unprojected_entry_identity
    {a ε h : ℝ} {B E : Fin 3 → Fin 3 → ℝ} (ha : a ≠ 0) :
    ∀ j, (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 0 j) ∧
      (scaledVelocityEntry a ε
        (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j =
      normalizedUnprojectedEntry ε (ε ^ 2 * h / a) (B 0 1 / a)
        (fun i j => ε * B i j / a) (fun i j => E i j / a) 1 j) := by
  intro j
  fin_cases j <;> constructor <;>
    simp only [show (⟨2, by decide⟩ : Fin 3) = 2 from rfl] <;>
    norm_num [scaledVelocityEntry, parentEntry, frameSkew,
      normalizedUnprojectedEntry, Fin.ext_iff] <;> field_simp <;> ring

theorem normalized_unprojected_entry_error
    {ε H α e : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (hε : 0 ≤ ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heupper : e ≤ 1)
    (hB : ∀ i j, |B i j| ≤ e) (hE : ∀ i j, |E i j| ≤ e)
    (hH : |H - 1| ≤ e) (hα : |α - 1| ≤ e) :
    ∀ i j, |normalizedUnprojectedEntry ε H α B E i j - idealUnprojectedEntry i j| ≤ 5 * e := by
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hε2e : ε ^ 2 ≤ e := by nlinarith
  have hεBn : ∀ i j, |ε * B i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hB i j) (abs_nonneg _) zero_le_one
  have hεEn : ∀ i j, |ε * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg hε]
    simpa using mul_le_mul hεupper (hE i j) (abs_nonneg _) zero_le_one
  have hε2En : ∀ i j, |ε ^ 2 * E i j| ≤ e := by
    intro i j
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    simpa using mul_le_mul hε2 (hE i j) (abs_nonneg _) zero_le_one
  have hαabs : |α| ≤ 2 := by
    have hh := abs_add_le (α - 1) 1
    norm_num at hh
    linarith
  have hαε : |ε ^ 2 * α| ≤ 2 * e := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hε2e hαabs (abs_nonneg α) he
    nlinarith only [hh]
  have b00 := abs_le.mp (hB 0 0)
  have b02 := abs_le.mp (hB 0 2)
  have b11 := abs_le.mp (hB 1 1)
  have bε10 := abs_le.mp (hεBn 1 0)
  have bε12 := abs_le.mp (hεBn 1 2)
  have bε21 := abs_le.mp (hεBn 2 1)
  have e01 := abs_le.mp (hE 0 1)
  have eε00 := abs_le.mp (hεEn 0 0)
  have eε02 := abs_le.mp (hεEn 0 2)
  have eε11 := abs_le.mp (hεEn 1 1)
  have eε210 := abs_le.mp (hε2En 1 0)
  have eε212 := abs_le.mp (hε2En 1 2)
  have hHb := abs_le.mp hH
  have hαb := abs_le.mp hα
  have hαεb := abs_le.mp hαε
  intro i j
  fin_cases i <;> fin_cases j <;> apply abs_le.mpr <;> constructor <;>
    norm_num [normalizedUnprojectedEntry, idealUnprojectedEntry, Fin.ext_iff] <;>
    linarith only [he, b00, b02, b11, bε10, bε12, bε21,
      e01, eε00, eε02, eε11, eε210, eε212, hHb, hαb, hαεb]

/-- A quotient difference bound requiring only the quantitative lower
bounds actually available for the ray denominator. -/
theorem quotient_difference_bound
    {P P₀ D D₀ ρ d A : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ A) (hDD : |D - D₀| ≤ d) :
    |P / D - P₀ / D₀| ≤ 4 * ρ + 4 * A * d := by
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans hP
  have hd : 0 ≤ d := (abs_nonneg _).trans hDD
  have hA : 0 ≤ A := (abs_nonneg _).trans hP₀
  have hprod : 1 / 4 ≤ D * D₀ := by nlinarith only [hD, hD₀, hDp]
  have hn := abs_product_difference hP
    (show |D₀ - D| ≤ d by simpa only [abs_sub_comm] using hDD)
    hP₀ (le_of_eq (abs_of_pos hD₀p))
  have hid : P / D - P₀ / D₀ = (P * D₀ - P₀ * D) / (D * D₀) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hDp hD₀p), div_le_iff₀ (mul_pos hDp hD₀p)]
  have h₁ := mul_le_mul_of_nonneg_left hD (mul_nonneg hρ hD₀p.le)
  have h₂ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hA hd)
  nlinarith only [hn, h₁, h₂]

/-- Quantitative stability of the two pressure projection components. -/
theorem velocity_projection_error
    {Θ ρ d j ε P Q D P₀ D₀ J J₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hd : 0 ≤ d) (_hj : 0 ≤ j) (hjupper : j ≤ 1)
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀)
    (hP : |P - P₀| ≤ ρ) (hP₀ : |P₀| ≤ Θ ^ 2)
    (hp : |P| ≤ 2 * Θ ^ 2) (hq : |Q| ≤ 3 * Θ ^ 2)
    (hDD : |D - D₀| ≤ d) (hJ : |J - J₀| ≤ j * (|U| + |V|))
    (hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|)) :
    |2 * P * J / D - 2 * P₀ * J₀ / D₀| + |2 * ε ^ 2 * Q * J / D| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d +
        72 * ε ^ 2 * Θ ^ 4) * (|U| + |V|) := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have hratio := quotient_difference_bound hD hD₀ hP hP₀ hDD
  have hratio0 : |P₀ / D₀| ≤ Θ ^ 2 := by
    rw [abs_div, abs_of_pos hD₀p, div_le_iff₀ hD₀p]
    have hm := mul_le_mul_of_nonneg_left hD₀ (sq_nonneg Θ)
    nlinarith only [hP₀, hm]
  have hJabs : |J| ≤ 3 * Θ ^ 2 * (|U| + |V|) := by
    have ht := abs_add_le (J - J₀) J₀
    have hid : J - J₀ + J₀ = J := by ring
    rw [hid] at ht
    have hm₁ := mul_le_mul_of_nonneg_right hjupper hL
    have hm₂ := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [ht, hJ, hJ₀, hm₁, hm₂]
  have hratioP : |P / D| ≤ 8 * Θ ^ 2 := by
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 8 * Θ ^ 2)
    nlinarith only [hp, hm]
  have hU : |2 * P * J / D - 2 * P₀ * J₀ / D₀| ≤
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d) * (|U| + |V|) := by
    have hh := abs_product_difference hratio hJ hratio0 hJabs
    have hbetter : |(P / D) * J - (P₀ / D₀) * J₀| ≤
        (8 * Θ ^ 2) * (j * (|U| + |V|)) +
          (4 * ρ + 4 * Θ ^ 2 * d) * (2 * Θ ^ 2 * (|U| + |V|)) := by
      have ht := abs_add_le ((P / D) * (J - J₀)) (((P / D) - (P₀ / D₀)) * J₀)
      have h₁ := mul_le_mul hratioP hJ (abs_nonneg _) (by positivity : 0 ≤ 8 * Θ ^ 2)
      have h₂ := mul_le_mul hratio hJ₀ (abs_nonneg _)
        (by positivity : 0 ≤ 4 * ρ + 4 * Θ ^ 2 * d)
      have hid : (P / D) * (J - J₀) + ((P / D) - (P₀ / D₀)) * J₀ =
          (P / D) * J - (P₀ / D₀) * J₀ := by ring
      rw [hid] at ht
      simp only [abs_mul] at ht
      nlinarith only [ht, h₁, h₂]
    have hid : 2 * P * J / D - 2 * P₀ * J₀ / D₀ =
        2 * ((P / D) * J - (P₀ / D₀) * J₀) := by ring
    rw [hid, abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [hbetter]
  have hV : |2 * ε ^ 2 * Q * J / D| ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg ε), abs_of_pos hDp, div_le_iff₀ hDp]
    have hh := mul_le_mul hq hJabs (abs_nonneg J) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm₁ := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * ε ^ 2)
    have hm₂ := mul_le_mul_of_nonneg_left hD
      (by positivity : 0 ≤ 72 * ε ^ 2 * Θ ^ 4 * (|U| + |V|))
    nlinarith only [hm₁, hm₂]
  nlinarith only [hU, hV]

/-- The first normalized velocity equation with pressure projection. -/
noncomputable def velocityFirstRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 0 0 * U + C 0 1 * V + C 0 2 * W) +
    2 * P * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The second normalized velocity equation with pressure projection. -/
noncomputable def velocitySecondRhs
    (A C : Fin 3 → Fin 3 → ℝ) (ε P Q N U V : ℝ) : ℝ :=
  let W := velocityThird P Q N U V;
  -(C 1 0 * U + C 1 1 * V + C 1 2 * W) +
    2 * ε ^ 2 * Q * velocityNumerator A P Q N U V W / rayDenominator ε P Q N

/-- The full pressure projection is a small matrix perturbation, with an
explicit constant and the power of Θ used in the source. -/
theorem velocity_rhs_error
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ i j, |C i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ5 : 1 ≤ Θ ^ 5 := one_le_pow₀ hΘ
  have heupper : e ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hΘ5 he
    nlinarith only [hsmall, hm]
  have hεupper : ε ≤ 1 := hεe.trans heupper
  have hε2e : ε ^ 2 ≤ e := by nlinarith only [hε, hεupper, hεe]
  let ρ := 800 * e * Θ ^ 5
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρupper : ρ ≤ 1 / 2 := by dsimp [ρ]; nlinarith only [hsmall]
  obtain ⟨hn, hp, hq, hnabs, hw, hD, hDD⟩ :=
    ray_geometric_bounds (ε := ε) (U := U) (V := V) hΘ hρ hρupper hP₀ hQ₀ hP hQ hN
  let W := velocityThird P Q N U V
  let D := rayDenominator ε P Q N
  let D₀ := 1 + P₀ ^ 2
  let J := velocityNumerator A P Q N U V W
  let J₀ := (P₀ + β) * V + Q₀ * U
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  let d := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have h45 : Θ ^ 4 ≤ Θ ^ 5 := pow_le_pow_right₀ hΘ (by decide)
  have hjupper : j ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left h45 (by positivity : 0 ≤ 147 * e)
    dsimp [j, ρ]
    nlinarith only [hsmall, hm]
  have hJ : |J - J₀| ≤ j * (|U| + |V|) := by
    have hh := velocity_numerator_error hΘ hρ (by positivity : 0 ≤ 3 * e) hβ hA hp hq hnabs hP hQ hN hw
    dsimp [J, J₀, W, j]
    nlinarith only [hh]
  have hJ₀ : |J₀| ≤ 2 * Θ ^ 2 * (|U| + |V|) := by
    have hcoef : |P₀ + β| ≤ 2 * Θ ^ 2 := by linarith [abs_add_le P₀ β]
    have hh := three_term_bound (p := V) (q := U) (n := (0 : ℝ)) hcoef hQ₀
      (show |(0 : ℝ)| ≤ 2 * Θ ^ 2 by simp; positivity)
    dsimp [J₀]
    simpa only [zero_mul, add_zero, norm3, abs_zero, add_comm] using hh
  have hD₀ : 1 ≤ D₀ := by dsimp [D₀]; nlinarith [sq_nonneg P₀]
  have hproj := velocity_projection_error (ε := ε) hΘ hρ hd hj hjupper hD hD₀ hP hP₀ hp hq hDD hJ hJ₀
  have hL : 0 ≤ |U| + |V| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hnorm : norm3 U V W ≤ 7 * Θ ^ 2 * (|U| + |V|) := by
    unfold norm3
    have hm := mul_le_mul_of_nonneg_right hΘ2 hL
    nlinarith only [hw, hm]
  have hrow : ∀ i, |(C i 0 - idealUnprojectedEntry i 0) * U +
      (C i 1 - idealUnprojectedEntry i 1) * V +
      (C i 2 - idealUnprojectedEntry i 2) * W| ≤
      35 * e * Θ ^ 2 * (|U| + |V|) := by
    intro i
    have hh := three_term_bound (p := U) (q := V) (n := W) (hC i 0) (hC i 1) (hC i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 5 * e)
    nlinarith only [hh, hm]
  have hu := hrow 0
  have hv := hrow 1
  norm_num [idealUnprojectedEntry, Fin.ext_iff] at hu hv
  have htU := abs_add_le (-(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W))
    (2 * P * J / D - 2 * P₀ * J₀ / D₀)
  have htV := abs_add_le (-((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W))
    (2 * ε ^ 2 * Q * J / D)
  rw [abs_neg] at htU htV
  have hUeq : velocityFirstRhs A C ε P Q N U V -
      (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2)) =
      -(C 0 0 * U + (C 0 1 - 2) * V + C 0 2 * W) +
        (2 * P * J / D - 2 * P₀ * J₀ / D₀) := by
    dsimp [velocityFirstRhs, W, J, J₀, D, D₀]; ring
  have hVeq : velocitySecondRhs A C ε P Q N U V + U =
      -((C 1 0 - 1) * U + C 1 1 * V + C 1 2 * W) + 2 * ε ^ 2 * Q * J / D := by
    dsimp [velocitySecondRhs, W, J, D]; ring
  rw [hUeq, hVeq]
  have hcoefficient : 70 * e * Θ ^ 2 +
      (16 * Θ ^ 2 * j + 16 * ρ * Θ ^ 2 + 16 * Θ ^ 4 * d + 72 * ε ^ 2 * Θ ^ 4) ≤
      200000 * e * Θ ^ 12 := by
    have h2 : Θ ^ 2 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h4 : Θ ^ 4 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h6 : Θ ^ 6 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h7 : Θ ^ 7 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h8 : Θ ^ 8 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have h11 : Θ ^ 11 ≤ Θ ^ 12 := pow_le_pow_right₀ hΘ (by decide)
    have he2 := mul_le_mul_of_nonneg_left h2 he
    have he4 := mul_le_mul_of_nonneg_left h4 he
    have he6 := mul_le_mul_of_nonneg_left h6 he
    have he7 := mul_le_mul_of_nonneg_left h7 he
    have he8 := mul_le_mul_of_nonneg_left h8 he
    have he11 := mul_le_mul_of_nonneg_left h11 he
    have hε4 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 4)
    have hε8 := mul_le_mul_of_nonneg_right hε2e (by positivity : 0 ≤ Θ ^ 8)
    dsimp [j, d, ρ]
    nlinarith only [he2, he4, he6, he7, he8, he11, hε4, hε8,
      mul_nonneg he (pow_nonneg hΘ0 12)]
  have hm := mul_le_mul_of_nonneg_right hcoefficient hL
  nlinarith only [htU, htV, hu, hv, hproj, hm]

end EulerPacketRay

end

section

open Set

namespace EulerPacketBridge

open EulerPacketGrowth EulerPacketPerturbation EulerPacketRay

/-- The first component of the ideal normalized velocity vector field. -/
noncomputable def idealVelocityFirst (β t U V : ℝ) : ℝ :=
  -2 * V + 2 * (β * t ^ 2) * (((β * t ^ 2) + β) * V + (-2 * β * t) * U) /
    (1 + (β * t ^ 2) ^ 2)

/-- The exact forced scalar flux equation obtained from the two velocity
components.  The forcing is the actual vector-field discrepancy. -/
theorem velocity_scalar_flux
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ}
    (hU : HasDerivAt U u₁ t) (hV : HasDerivAt V v₁ t) :
    HasDerivAt V (-U t + (v₁ + U t)) t ∧
    HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring

theorem continuousOn_idealVelocityFirst
    {β : ℝ} {I : Set ℝ} {U V : ℝ → ℝ}
    (hU : ContinuousOn U I) (hV : ContinuousOn V I) :
    ContinuousOn (fun t => idealVelocityFirst β t (U t) (V t)) I := by
  unfold idealVelocityFirst
  have hden : ∀ t ∈ I, 1 + (β * t ^ 2) ^ 2 ≠ 0 := by intro t _; positivity
  have hId : ContinuousOn (fun t : ℝ => t) I := continuousOn_id
  fun_prop

/-- Any continuously differentiable velocity solution inherits the precise
relative scalar stability estimate once its vector field has been bounded.
The preceding matrix and ray theorems provide that bound. -/
theorem velocity_relative_error_order29
    {σ Θ T e lam : ℝ} {F F₁ G G₁ Z Z₁ U U₁ V V₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hlam : 0 ≤ lam)
    (hsmall : 40 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U (U₁ t) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V (V₁ t) t)
    (hU₁c : ContinuousOn U₁ (Icc 0 T)) (hV₁c : ContinuousOn V₁ (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T,
      |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| + |V₁ t + U t| ≤
        (e * Θ ^ 12) * (|U t| + |V t|)) :
    ∀ t ∈ Icc 0 T,
      |V t - Z t| + |U t + Z₁ t| ≤ 800 * e * Θ ^ 29 * (1 + lam) * F t := by
  let f : ℝ → ℝ := fun t => V₁ t + U t
  let g : ℝ → ℝ := fun t => -U₁ t + idealVelocityFirst (σ ^ 2) t (U t) (V t)
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc 0 T) := hV₁c.add hUc
  have hgc : ContinuousOn g (Icc 0 T) := hU₁c.neg.add (continuousOn_idealVelocityFirst hUc hVc)
  have hY : ∀ t ∈ Icc 0 T, HasDerivAt V ((-U t) + f t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ ^ 2) (hU t ht) (hV t ht)).1
  have hfluxY : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * (-U s))
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * V t + (1 + (σ ^ 2 * t ^ 2) ^ 2) * g t) t := by
    intro t ht
    exact (velocity_scalar_flux (β := σ ^ 2) (hU t ht) (hV t ht)).2
  have hforcing : ∀ t ∈ Icc 0 T, |f t| + |g t| ≤ (e * Θ ^ 12) * (|V t| + |-U t|) := by
    intro t ht
    have hh := herror t ht
    have hg : |g t| = |U₁ t - idealVelocityFirst (σ ^ 2) t (U t) (V t)| := by
      dsimp [g]
      rw [neg_add_eq_sub, abs_sub_comm]
    rw [hg, abs_neg]
    dsimp [f]
    nlinarith only [hh]
  have hminusU0 : -U 0 = lam := by rw [hU0, neg_neg]
  have hresult := equation30_relative_error_order29 hσ hσsmall hΘ hT0 hT he hlam hsmall
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hY hfluxY hZ hfluxZ
    hV0 hminusU0 hZ0 hZ₁0 hfc hgc hforcing
  intro t ht
  have hh := hresult t ht
  have hid : -U t - Z₁ t = -(U t + Z₁ t) := by ring
  simpa only [hid, abs_neg] using hh

/-- Ray coefficient bounds imply the velocity vector-field discrepancy.
The ray error and the nonvanishing third coordinate are conclusions of
the actual ray ODE, not premises. -/
theorem ray_controlled_velocity_error
    {β Θ T e ε : ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N : ℝ → ℝ}
    (hβ : 0 ≤ β) (hβupper : β ≤ 1) (hΘ : 1 ≤ Θ) (hT0 : 0 ≤ T) (hT : T ≤ Θ)
    (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hsmall : 10000 * e * Θ ^ 5 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry β i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hinitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e) :
    ∀ t ∈ Icc 0 T, 1 / 2 ≤ N t ∧ ∀ U V : ℝ,
      |velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) U V -
          idealVelocityFirst β t U V| +
        |velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) U V + U| ≤
          200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hΘ0 : 0 ≤ Θ := by linarith
  have hsmallR : 400 * (4 * e) * Θ ^ 5 ≤ 1 := by
    have hnonneg : 0 ≤ e * Θ ^ 5 := by positivity
    nlinarith only [hsmall, hnonneg]
  have hinitialR : norm3 (P 0) (Q 0) (N 0 - 1) ≤ 4 * e := by linarith
  have hray := ray_closeness_of_coefficient_error hβ hβupper hΘ hT0 hT
    (by positivity : 0 ≤ 4 * e) hsmallR hRc hP hQ hN hRclose hinitialR
  intro t ht
  obtain ⟨herr, hn⟩ := hray t ht
  refine ⟨hn, ?_⟩
  intro U V
  have herrorP : |P t - β * t ^ 2| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    nlinarith only [herr, abs_nonneg (Q t + 2 * β * t), abs_nonneg (N t - 1)]
  have herrorQ : |Q t - (-2 * β * t)| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    have hid : Q t - (-2 * β * t) = Q t + 2 * β * t := by ring
    rw [hid]
    nlinarith only [herr, abs_nonneg (P t - β * t ^ 2), abs_nonneg (N t - 1)]
  have herrorN : |N t - 1| ≤ 800 * e * Θ ^ 5 := by
    unfold norm3 at herr
    nlinarith only [herr, abs_nonneg (P t - β * t ^ 2), abs_nonneg (Q t + 2 * β * t)]
  have htΘ : t ≤ Θ := ht.2.trans hT
  have ht2 : t ^ 2 ≤ Θ ^ 2 := (sq_le_sq₀ ht.1 hΘ0).mpr htΘ
  have hP₀ : |β * t ^ 2| ≤ Θ ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hβ (sq_nonneg t))]
    have hh := mul_le_mul_of_nonneg_right hβupper (sq_nonneg t)
    nlinarith only [hh, ht2]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg ht.1]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have htTheta2 : t ≤ Θ ^ 2 := by nlinarith only [htΘ, hΘ]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.1
    nlinarith only [hh, htTheta2]
  have hβabs : |β| ≤ 1 := by rwa [abs_of_nonneg hβ]
  exact velocity_rhs_error hΘ he hε hεe hsmall hβabs
    (hAclose t ht) (hCclose t ht) hP₀ hQ₀ herrorP herrorQ herrorN

theorem continuousOn_velocity_rhs
    {ε : ℝ} {I : Set ℝ} {A C : ℝ → Fin 3 → Fin 3 → ℝ} {P Q N U V : ℝ → ℝ}
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) I)
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I) (hN : ContinuousOn N I)
    (hU : ContinuousOn U I) (hV : ContinuousOn V I)
    (hNne : ∀ t ∈ I, N t ≠ 0) :
    ContinuousOn (fun t => velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I ∧
    ContinuousOn (fun t => velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) I := by
  have hW : ContinuousOn (fun t => velocityThird (P t) (Q t) (N t) (U t) (V t)) I := by
    unfold velocityThird
    exact ((hP.mul hU).add (hQ.mul hV)).neg.div hN hNne
  have hD : ContinuousOn (fun t => rayDenominator ε (P t) (Q t) (N t)) I := by
    unfold rayDenominator
    fun_prop
  have hDne : ∀ t ∈ I, rayDenominator ε (P t) (Q t) (N t) ≠ 0 := by
    intro t ht
    have hn : 0 < N t ^ 2 := sq_pos_of_ne_zero (hNne t ht)
    unfold rayDenominator
    positivity
  have hJ : ContinuousOn (fun t => velocityNumerator (A t) (P t) (Q t) (N t)
      (U t) (V t) (velocityThird (P t) (Q t) (N t) (U t) (V t))) I := by
    unfold velocityNumerator
    fun_prop
  constructor
  · exact ((((hCc 0 0).mul hU).add ((hCc 0 1).mul hV)).add
      ((hCc 0 2).mul hW)).neg.add (((hP.const_mul 2).mul hJ).div hD hDne)
  · exact ((((hCc 1 0).mul hU).add ((hCc 1 1).mul hV)).add
      ((hCc 1 2).mul hW)).neg.add (((hQ.const_mul (2 * ε ^ 2)).mul hJ).div hD hDne)

/-- The complete finite-dimensional stability bridge: actual ray and
velocity equations with controlled matrix coefficients imply the relative
`Θ^29` error.  All denominator and Duhamel bounds are derived above. -/
theorem controlled_velocity_relative_error
    {σ Θ T e ε lam : ℝ} {F F₁ G G₁ Z Z₁ U V P Q N : ℝ → ℝ}
    {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 8000000 * e * Θ ^ 21 ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hG : ∀ t, 0 ≤ t → HasDerivAt G (G₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxG : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * G t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hG₁0 : G₁ 0 = 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam) :
    ∀ t ∈ Icc 0 T,
      |V t - Z t| + |U t + Z₁ t| ≤ 160000000 * e * Θ ^ 29 * (1 + lam) * F t := by
  have hσsq : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  have hgeomSmall : 10000 * e * Θ ^ 5 ≤ 1 := by
    have hh := pow_le_pow_right₀ hΘ (show 5 ≤ 21 by decide)
    have hm := mul_le_mul_of_nonneg_left hh he
    have hp : 0 ≤ e * Θ ^ 21 := by positivity
    nlinarith only [hsmall, hm, hp]
  have hcontrol := ray_controlled_velocity_error (sq_nonneg σ) hσsq hΘ hT0 hT he hε hεe
    hgeomSmall hRc hP hQ hN hRclose hAclose hCclose hrayInitial
  have hPc : ContinuousOn P (Icc 0 T) := fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hNc : ContinuousOn N (Icc 0 T) := fun t ht => (hN t ht).continuousAt.continuousWithinAt
  have hUc : ContinuousOn U (Icc 0 T) := fun t ht => (hU t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun t ht => (hV t ht).continuousAt.continuousWithinAt
  have hNne : ∀ t ∈ Icc 0 T, N t ≠ 0 := by
    intro t ht
    have hh := (hcontrol t ht).1
    linarith
  obtain ⟨hU₁c, hV₁c⟩ := continuousOn_velocity_rhs (ε := ε) hAc hCc hPc hQc hNc hUc hVc hNne
  have hsmall' : 40 * (200000 * e) * Θ ^ 21 ≤ 1 := by nlinarith only [hsmall]
  have herror : ∀ t ∈ Icc 0 T,
      |velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t) -
        idealVelocityFirst (σ ^ 2) t (U t) (V t)| +
      |velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t) + U t| ≤
        ((200000 * e) * Θ ^ 12) * (|U t| + |V t|) := by
    intro t ht
    exact (hcontrol t ht).2 (U t) (V t)
  have hh := velocity_relative_error_order29 hσ hσsmall hΘ hT0 hT
    (by positivity : 0 ≤ 200000 * e) hlam hsmall'
    hF hG hfluxF hfluxG hF0 hF₁0 hG₁0 hU hV hU₁c hV₁c hZ hfluxZ hU0 hV0 hZ0 hZ₁0 herror
  intro t ht
  have h := hh t ht
  nlinarith only [h]

end EulerPacketBridge

end

section

open Set

namespace EulerPacketFrameStability

open Real EulerPacketGrowth EulerPacketPerturbation EulerPacketRay EulerPacketBridge

/-- Exact relation between the original and inverted logarithmic slopes. -/
theorem inverted_logarithmic_identity
    {ε y : ℝ} {V V₁ : ℝ → ℝ} (hε : ε ≠ 0) (hy : y ≠ 0)
    (hV : V (y⁻¹ / ε) ≠ 0) :
    y ^ 2 * (-ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y) - ε * y =
      V₁ (y⁻¹ / ε) / V (y⁻¹ / ε) := by
  have halg (v w : ℝ) (hv : v ≠ 0) :
      y ^ 2 * (-ε * (-v / y ^ 2 - w / (ε * y ^ 3)) / (v / y)) - ε * y = w / v := by
    field_simp
    ring
  exact halg (V (y⁻¹ / ε)) (V₁ (y⁻¹ / ε)) hV

/-- The logarithmic slope is bounded uniformly in the initial nonnegative
slope after time one. -/
theorem equation30_primary_logderivative_bound
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 1 ≤ t → |V₁ t / V t| ≤ 4 := by
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t htpos.le
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos.le, hpre⟩
    have hu := equation30_log_derivative_upper (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨htpos, hpre⟩
    have hnonneg : 0 ≤ V₁ t / V t := div_nonneg hp.2 hVp.le
    rw [abs_of_nonneg hnonneg]
    have hinv : 1 / t ≤ 1 := (div_le_one htpos).mpr ht
    linarith
  · have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp (le_of_not_ge hpre)
      nlinarith only [hh]
    let y := 1 / (ε * t)
    have hy : 0 < y := by dsimp [y]; positivity
    have hy1 : y ≤ 1 := by dsimp [y]; exact (div_le_one (by positivity)).mpr hεt
    have harg : y⁻¹ / ε = t := by dsimp [y]; rw [one_div, inv_inv]; field_simp
    have hz := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy hy1
    have hid := inverted_logarithmic_identity (V₁ := V₁) hεne (ne_of_gt hy)
      (show V (y⁻¹ / ε) ≠ 0 by rw [harg]; exact ne_of_gt hVp)
    rw [harg] at hid
    let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
    have hz0 : 0 ≤ z := hz.1
    have hz4 : z ≤ 4 := hz.2
    have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.le, hy1]
    have hmul := mul_le_mul_of_nonneg_left hz4 (sq_nonneg y)
    have hepsy : 0 ≤ ε * y := mul_nonneg hε.le hy.le
    have hepsyUpper : ε * y ≤ 1 := by nlinarith only [hε, hεsmall, hy.le, hy1]
    have hzmul : 0 ≤ y ^ 2 * z := mul_nonneg (sq_nonneg y) hz0
    apply abs_le.mpr
    dsimp [z] at hmul hzmul
    constructor <;> nlinarith only [hid, hmul, hepsy, hepsyUpper, hzmul, hy2]

/-- The ideal pressure numerator has the sign required for the next-frame
construction, throughout the forward evolution. -/
theorem equation30_ideal_numerator_positive
    {ε : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    ∀ t, 0 ≤ t → ε ^ 2 * V t ≤
      (ε ^ 2 * t ^ 2 + ε ^ 2) * V t + 2 * ε ^ 2 * t * V₁ t := by
  intro t ht
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht
  have hεne : ε ≠ 0 := ne_of_gt hε
  by_cases hpre : t ≤ 1 / ε
  · have hT : 0 ≤ 1 / ε := by positivity
    have hscale : ε ^ 2 * (1 / ε) ^ 2 ≤ 1 := by field_simp; norm_num
    have hp := equation30_positive (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2)
      hT hscale (fun s hs => hV s hs.1) (fun s hs => hflux s hs.1) hV0 hV₁0 t ⟨ht, hpre⟩
    have h₁ := mul_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg t)) hVp.le
    have h₂ := mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) ht) hp.2
    nlinarith only [h₁, h₂]
  · have hpost : 1 / ε ≤ t := le_of_not_ge hpre
    have hposit := equation30_post_inversion_positive_derivative hε hεsmall hV hflux hV0 hV₁0 t hpost
    have hεt : 1 ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp hpost
      nlinarith only [hh]
    have hεt2 : 1 ≤ ε ^ 2 * t ^ 2 := by nlinarith only [hεt]
    have hε2 : 2 * ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
    have h₁ := mul_nonneg (show 0 ≤ ε ^ 2 * t ^ 2 - 2 * ε ^ 2 by linarith) hVp.le
    have h₂ := mul_nonneg (by positivity : 0 ≤ 2 * ε ^ 2) hposit.le
    nlinarith only [h₁, h₂]

/-- Relative control of both components gives positivity and control of
the logarithmic ratio without dividing by an uncontrolled quantity. -/
theorem relative_state_error_consequences
    {U V Z Z₁ η : ℝ} (hZ : 0 < Z) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (herror : |V - Z| + |U + Z₁| ≤ η * Z) (hslope : |Z₁ / Z| ≤ 4) :
    0 < V ∧ |V / Z - 1| ≤ η ∧ |U / V + Z₁ / Z| ≤ 10 * η := by
  have hVerror : |V - Z| ≤ η * Z := by linarith [abs_nonneg (U + Z₁)]
  have hUerror : |U + Z₁| ≤ η * Z := by linarith [abs_nonneg (V - Z)]
  have hVlower : Z / 2 ≤ V := by
    have hh := (abs_le.mp hVerror).1
    have hm := mul_le_mul_of_nonneg_right hηsmall hZ.le
    nlinarith only [hh, hm]
  have hVp : 0 < V := by linarith only [hZ, hVlower]
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hVne : V ≠ 0 := ne_of_gt hVp
  have hZ₁abs : |Z₁| ≤ 4 * Z := by
    rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ] at hslope
    exact hslope
  refine ⟨hVp, ?_, ?_⟩
  · have hid : V / Z - 1 = (V - Z) / Z := by field_simp
    rw [hid, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    exact hVerror
  · have hnum : |U * Z + Z₁ * V| ≤ 5 * η * Z ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_right hUerror hZ.le
      have h₂ := mul_le_mul hZ₁abs hVerror (abs_nonneg _) (by positivity : 0 ≤ 4 * Z)
      have ht := abs_add_le ((U + Z₁) * Z) (Z₁ * (V - Z))
      rw [abs_mul, abs_mul, abs_of_pos hZ] at ht
      have hid : (U + Z₁) * Z + Z₁ * (V - Z) = U * Z + Z₁ * V := by ring
      rw [hid] at ht
      nlinarith only [ht, h₁, h₂]
    have hid : U / V + Z₁ / Z = (U * Z + Z₁ * V) / (V * Z) := by field_simp
    rw [hid, abs_div, abs_of_pos (mul_pos hVp hZ), div_le_iff₀ (mul_pos hVp hZ)]
    have hm := mul_le_mul_of_nonneg_right hVlower (by positivity : 0 ≤ 10 * η * Z)
    nlinarith only [hnum, hm]

/-- Stability relative to the growing primary solution, with constants
independent of its nonnegative initial slope. -/
theorem equation30_relative_state_consequences
    {ε lam δ t U V : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam) (ht : 1 ≤ t)
    (hδ : 0 ≤ δ) (hsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F₁ t) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V ∧ |V / Z t - 1| ≤ 2 * exp 6 * δ ∧
      |U / V + Z₁ t / Z t| ≤ 20 * exp 6 * δ := by
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t (by linarith)
  have hlower := equation30_slope_uniform_lower hε hεsmall hlam hF hZ hfluxF hfluxZ
    hF0 hF₁0 hZ0 hZ₁0 t ht
  have hslope := equation30_primary_logderivative_bound hε hεsmall hZ hfluxZ hZ0 hZ₁0pos t ht
  have hη : 0 ≤ 2 * exp 6 * δ := by positivity
  have hηsmall : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hsmall]
  have hrelative : |V - Z t| + |U + Z₁ t| ≤ (2 * exp 6 * δ) * Z t := by
    calc
      |V - Z t| + |U + Z₁ t| ≤ δ * (1 + lam) * F t := herror
      _ = (2 * exp 6 * δ) * (((1 + lam) / (2 * exp 6)) * F t) := by field_simp
      _ ≤ (2 * exp 6 * δ) * Z t := mul_le_mul_of_nonneg_left hlower hη
  obtain ⟨hv, hratio, hs⟩ := relative_state_error_consequences hZpos hη hηsmall hrelative hslope
  refine ⟨hv, hratio, ?_⟩
  nlinarith only [hs]

/-- Division of the pressure-numerator error is safe once positivity and
the logarithmic-ratio bounds have been derived. -/
theorem pressure_ratio_error
    {Θ η j P₀ Q₀ β U V r₀ J : ℝ}
    (hΘ : 1 ≤ Θ) (_hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hj : 0 ≤ j)
    (hV : 0 < V) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2) (hr₀ : |r₀| ≤ 4)
    (hr : |U / V - r₀| ≤ 10 * η)
    (hJ : |J - ((P₀ + β) * V + Q₀ * U)| ≤ j * (|U| + |V|)) :
    |J / V - (P₀ + β + Q₀ * r₀)| ≤ 10 * j + 20 * Θ ^ 2 * η := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hrabs : |U / V| ≤ 9 := by
    have hh := abs_add_le (U / V - r₀) r₀
    have hid : U / V - r₀ + r₀ = U / V := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hUabs : |U| ≤ 9 * V := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV] at hrabs
    exact hrabs
  have hJdiv : |(J - ((P₀ + β) * V + Q₀ * U)) / V| ≤ 10 * j := by
    rw [abs_div, abs_of_pos hV, div_le_iff₀ hV]
    rw [abs_of_pos hV] at hJ
    have hm := mul_le_mul_of_nonneg_left hUabs hj
    nlinarith only [hJ, hm]
  have hQerr : |Q₀ * (U / V - r₀)| ≤ 20 * Θ ^ 2 * η := by
    rw [abs_mul]
    have hh := mul_le_mul hQ₀ hr (abs_nonneg _) (by positivity : 0 ≤ 2 * Θ ^ 2)
    nlinarith only [hh]
  have hid : J / V - (P₀ + β + Q₀ * r₀) =
      (J - ((P₀ + β) * V + Q₀ * U)) / V + Q₀ * (U / V - r₀) := by field_simp; ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hJdiv hQerr)

/-- The actual pressure numerator preserves the required positive sign
under the quantitatively derived relative state error. -/
theorem equation30_pressure_sign_stable
    {ε Θ t η j U V J : ℝ} {Z Z₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hΘ : 1 ≤ Θ) (ht : 1 ≤ t) (htΘ : t ≤ Θ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (hj : 0 ≤ j)
    (hsmall : 10 * j + 20 * Θ ^ 2 * η ≤ ε ^ 2 / 2)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (herror : |V - Z t| + |U + Z₁ t| ≤ η * Z t)
    (hJ : |J - ((ε ^ 2 * t ^ 2 + ε ^ 2) * V + (-2 * ε ^ 2 * t) * U)| ≤
      j * (|U| + |V|)) :
    0 < V ∧ ε ^ 2 / 2 ≤ J / V ∧ 0 < J := by
  have ht0 : 0 ≤ t := by linarith
  have hZpos := equation30_global_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht0
  have hslope := equation30_primary_logderivative_bound hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht
  obtain ⟨hVp, _, hr⟩ := relative_state_error_consequences hZpos hη hηsmall herror hslope
  have hQ₀ : |-2 * ε ^ 2 * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_nonneg ht0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have he2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
    have htTheta2 : t ≤ Θ ^ 2 := by nlinarith only [htΘ, hΘ]
    have hm := mul_le_mul_of_nonneg_right he2 ht0
    nlinarith only [hm, htTheta2]
  have hr₀ : |-Z₁ t / Z t| ≤ 4 := by simpa only [neg_div, abs_neg] using hslope
  have hr' : |U / V - (-Z₁ t / Z t)| ≤ 10 * η := by simpa only [neg_div, sub_neg_eq_add] using hr
  have hpressure := pressure_ratio_error hΘ hη hηsmall hj hVp hQ₀ hr₀ hr' hJ
  have hideal := equation30_ideal_numerator_positive hε hεsmall hZ hfluxZ hZ0 hZ₁0 t ht0
  have hidealRatio : ε ^ 2 ≤ ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-Z₁ t / Z t) := by
    apply (mul_le_mul_iff_right₀ hZpos).mp
    have hZne : Z t ≠ 0 := ne_of_gt hZpos
    have hid : (ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-Z₁ t / Z t)) * Z t =
        (ε ^ 2 * t ^ 2 + ε ^ 2) * Z t + 2 * ε ^ 2 * t * Z₁ t := by field_simp
    nlinarith only [hideal, hid]
  have hJlower : ε ^ 2 / 2 ≤ J / V := by
    have hh := (abs_le.mp hpressure).1
    nlinarith only [hh, hidealRatio, hsmall]
  have hJpositive : 0 < J := by
    have hratioPos : 0 < J / V := lt_of_lt_of_le (by positivity : 0 < ε ^ 2 / 2) hJlower
    exact (div_pos_iff.mp hratioPos).resolve_right (by intro hh; linarith [hh.2]) |>.1
  exact ⟨hVp, hJlower, hJpositive⟩

/-- The third normalized velocity ratio follows from orthogonality and
the already controlled ray and first velocity ratio. -/
theorem third_ratio_error
    {Θ ρ η P Q N P₀ Q₀ r r₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η) :
    |r| ≤ 9 ∧ |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 ∧
      |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 ∧
      |velocityThird P Q N r 1 - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hrabs : |r| ≤ 9 := by
    have hh := abs_add_le (r - r₀) r₀
    have hid : r - r₀ + r₀ = r := by ring
    rw [hid] at hh
    nlinarith only [hh, hr, hr₀, hηsmall]
  have hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2 := by
    rw [abs_neg]
    have hh := abs_add_le (P₀ * r₀) Q₀
    rw [abs_mul] at hh
    have hm := mul_le_mul hP₀ hr₀ (abs_nonneg _) (sq_nonneg Θ)
    nlinarith only [hh, hm, hQ₀]
  obtain ⟨hn, _, _, _, hw, _, _⟩ :=
    ray_geometric_bounds (ε := 0) (U := r) (V := 1) hΘ hρ hρsmall hP₀ hQ₀ hP hQ hN
  have hwabs : |velocityThird P Q N r 1| ≤ 60 * Θ ^ 2 := by
    norm_num only [abs_one] at hw
    have hm := mul_le_mul_of_nonneg_left hrabs (by positivity : 0 ≤ 6 * Θ ^ 2)
    nlinarith only [hw, hm]
  have hNpos : 0 < N := by linarith only [hn]
  have hNne : N ≠ 0 := ne_of_gt hNpos
  let w₀ := -(P₀ * r₀ + Q₀)
  have hPr := abs_product_difference hP hr hP₀ hrabs
  have hNw : |(N - 1) * w₀| ≤ 6 * ρ * Θ ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hN hw₀ (abs_nonneg _) hρ
    nlinarith only [hh]
  have hsum : |(P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀| ≤
      (16 * ρ + 10 * η) * Θ ^ 2 := by
    have h₁ := abs_add_le (P * r - P₀ * r₀) (Q - Q₀)
    have h₂ := abs_add_le ((P * r - P₀ * r₀) + (Q - Q₀)) ((N - 1) * w₀)
    have hm := mul_le_mul_of_nonneg_left hΘ2 (by positivity : 0 ≤ 10 * ρ)
    nlinarith only [h₁, h₂, hPr, hQ, hNw, hm]
  refine ⟨hrabs, hw₀, hwabs, ?_⟩
  have hid : velocityThird P Q N r 1 - w₀ =
      -((P * r - P₀ * r₀) + (Q - Q₀) + (N - 1) * w₀) / N := by
    dsimp [velocityThird, w₀]
    field_simp
    ring
  change |velocityThird P Q N r 1 - w₀| ≤ _
  rw [hid, abs_div, abs_neg, abs_of_pos hNpos, div_le_iff₀ hNpos]
  have hm := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ (32 * ρ + 20 * η) * Θ ^ 2)
  nlinarith only [hsum, hm]

/-- A normalized parent-gradient row applied to the velocity ratios. -/
def rowAction (A : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (r w : ℝ) : ℝ :=
  A i 0 * r + A i 1 + A i 2 * w

/-- Rowwise control of the normalized parent action on the new velocity. -/
theorem normalized_action_error
    {Θ e β r w : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    |rowAction A 0 r w - 1| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 1 r w - r| ≤ 70 * e * Θ ^ 2 ∧
    |rowAction A 2 r w - β| ≤ 70 * e * Θ ^ 2 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hnorm : norm3 r 1 w ≤ 70 * Θ ^ 2 := by
    unfold norm3
    norm_num only [abs_one]
    nlinarith only [hr, hw, hΘ2]
  have hrow : ∀ i, |(A i 0 - idealVelocityEntry β i 0) * r +
      (A i 1 - idealVelocityEntry β i 1) * 1 + (A i 2 - idealVelocityEntry β i 2) * w| ≤
      70 * e * Θ ^ 2 := by
    intro i
    have hh := three_term_bound (p := r) (q := 1) (n := w) (hA i 0) (hA i 1) (hA i 2)
    have hm := mul_le_mul_of_nonneg_left hnorm he
    nlinarith only [hh, hm]
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  norm_num [idealVelocityEntry, Fin.ext_iff] at h0 h1 h2
  constructor
  · convert! h0 using 1
    unfold rowAction
    congr 1
    ring
  constructor
  · convert! h1 using 1
    unfold rowAction
    congr 1
    ring
  · convert! h2 using 1
    unfold rowAction
    congr 1
    ring

/-- The cross-product numerator for the next normalized coupling.
The middle argument `Tq` denotes ε times the physical middle component. -/
def frameCrossNumerator (ε P Q N r w Tp Tq Tn : ℝ) : ℝ :=
  (-N + ε ^ 2 * Q * w) * Tp + (N * r - P * w) * Tq + (P - ε ^ 2 * Q * r) * Tn

/-- The ideal next-frame cross numerator in original scalar coordinates. -/
def idealCrossNumerator (β P Q r : ℝ) : ℝ :=
  -1 + β * P + (1 + P ^ 2) * r ^ 2 + P * Q * r

/-- Quantitative stability of the exact cross-product numerator. -/
theorem frame_cross_numerator_error
    {Θ ρ η σ ε β P Q N P₀ Q₀ r r₀ w Tp Tq Tn : ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hσ : 0 ≤ σ)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hP : |P - P₀| ≤ ρ) (hQ : |Q| ≤ 3 * Θ ^ 2)
    (hN : |N - 1| ≤ ρ) (hr₀ : |r₀| ≤ 4) (hrabs : |r| ≤ 9)
    (hr : |r - r₀| ≤ 10 * η) (hwabs : |w| ≤ 60 * Θ ^ 2)
    (hw₀ : |-(P₀ * r₀ + Q₀)| ≤ 6 * Θ ^ 2)
    (hw : |w - (-(P₀ * r₀ + Q₀))| ≤ (32 * ρ + 20 * η) * Θ ^ 2)
    (hTp : |Tp - 1| ≤ σ) (hTq : |Tq - r₀| ≤ σ + 10 * η) (hTn : |Tn - β| ≤ σ)
    (hTpabs : |Tp| ≤ 2) (hTqabs : |Tq| ≤ 10) (hTnabs : |Tn| ≤ 2) :
    |frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀| ≤
      (1100 * ρ + 400 * η + 12 * σ + 500 * ε ^ 2) * Θ ^ 4 := by
  have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have h24 : Θ ^ 2 ≤ Θ ^ 4 := pow_le_pow_right₀ hΘ (by decide)
  let w₀ := -(P₀ * r₀ + Q₀)
  let c₀ := -N + ε ^ 2 * Q * w
  let c₁ := N * r - P * w
  let c₂ := P - ε ^ 2 * Q * r
  let c₁₀ := r₀ - P₀ * w₀
  have hQw : |ε ^ 2 * Q * w| ≤ 180 * ε ^ 2 * Θ ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hwabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hQr : |ε ^ 2 * Q * r| ≤ 27 * ε ^ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ε)]
    have hh := mul_le_mul hQ hrabs (abs_nonneg _) (by positivity : 0 ≤ 3 * Θ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    nlinarith only [hm]
  have hc₀ : |c₀ - (-1)| ≤ ρ + 180 * ε ^ 2 * Θ ^ 4 := by
    have hh := abs_add_le (-(N - 1)) (ε ^ 2 * Q * w)
    rw [abs_neg] at hh
    have hid : c₀ - (-1) = -(N - 1) + ε ^ 2 * Q * w := by dsimp [c₀]; ring
    rw [hid]
    linarith only [hh, hN, hQw]
  have hc₂ : |c₂ - P₀| ≤ ρ + 27 * ε ^ 2 * Θ ^ 2 := by
    have hh := abs_add_le (P - P₀) (-(ε ^ 2 * Q * r))
    rw [abs_neg] at hh
    have hid : c₂ - P₀ = (P - P₀) + -(ε ^ 2 * Q * r) := by dsimp [c₂]; ring
    rw [hid]
    linarith only [hh, hP, hQr]
  have hNr := abs_product_difference hN hr (by norm_num : |(1 : ℝ)| ≤ 1) hrabs
  have hPw := abs_product_difference hP hw hP₀ hwabs
  have hc₁ : |c₁ - c₁₀| ≤ (101 * ρ + 30 * η) * Θ ^ 4 := by
    have hh := abs_add_le (N * r - r₀) (-(P * w - P₀ * w₀))
    rw [abs_neg] at hh
    have hid : c₁ - c₁₀ = (N * r - r₀) + -(P * w - P₀ * w₀) := by dsimp [c₁, c₁₀]; ring
    rw [hid]
    have hm₁ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 9 * ρ)
    have hm₂ := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 60 * ρ)
    have hm₃ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 10 * η)
    norm_num only [one_mul] at hNr
    nlinarith only [hh, hNr, hPw, hm₁, hm₂, hm₃]
  have hc₁₀ : |c₁₀| ≤ 10 * Θ ^ 4 := by
    have hh := abs_add_le r₀ (-(P₀ * w₀))
    rw [abs_neg, abs_mul] at hh
    have hm := mul_le_mul hP₀ hw₀ (abs_nonneg _) (sq_nonneg Θ)
    change |r₀ - P₀ * w₀| ≤ _
    have hid : r₀ + -(P₀ * w₀) = r₀ - P₀ * w₀ := by ring
    rw [hid] at hh
    nlinarith only [hh, hr₀, hm, hΘ4]
  have hS₀ := abs_product_difference hc₀ hTp (by norm_num : |(-1 : ℝ)| ≤ 1) hTpabs
  have hS₁ := abs_product_difference hc₁ hTq hc₁₀ hTqabs
  have hS₂ := abs_product_difference hc₂ hTn hP₀ hTnabs
  have hsum := abs_add_le (c₀ * Tp - (-1) * 1) (c₁ * Tq - c₁₀ * r₀)
  have hsum' := abs_add_le ((c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀))
    (c₂ * Tn - P₀ * β)
  have hid : frameCrossNumerator ε P Q N r w Tp Tq Tn - idealCrossNumerator β P₀ Q₀ r₀ =
      (c₀ * Tp - (-1) * 1) + (c₁ * Tq - c₁₀ * r₀) + (c₂ * Tn - P₀ * β) := by
    dsimp [frameCrossNumerator, idealCrossNumerator, c₀, c₁, c₂, c₁₀, w₀]
    ring
  rw [hid]
  have hmρ := mul_le_mul_of_nonneg_left hΘ4 (by positivity : 0 ≤ 4 * ρ)
  have hmσ := mul_le_mul_of_nonneg_left hΘ4 hσ
  have hmσ2 := mul_le_mul_of_nonneg_left h24 hσ
  have hmε := mul_le_mul_of_nonneg_left h24 (by positivity : 0 ≤ 54 * ε ^ 2)
  have hpρ : 0 ≤ 86 * ρ * Θ ^ 4 := by positivity
  have hpε : 0 ≤ 86 * ε ^ 2 * Θ ^ 4 := by positivity
  nlinarith only [hsum, hsum', hS₀, hS₁, hS₂, hmρ, hmσ, hmσ2, hmε, hpρ, hpε]

/-- The cross numerator bound with every velocity-ratio and parent-action
estimate derived from ray, state, and matrix coefficient errors. -/
theorem frame_cross_error_from_matrix
    {Θ ρ η e ε β P Q N P₀ Q₀ r r₀ : ℝ} {A : Fin 3 → Fin 3 → ℝ}
    (hΘ : 1 ≤ Θ) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2) (he : 0 ≤ e)
    (hsmall : 70 * e * Θ ^ 2 ≤ 1) (hβ : |β| ≤ 1)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ ρ) (hQ : |Q - Q₀| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hr₀ : |r₀| ≤ 4) (hr : |r - r₀| ≤ 10 * η)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ e) :
    let w := velocityThird P Q N r 1
    |frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w) -
      idealCrossNumerator β P₀ Q₀ r₀| ≤
        (1100 * ρ + 400 * η + 840 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4 := by
  let w := velocityThird P Q N r 1
  obtain ⟨hrabs, hw₀, hwabs, hw⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall
    hP₀ hQ₀ hP hQ hN hr₀ hr
  obtain ⟨hTp, hTq, hTn⟩ := normalized_action_error hΘ he hrabs hwabs hA
  have hTq' : |rowAction A 1 r w - r₀| ≤ 70 * e * Θ ^ 2 + 10 * η := by
    have hh := abs_add_le (rowAction A 1 r w - r) (r - r₀)
    have hid : rowAction A 1 r w - r + (r - r₀) = rowAction A 1 r w - r₀ := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hr]
  have hTpabs : |rowAction A 0 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 0 r w - 1) 1
    norm_num at hh
    linarith only [hh, hTp, hsmall]
  have hTqabs : |rowAction A 1 r w| ≤ 10 := by
    have hh := abs_add_le (rowAction A 1 r w - r) r
    have hid : rowAction A 1 r w - r + r = rowAction A 1 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTq, hsmall, hrabs]
  have hTnabs : |rowAction A 2 r w| ≤ 2 := by
    have hh := abs_add_le (rowAction A 2 r w - β) β
    have hid : rowAction A 2 r w - β + β = rowAction A 2 r w := by ring
    rw [hid] at hh
    linarith only [hh, hTn, hsmall, hβ]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q - Q₀) Q₀
    have hid : Q - Q₀ + Q₀ = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    linarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hh := frame_cross_numerator_error (ε := ε) hΘ hρ hη
    (by positivity : 0 ≤ 70 * e * Θ ^ 2) hP₀ hP hQabs hN hr₀ hrabs hr hwabs hw₀ hw
    hTp hTq' hTn hTpabs hTqabs hTnabs
  dsimp only
  nlinarith only [hh]

/-- Squared norm of the normalized velocity direction. -/
def velocityDirectionNormSq (ε r w : ℝ) : ℝ := 1 + ε ^ 2 * (r ^ 2 + w ^ 2)

theorem velocity_direction_norm_bound
    {Θ ε r w : ℝ} (hΘ : 1 ≤ Θ) (hr : |r| ≤ 9) (hw : |w| ≤ 60 * Θ ^ 2) :
    1 ≤ velocityDirectionNormSq ε r w ∧
      velocityDirectionNormSq ε r w - 1 ≤ 3681 * ε ^ 2 * Θ ^ 4 := by
  have hΘ4 : 1 ≤ Θ ^ 4 := one_le_pow₀ hΘ
  have hr2 : r ^ 2 ≤ 81 := by
    have hh := (sq_le_sq₀ (abs_nonneg r) (by norm_num : (0 : ℝ) ≤ 9)).mpr hr
    rw [sq_abs] at hh
    norm_num at hh
    exact hh
  have hw2 : w ^ 2 ≤ 3600 * Θ ^ 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg w) (by positivity : 0 ≤ 60 * Θ ^ 2)).mpr hw
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hsum : r ^ 2 + w ^ 2 ≤ 3681 * Θ ^ 4 := by nlinarith only [hr2, hw2, hΘ4]
  have hm := mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
  unfold velocityDirectionNormSq
  constructor
  · nlinarith only [mul_nonneg (sq_nonneg ε) (add_nonneg (sq_nonneg r) (sq_nonneg w))]
  · nlinarith only [hm]

end EulerPacketFrameStability

end

section

open Set

namespace EulerPacketFrameRenewal

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability

/-- Square-root normalization preserves an error from the unit value. -/
theorem sqrt_unit_error
    {E d : ℝ} (hE : 1 ≤ E) (herror : E - 1 ≤ d) (hd : d ≤ 1) :
    1 ≤ sqrt E ∧ sqrt E ≤ 2 ∧ |sqrt E - 1| ≤ d := by
  have hs : 1 ≤ sqrt E := Real.one_le_sqrt.mpr hE
  have hself : sqrt E ≤ E := Real.sqrt_le_self_iff.mpr (Or.inr hE)
  refine ⟨hs, by linarith, ?_⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ sqrt E - 1)]
  linarith

/-- The ray square root is uniformly stable away from zero. -/
theorem sqrt_ray_error
    {D D₀ d : ℝ} (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (herror : |D - D₀| ≤ d) :
    1 / 2 ≤ sqrt D ∧ |sqrt D - sqrt D₀| ≤ d := by
  have hD0 : 0 ≤ D := by linarith
  have hD₀0 : 0 ≤ D₀ := by linarith
  have hsq := sq_sqrt hD0
  have hsq₀ := sq_sqrt hD₀0
  have hs0 := sqrt_nonneg D
  have hs₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hsum : 1 ≤ sqrt D + sqrt D₀ := by linarith
  have hid : (sqrt D - sqrt D₀) * (sqrt D + sqrt D₀) = D - D₀ := by nlinarith only [hsq, hsq₀]
  have hh : |sqrt D - sqrt D₀| * (sqrt D + sqrt D₀) ≤ d := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ sqrt D + sqrt D₀), ← abs_mul, hid]
    exact herror
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (sqrt D - sqrt D₀))
  constructor <;> nlinarith only [hD, hsq, hs0, hh, hm]

/-- Stability of the next-frame expansion coefficient under perturbation
of the pressure numerator and both normalization factors. -/
theorem expansion_quotient_error
    {D D₀ E J J₀ dD dE dJ M aerr : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (hE : 1 ≤ E)
    (hDE : |D - D₀| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJ₀ : |J₀| ≤ M) (hroot : sqrt D₀ ≤ M)
    (hideal : |J₀ / sqrt D₀ - 1| ≤ aerr) :
    |J / (sqrt D * sqrt E) - 1| ≤
      aerr + 4 * dJ + 4 * M * (2 * dD + M * dE) := by
  obtain ⟨hrootD, hrootDiff⟩ := sqrt_ray_error hD hD₀ hDE
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hrootD₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hM : 0 ≤ M := (abs_nonneg _).trans hJ₀
  have hden : 1 / 4 ≤ sqrt D * sqrt E := by
    have hh := mul_le_mul hrootD hrootE (by norm_num : (0 : ℝ) ≤ 1) (sqrt_nonneg D)
    nlinarith only [hh]
  have hdenDiff : |sqrt D * sqrt E - sqrt D₀| ≤ 2 * dD + M * dE := by
    have hh := abs_product_difference hrootDiff hrootEE
      (show |sqrt D₀| ≤ M by rw [abs_of_nonneg (sqrt_nonneg D₀)]; exact hroot)
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm dD 2] using hh
  have hdiff := quotient_difference_bound hden hrootD₀ hJE hJ₀ hdenDiff
  have ht := abs_add_le (J / (sqrt D * sqrt E) - J₀ / sqrt D₀) (J₀ / sqrt D₀ - 1)
  have hid : J / (sqrt D * sqrt E) - J₀ / sqrt D₀ + (J₀ / sqrt D₀ - 1) =
      J / (sqrt D * sqrt E) - 1 := by ring
  rw [hid] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Quotient stability when the reference denominator is at least one half. -/
theorem quotient_error_half_denominator
    {a a₀ b b₀ da db M : ℝ}
    (hb : 1 / 4 ≤ b) (hb₀ : 1 / 2 ≤ b₀)
    (ha : |a - a₀| ≤ da) (ha₀ : |a₀| ≤ M) (hbb : |b - b₀| ≤ db) :
    |a / b - a₀ / b₀| ≤ 8 * da + 16 * M * db := by
  have ha2 : |2 * a - 2 * a₀| ≤ 2 * da := by
    have hid : 2 * a - 2 * a₀ = 2 * (a - a₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [ha]
  have ha₀2 : |2 * a₀| ≤ 2 * M := by rw [abs_mul]; norm_num; linarith only [ha₀]
  have hb2 : |2 * b - 2 * b₀| ≤ 2 * db := by
    have hid : 2 * b - 2 * b₀ = 2 * (b - b₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [hbb]
  have hh := quotient_difference_bound (show (1 : ℝ) / 4 ≤ 2 * b by linarith)
    (show (1 : ℝ) ≤ 2 * b₀ by linarith) ha2 ha₀2 hb2
  have hbe : b ≠ 0 := by linarith
  have hb₀e : b₀ ≠ 0 := by linarith
  have h₁ : 2 * a / (2 * b) = a / b := by field_simp
  have h₂ : 2 * a₀ / (2 * b₀) = a₀ / b₀ := by field_simp
  rw [h₁, h₂] at hh
  nlinarith only [hh]

/-- Stability of the next coupling multiplied by the target scale squared. -/
theorem coupling_quotient_error
    {P₀ E J J₀ S S₀ dE dJ dS berr : ℝ}
    (hP₀ : 0 < P₀) (hE : 1 ≤ E) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJEsmall : dJ ≤ P₀ / 4)
    (hJ₀ : 1 / 2 ≤ J₀ / P₀) (hJ₀upper : J₀ / P₀ ≤ 2)
    (hSE : |S - S₀| ≤ dS) (hS₀ : |S₀| ≤ 20)
    (hideal : |S₀ / (J₀ / P₀) - 1| ≤ berr) :
    |P₀ * S / (J * sqrt E) - 1| ≤ berr + 8 * dS + 640 * (dJ / P₀) + 640 * dE := by
  have hP₀ne : P₀ ≠ 0 := ne_of_gt hP₀
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hJscaled : |J / P₀ - J₀ / P₀| ≤ dJ / P₀ := by
    rw [← sub_div, abs_div, abs_of_pos hP₀]
    exact div_le_div_of_nonneg_right hJE hP₀.le
  have hJsmall : dJ / P₀ ≤ 1 / 4 := (div_le_iff₀ hP₀).mpr (by nlinarith only [hJEsmall])
  have hJlower : 1 / 4 ≤ J / P₀ := by
    have hh := (abs_le.mp hJscaled).1
    nlinarith only [hh, hJ₀, hJsmall]
  have hden : 1 / 4 ≤ (J / P₀) * sqrt E := by
    have hh := mul_le_mul hJlower hrootE (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ J / P₀)
    nlinarith only [hh]
  have hJ₀abs : |J₀ / P₀| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ J₀ / P₀)]; exact hJ₀upper
  have hdenDiff : |(J / P₀) * sqrt E - J₀ / P₀| ≤ 2 * (dJ / P₀) + 2 * dE := by
    have hh := abs_product_difference hJscaled hrootEE hJ₀abs
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm (dJ / P₀) 2] using hh
  have hdiff := quotient_error_half_denominator hden hJ₀ hSE hS₀ hdenDiff
  have hJpos : 0 < J := by
    have hh : 0 < J / P₀ := by linarith only [hJlower]
    exact (div_pos_iff_of_pos_right hP₀).mp hh
  have hid : P₀ * S / (J * sqrt E) = S / ((J / P₀) * sqrt E) := by field_simp
  rw [hid]
  have ht := abs_add_le (S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀)) (S₀ / (J₀ / P₀) - 1)
  have hsum : S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀) + (S₀ / (J₀ / P₀) - 1) =
      S / ((J / P₀) * sqrt E) - 1 := by ring
  rw [hsum] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Absolute bounds for the ideal inversion-coordinate frame quantities. -/
theorem ideal_frame_absolute_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4) :
    idealFrameDenominator ε y z ≤ 2 ∧ |idealFrameNumerator ε y z| ≤ 20 := by
  have hy2 : y ^ 2 ≤ 1 / 4 := by nlinarith only [hy, hysmall]
  have hy3 : y ^ 3 ≤ 1 / 8 := by
    have hh := pow_le_pow_left₀ hy hysmall 3
    norm_num at hh
    exact hh
  have hy4 : y ^ 4 ≤ 1 / 16 := by
    have hh := pow_le_pow_left₀ hy hysmall 4
    norm_num at hh
    exact hh
  have hz2 : z ^ 2 ≤ 16 := by nlinarith only [hz, hzupper]
  have hε2 : ε ^ 2 ≤ 1 / 16 := by nlinarith only [hε, hεsmall]
  have hT : ε ^ 2 * y ^ 2 ≤ 1 / 64 := by
    have hh := mul_le_mul hε2 hy2 (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith only [hh]
  have hZ : (1 + y ^ 4) * z ^ 2 ≤ 17 := by
    have hh := mul_le_mul (show 1 + y ^ 4 ≤ 17 / 16 by linarith only [hy4]) hz2
      (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 17 / 16)
    nlinarith only [hh]
  have hεz : ε * z ≤ 1 := by
    have hh := mul_le_mul hεsmall hzupper hz (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [hh]
  have hU : 2 * ε * z * y ^ 3 ≤ 1 / 4 := by
    have hh := mul_le_mul hεz hy3 (pow_nonneg hy 3) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh]
  have hT0 : 0 ≤ ε ^ 2 * y ^ 2 := mul_nonneg (sq_nonneg ε) (sq_nonneg y)
  have hZ0 : 0 ≤ (1 + y ^ 4) * z ^ 2 := by positivity
  have hU0 : 0 ≤ 2 * ε * z * y ^ 3 := by positivity
  constructor
  · unfold idealFrameDenominator
    nlinarith only [hT0, hU]
  · unfold idealFrameNumerator
    apply abs_le.mpr
    constructor <;> nlinarith only [hT0, hZ0, hU0, hT, hZ, hU]

theorem target_sqrt_identity {y : ℝ} (hy : y ≠ 0) :
    sqrt (1 + (y⁻¹) ^ 4) = sqrt (1 + y ^ 4) / y ^ 2 := by
  have hid : 1 + (y⁻¹) ^ 4 = (1 + y ^ 4) / (y ^ 2) ^ 2 := by field_simp; ring
  rw [hid, Real.sqrt_div (by positivity : 0 ≤ 1 + y ^ 4), sqrt_sq (sq_nonneg y)]

/-- Ideal frame renewal expressed directly in the original scalar
solution and the target time, rather than in auxiliary Riccati variables. -/
theorem equation30_target_ideal_quantities
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    let t := y⁻¹ / ε
    let P₀ := ε ^ 2 * t ^ 2
    let Q₀ := -2 * ε ^ 2 * t
    let r₀ := -V₁ t / V t
    let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
    let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
    1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
      |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |S₀ / (J₀ / P₀) - 1| ≤ 1500 * ε := by
  let t := y⁻¹ / ε
  let P₀ := ε ^ 2 * t ^ 2
  let Q₀ := -2 * ε ^ 2 * t
  let r₀ := -V₁ t / V t
  let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
  let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
  let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hyne : y ≠ 0 := ne_of_gt hy
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht0
  have hPr : P₀ = (y⁻¹) ^ 2 := by dsimp [P₀, t]; field_simp
  have hQr : Q₀ = -2 * ε * y⁻¹ := by dsimp [Q₀, t]; field_simp
  have hr : r₀ = ε * y - z * y ^ 2 := by
    have hh := inverted_logarithmic_identity (V₁ := V₁) hεne hyne (ne_of_gt hVp)
    dsimp [r₀, t, z]
    rw [neg_div]
    nlinarith only [hh]
  have hJr : J₀ = idealFrameDenominator ε y z / y ^ 2 := by
    dsimp [J₀]
    rw [hPr, hQr, hr]
    exact (ideal_frame_identities hyne).1
  have hSr : S₀ = idealFrameNumerator ε y z := by
    dsimp [S₀, idealCrossNumerator]
    rw [hPr, hQr, hr]
    convert! (ideal_frame_identities (ε := ε) (z := z) hyne).2 using 1
    ring
  have hR := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith)
  have hB := equation30_ideal_frame_bounds hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  have hA := ideal_frame_absolute_bounds hε.le hεsmall hy.le hysmall hR.1 hR.2
  have hJP : J₀ / P₀ = idealFrameDenominator ε y z := by rw [hJr, hPr]; field_simp
  have hJroot : J₀ / sqrt (1 + P₀ ^ 2) = idealFrameDenominator ε y z / sqrt (1 + y ^ 4) := by
    rw [hJr, hPr]
    have hid : ((y⁻¹) ^ 2) ^ 2 = (y⁻¹) ^ 4 := by ring
    rw [hid, target_sqrt_identity hyne]
    field_simp
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  change 1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ _ ∧ |S₀ / (J₀ / P₀) - 1| ≤ _
  rw [hJP, hSr, hJroot]
  refine ⟨?_, hB.1, hA.1, hA.2, hB.2.2.1, hB.2.2.2⟩
  rw [hPr]
  nlinarith only [hyinv]

/-- The perturbed target ray keeps the shear compression strictly negative
with the reciprocal target-time magnitude used in equation (35). -/
theorem perturbed_target_compression
    {β t ε H P Q N ρ : ℝ}
    (hβ : 0 < β) (ht : 0 < t) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hscale : 1 ≤ β * t ^ 2) (_hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2) (hρQ : ρ ≤ β * t)
    (hP : |P - β * t ^ 2| ≤ ρ) (hQ : |Q + 2 * β * t| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hεQ : |ε * Q| ≤ 1 / 2) :
    H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  have hPb := abs_le.mp hP
  have hQb := abs_le.mp hQ
  have hNb := abs_le.mp hN
  have hPlower : β * t ^ 2 / 2 ≤ P := by nlinarith only [hPb, hρsmall, hscale]
  have hPupper : P ≤ 3 / 2 * (β * t ^ 2) := by nlinarith only [hPb, hρsmall, hscale]
  have hPpos : 0 < P := by nlinarith only [hPlower, hscale]
  have hQupper : Q ≤ -β * t := by nlinarith only [hQb, hρQ]
  have hNabs : |N| ≤ 3 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hNb, hρsmall]
  have hPabs : |P| ≤ 3 / 2 * (β * t ^ 2) := by rwa [abs_of_pos hPpos]
  have hPsq : P ^ 2 ≤ 9 / 4 * (β * t ^ 2) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg P) (by positivity : 0 ≤ 3 / 2 * (β * t ^ 2))).mpr hPabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hNsq : N ^ 2 ≤ 9 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg N) (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr hNabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hεQsq : ε ^ 2 * Q ^ 2 ≤ 1 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (ε * Q)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hεQ
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hscale2 : 1 ≤ (β * t ^ 2) ^ 2 := by nlinarith only [hscale]
  have hDupper : rayDenominator ε P Q N ≤ 5 * β ^ 2 * t ^ 4 := by
    unfold rayDenominator
    nlinarith only [hPsq, hNsq, hεQsq, hscale2]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  have hQP : Q * P ≤ -(β ^ 2 * t ^ 3) / 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hQupper hPpos.le
    have h₂ := mul_le_mul_of_nonneg_left hPlower (mul_nonneg hβ.le ht.le)
    nlinarith only [h₁, h₂]
  have hHε : 0 ≤ H * ε := mul_nonneg hH hε
  have hnum := mul_le_mul_of_nonneg_left hQP hHε
  have hnumtime := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 10 * t)
  have hden := mul_le_mul_of_nonneg_left hDupper hHε
  apply (div_le_div_iff₀ hDpos (by positivity : 0 < 10 * t)).mpr
  nlinarith only [hnumtime, hden]

/-- The coordinate quadratic form of a real three-by-three matrix. -/
def quadraticForm3 (B : Fin 3 → Fin 3 → ℝ) (p q n : ℝ) : ℝ :=
  p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) +
  q * (B 1 0 * p + B 1 1 * q + B 1 2 * n) +
  n * (B 2 0 * p + B 2 1 * q + B 2 2 * n)

theorem quadratic_form_bound
    {B : Fin 3 → Fin 3 → ℝ} {G p q n : ℝ}
    (hB : ∀ i j, |B i j| ≤ G) :
    |quadraticForm3 B p q n| ≤ 3 * G * (p ^ 2 + q ^ 2 + n ^ 2) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hB 0 0)
  have hrow0 := three_term_bound (p := p) (q := q) (n := n) (hB 0 0) (hB 0 1) (hB 0 2)
  have hrow1 := three_term_bound (p := p) (q := q) (n := n) (hB 1 0) (hB 1 1) (hB 1 2)
  have hrow2 := three_term_bound (p := p) (q := q) (n := n) (hB 2 0) (hB 2 1) (hB 2 2)
  have h₀ := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg p)
  have h₁ := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg q)
  have h₂ := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg n)
  have ht0 := abs_add_le (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n))
    (q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
  have ht1 := abs_add_le
    (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) + q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
    (n * (B 2 0 * p + B 2 1 * q + B 2 2 * n))
  simp only [abs_mul] at ht0 ht1
  have hnorm : norm3 p q n ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + n ^ 2) := by
    have h₁ := sq_nonneg (|p| - |q|)
    have h₂ := sq_nonneg (|p| - |n|)
    have h₃ := sq_nonneg (|q| - |n|)
    have hp := sq_abs p
    have hq := sq_abs q
    have hn := sq_abs n
    unfold norm3
    nlinarith only [h₁, h₂, h₃, hp, hq, hn]
  have hm := mul_le_mul_of_nonneg_left hnorm hG
  unfold quadraticForm3 norm3 at *
  nlinarith only [h₀, h₁, h₂, ht0, ht1, hm]

/-- The full normalized compression is the negative shear term plus a
controlled contribution from the older gradient and the packet error. -/
theorem parent_ray_compression
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G : ℝ}
    (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N ≤
      H * ε * Q * P / rayDenominator ε P Q N + 3 * G := by
  have hid : quadraticForm3 (parentEntry B E H) P (ε * Q) N =
      H * ε * Q * P + quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N := by
    norm_num [quadraticForm3, parentEntry, Fin.ext_iff]
    ring
  have hb := quadratic_form_bound (p := P) (q := ε * Q) (n := N) hB
  have hquad : quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N ≤
      3 * G * rayDenominator ε P Q N := by
    have hh := le_abs_self (quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N)
    unfold rayDenominator
    nlinarith only [hh, hb]
  rw [hid, add_div]
  gcongr
  exact (div_le_iff₀ hD).mpr hquad

/-- The ideal pressure-to-velocity ratio at the inverse target scale. -/
noncomputable def idealTargetPressure (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-V₁ t / V t)

/-- The ideal cross numerator at the inverse target scale. -/
noncomputable def idealTargetCross (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  idealCrossNumerator (ε ^ 2) (ε ^ 2 * t ^ 2) (-2 * ε ^ 2 * t) (-V₁ t / V t)

/-- Actual target-frame renewal, with all ideal quantities obtained from
the scalar equation and all perturbation losses displayed explicitly. -/
theorem equation30_target_frame_renewal
    {ε y D E J S dD dE dJ dS : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0)
    (hD : 1 / 4 ≤ D) (hE : 1 ≤ E)
    (hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - idealTargetPressure ε y V V₁| ≤ dJ) (hJEsmall : dJ ≤ (y⁻¹) ^ 2 / 4)
    (hSE : |S - idealTargetCross ε y V V₁| ≤ dS) :
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 + 4 * dJ +
        16 * (y⁻¹) ^ 2 * dD + 16 * (y⁻¹) ^ 4 * dE ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤
      1500 * ε + 8 * dS + 640 * (dJ / (y⁻¹) ^ 2) + 640 * dE := by
  let t := y⁻¹ / ε
  let P₀ := (y⁻¹) ^ 2
  let J₀ := idealTargetPressure ε y V V₁
  let S₀ := idealTargetCross ε y V V₁
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hPeq : ε ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hI := equation30_target_ideal_quantities hε hεsmall hy hysmall hV hflux hV0 hV₁0
  change 1 ≤ ε ^ 2 * t ^ 2 ∧ 1 / 2 ≤ J₀ / (ε ^ 2 * t ^ 2) ∧
    J₀ / (ε ^ 2 * t ^ 2) ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + (ε ^ 2 * t ^ 2) ^ 2) - 1| ≤ _ ∧
    |S₀ / (J₀ / (ε ^ 2 * t ^ 2)) - 1| ≤ _ at hI
  rw [hPeq] at hI
  obtain ⟨hP₀, hJ₀lower, hJ₀upper, hS₀, hAideal, hBideal⟩ := hI
  have hP₀pos : 0 < P₀ := by linarith
  have hJ₀pos : 0 < J₀ := by
    have hh := (le_div_iff₀ hP₀pos).mp hJ₀lower
    nlinarith only [hh, hP₀pos]
  have hJ₀abs : |J₀| ≤ 2 * P₀ := by
    rw [abs_of_pos hJ₀pos]
    exact (div_le_iff₀ hP₀pos).mp hJ₀upper
  have hD₀ : 1 ≤ 1 + P₀ ^ 2 := by nlinarith [sq_nonneg P₀]
  have hroot : sqrt (1 + P₀ ^ 2) ≤ 2 * P₀ := by
    have hh := sq_sqrt (by positivity : 0 ≤ 1 + P₀ ^ 2)
    have hn := sqrt_nonneg (1 + P₀ ^ 2)
    nlinarith only [hh, hn, hP₀]
  have hD₀eq : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
  have hDE' : |D - (1 + P₀ ^ 2)| ≤ dD := by rwa [hD₀eq]
  have ha := expansion_quotient_error hD hD₀ hE hDE' hEE hdE hJE hJ₀abs hroot hAideal
  have hb := coupling_quotient_error hP₀pos hE hEE hdE hJE hJEsmall hJ₀lower hJ₀upper hSE hS₀ hBideal
  constructor
  · dsimp [P₀] at ha
    nlinarith only [ha]
  · exact hb

end EulerPacketFrameRenewal

end

section

open Set

namespace EulerPacketFrameQuantitative

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability EulerPacketFrameRenewal

/-- Comparison of the polynomial losses on a common time scale. -/
theorem scaled_power_le
    {Θ K e : ℝ} {n m : ℕ} (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hnm : n ≤ m) :
    e * Θ ^ n ≤ K * e * Θ ^ m := by
  have hpow := pow_le_pow_right₀ hΘ hnm
  have hm := mul_le_mul_of_nonneg_left hpow he
  have hKmul := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ e * Θ ^ m)
  nlinarith only [hm, hKmul]

/-- Explicit polynomial control of all target-frame perturbation losses. -/
theorem frame_error_polynomial_bounds
    {Θ K e ε P₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hP₀ : 1 ≤ P₀) (hP₀upper : P₀ ≤ Θ ^ 2) :
    let ρ := 800 * e * Θ ^ 5
    let η := K * e * Θ ^ 29
    let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
    let dE := 3681 * ε ^ 2 * Θ ^ 4
    let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
    let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
    ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
      4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
      8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 := by
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let M := K * e * Θ ^ 40
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hKp (n : ℕ) (hn : n ≤ 40) : K * e * Θ ^ n ≤ M := by
    have hh := pow_le_pow_right₀ hΘ hn
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ K * e)
    exact hm
  have he1 : e ≤ 1 := by
    have hh := hp 0 (by decide)
    norm_num at hh
    nlinarith only [hh, hMb]
  have hε1 : ε ≤ 1 := hεe.trans he1
  have hε2 : ε ^ 2 ≤ e := by nlinarith only [hε, hε1, hεe]
  have hεp (n : ℕ) (hn : n ≤ 40) : ε ^ 2 * Θ ^ n ≤ M := by
    have hh := mul_le_mul_of_nonneg_right hε2 (by positivity : 0 ≤ Θ ^ n)
    exact hh.trans (hp n hn)
  have hρb : ρ ≤ 1 / 2 := by have hh := hp 5 (by decide); dsimp [ρ]; nlinarith only [hh, hMb]
  have hηb : η ≤ 1 / 2 := by have hh := hKp 29 (by decide); dsimp [η]; nlinarith only [hh, hMb]
  have hAb : 210 * e * Θ ^ 2 ≤ 1 := by have hh := hp 2 (by decide); nlinarith only [hh, hMb]
  have hEb : dE ≤ 1 := by have hh := hεp 4 (by decide); dsimp [dE]; nlinarith only [hh, hMb]
  have hJbound : dJ ≤ 17490 * M := by
    have h4 := hp 4 (by decide)
    have h5 := hp 5 (by decide)
    have h31 := hKp 31 (by decide)
    dsimp [dJ, ρ, η]
    nlinarith only [h4, h5, h31]
  have hJb : dJ ≤ P₀ / 4 := by nlinarith only [hJbound, hMb, hP₀]
  have hD0 : 0 ≤ dD := by dsimp [dD, ρ]; positivity
  have hE0 : 0 ≤ dE := by dsimp [dE]; positivity
  have hJ0 : 0 ≤ dJ := by dsimp [dJ, ρ, η]; positivity
  have hP₀0 : 0 ≤ P₀ := by linarith
  have hP₀sq : P₀ ^ 2 ≤ Θ ^ 4 := by
    have hh := (sq_le_sq₀ hP₀0 (sq_nonneg Θ)).mpr hP₀upper
    nlinarith only [hh]
  have hPD : P₀ * dD ≤ 4809 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀upper hD0
    have h9 := hp 9 (by decide)
    have h6 := hεp 6 (by decide)
    dsimp [dD, ρ] at hm ⊢
    nlinarith only [hm, h9, h6]
  have hPE : P₀ ^ 2 * dE ≤ 3681 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀sq hE0
    have h8 := hεp 8 (by decide)
    dsimp [dE] at hm ⊢
    nlinarith only [hm, h8]
  have hSbound : dS ≤ 883420 * M := by
    have h9 := hp 9 (by decide)
    have h33 := hKp 33 (by decide)
    have h6 := hp 6 (by decide)
    have h4 := hεp 4 (by decide)
    dsimp [dS, ρ, η]
    nlinarith only [h9, h33, h6, h4]
  have hEbound : dE ≤ 3681 * M := by
    have hh := hεp 4 (by decide)
    dsimp [dE]
    nlinarith only [hh]
  have hJdiv : dJ / P₀ ≤ dJ := by
    apply (div_le_iff₀ (by linarith : 0 < P₀)).mpr
    nlinarith only [mul_nonneg hJ0 (sub_nonneg.mpr hP₀)]
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40
  dsimp [M] at hJbound hPD hPE hSbound hEbound hM
  refine ⟨hρb, hηb, hAb, hEb, hJb, ?_, ?_⟩
  · nlinarith only [hJbound, hPD, hPE, hM]
  · nlinarith only [hSbound, hJbound, hJdiv, hEbound, hM]

/-- The source's `Θ^40` frame-renewal estimate, derived from coefficient,
ray, and relative state errors and the actual scalar initial value problem. -/
theorem frame_renewal_order40
    {σ y Θ K e ε P Q N r : ℝ} {A : Fin 3 → Fin 3 → ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (htΘ : y⁻¹ / σ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P - (y⁻¹) ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * σ * y⁻¹| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5)
    (hr : |r + Z₁ (y⁻¹ / σ) / Z (y⁻¹ / σ)| ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |A i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    let w := velocityThird P Q N r 1
    let D := rayDenominator ε P Q N
    let E := velocityDirectionNormSq ε r w
    let J := velocityNumerator A P Q N r 1 w
    let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w)
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + σ ^ 2 * y ^ 2 + 8 * σ * y ^ 3 + 30000000 * K * e * Θ ^ 40 ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ 1500 * σ + 30000000 * K * e * Θ ^ 40 := by
  let t := y⁻¹ / σ
  let P₀ := (y⁻¹) ^ 2
  let Q₀ := -2 * σ * y⁻¹
  let r₀ := -Z₁ t / Z t
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let w := velocityThird P Q N r 1
  let D := rayDenominator ε P Q N
  let E := velocityDirectionNormSq ε r w
  let J := velocityNumerator A P Q N r 1 w
  let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r w)
  have hΘ0 : 0 ≤ Θ := by linarith
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hyinv0 : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  have hyinvΘ : y⁻¹ ≤ Θ := by
    have hh := (div_le_iff₀ hσ).mp htΘ
    have hm := mul_le_mul_of_nonneg_left (show σ ≤ 1 by linarith) hΘ0
    nlinarith only [hh, hm]
  have ht : 1 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hσ).mpr
    nlinarith only [hyinv, hσsmall]
  have hP₀ : 1 ≤ P₀ := by dsimp [P₀]; nlinarith only [hyinv]
  have hP₀upper : P₀ ≤ Θ ^ 2 := (sq_le_sq₀ hyinv0 hΘ0).mpr hyinvΘ
  have hP₀abs : |P₀| ≤ Θ ^ 2 := by rw [abs_of_nonneg (by dsimp [P₀]; positivity)]; exact hP₀upper
  have hQ₀abs : |Q₀| ≤ 2 * Θ ^ 2 := by
    dsimp [Q₀]
    rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_nonneg hyinv0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hyinv0
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hm, hyinvΘ, hΘ2]
  have hσabs : |σ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg σ)]; nlinarith only [hσ, hσsmall]
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hpoly := frame_error_polynomial_bounds hΘ hK he hε hεe hsmall hP₀ hP₀upper
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 at hpoly
  obtain ⟨hρsmall, hηsmall, hAsmall, hEsmall, hJsmall, hAbound, hBbound⟩ := hpoly
  have hQ' : |Q - Q₀| ≤ ρ := by
    have hid : Q - Q₀ = Q + 2 * σ * y⁻¹ := by dsimp [Q₀]; ring
    rwa [hid]
  have hr₀ : |r₀| ≤ 4 := by
    have hh := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 t ht
    simpa only [r₀, neg_div, abs_neg] using hh
  have hr' : |r - r₀| ≤ 10 * η := by
    simpa only [r₀, t, neg_div, sub_neg_eq_add] using hr
  obtain ⟨hrabs, _, hwabs, _⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall hP₀abs hQ₀abs hP hQ' hN hr₀ hr'
  obtain ⟨_, hp, hq, hn, hw, hDlower, hDerror⟩ :=
    ray_geometric_bounds (ε := ε) (U := r) (V := 1) hΘ hρ hρsmall hP₀abs hQ₀abs hP hQ' hN
  have hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD := by
    have hid : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
    rw [hid] at hDerror
    exact hDerror
  have hEnorm := velocity_direction_norm_bound (ε := ε) hΘ hrabs hwabs
  have hEE : E - 1 ≤ dE := hEnorm.2
  have hE : 1 ≤ E := hEnorm.1
  have hcross := frame_cross_error_from_matrix (ε := ε) hΘ hρ hρsmall hη hηsmall
    (by positivity : 0 ≤ 3 * e) (by nlinarith only [hAsmall] : 70 * (3 * e) * Θ ^ 2 ≤ 1)
    hσabs hP₀abs hQ₀abs hP hQ' hN hr₀ hr' hA
  have hSE' : |S - idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀| ≤ dS := by
    dsimp only at hcross
    dsimp [S, dS]
    nlinarith only [hcross]
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hJraw : |J - ((P₀ + σ ^ 2) * 1 + Q₀ * r)| ≤ j * (|r| + |(1 : ℝ)|) := by
    have hh := velocity_numerator_error hΘ hρ (by positivity : 0 ≤ 3 * e) hσabs hA hp hq hn hP hQ' hN hw
    dsimp [J, j, w, P₀]
    nlinarith only [hh]
  have hpressure := pressure_ratio_error hΘ hη hηsmall hj (by norm_num : (0 : ℝ) < 1)
    hQ₀abs hr₀ (by simpa only [div_one] using hr') hJraw
  have hJE' : |J - (P₀ + σ ^ 2 + Q₀ * r₀)| ≤ dJ := by
    simp only [div_one] at hpressure
    dsimp [j, dJ] at *
    nlinarith only [hpressure]
  have hPeq : σ ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hQeq : -2 * σ ^ 2 * t = Q₀ := by dsimp [t, Q₀]; field_simp
  have hJideal : idealTargetPressure σ y Z Z₁ = P₀ + σ ^ 2 + Q₀ * r₀ := by
    change σ ^ 2 * t ^ 2 + σ ^ 2 + (-2 * σ ^ 2 * t) * r₀ = _
    rw [hPeq, hQeq]
  have hSideal : idealTargetCross σ y Z Z₁ = idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀ := by
    change idealCrossNumerator (σ ^ 2) (σ ^ 2 * t ^ 2) (-2 * σ ^ 2 * t) r₀ = _
    rw [hPeq, hQeq]
  have hJE : |J - idealTargetPressure σ y Z Z₁| ≤ dJ := by rwa [hJideal]
  have hSE : |S - idealTargetCross σ y Z Z₁| ≤ dS := by rwa [hSideal]
  have hrenew := equation30_target_frame_renewal hσ hσsmall hy hysmall hZ hfluxZ hZ0 hZ₁0
    hDlower hE hDE hEE hEsmall hJE hJsmall hSE
  change |J / (sqrt D * sqrt E) - 1| ≤ _ ∧ |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ _
  constructor
  · have hh := hrenew.1
    dsimp [P₀] at hAbound
    nlinarith only [hh, hAbound]
  · have hh := hrenew.2
    exact hh.trans (by dsimp [P₀] at hBbound; nlinarith only [hBbound])

end EulerPacketFrameQuantitative

end

section

open Function intervalIntegral MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace EulerPacketExistence

section GlobalPicard

variable {E : Type*} [NormedAddCommGroup E]
  {a b : ℝ} (t₀ : Icc a b)

/-- Extend a continuous curve from a compact interval by endpoint values. -/
noncomputable def extendCurve (α : C(Icc a b, E)) (t : ℝ) : E :=
  α (projIcc a b (t₀.2.1.trans t₀.2.2) t)

theorem continuous_extendCurve (α : C(Icc a b, E)) : Continuous (extendCurve t₀ α) :=
  α.continuous.comp continuous_projIcc

theorem extendCurve_of_mem (α : C(Icc a b, E)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendCurve t₀ α t = α ⟨t, ht⟩ := by
  simp only [extendCurve, projIcc_of_mem _ ht]

variable {f : ℝ → E → E} (hf : Continuous (uncurry f))

include hf

theorem continuous_comp_extendCurve (α : C(Icc a b, E)) :
    Continuous (fun t => f t (extendCurve t₀ α t)) :=
  hf.comp (continuous_id.prodMk (continuous_extendCurve t₀ α))

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Volterra map on all continuous curves, without a spatial-radius
restriction.  Global Lipschitz continuity makes an iterate contractive. -/
noncomputable def picardStep (x : E) (α : C(Icc a b, E)) : C(Icc a b, E) :=
  ⟨fun t => x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s),
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous
      (continuous_comp_extendCurve t₀ hf α)).continuous).comp continuous_subtype_val⟩

theorem picardStep_apply (x : E) (α : C(Icc a b, E)) (t : Icc a b) :
    picardStep t₀ hf x α t = x + ∫ s in t₀.1..t.1, f s (extendCurve t₀ α s) := rfl

variable {K : ℝ≥0} (hLip : ∀ t, LipschitzWith K (f t))

include hLip

theorem picard_iterate_point_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) (t : Icc a b) :
    dist (((picardStep t₀ hf x)^[n]) α t) (((picardStep t₀ hf x)^[n]) β t) ≤
      (K * |t.1 - t₀.1|) ^ n / n ! * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, picardStep_apply,
      picardStep_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)
        ((continuous_comp_extendCurve t₀ hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in uIoc t₀.1 t.1, K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hsi : s ∈ Icc a b := (uIcc_subset_Icc t₀.2 t.2) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, extendCurve_of_mem t₀ _ hsi, extendCurve_of_mem t₀ _ hsi]
        calc
          _ ≤ K * dist (((picardStep t₀ hf x)^[n]) α ⟨s, hsi⟩)
              (((picardStep t₀ hf x)^[n]) β ⟨s, hsi⟩) := (hLip s).dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |s - t₀.1| ^ n / n ! * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨s, hsi⟩
      _ ≤ (K * |t.1 - t₀.1|) ^ (n + 1) / (n + 1) ! * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem picard_iterate_bound (x : E) (α β : C(Icc a b, E)) (n : ℕ) :
    dist (((picardStep t₀ hf x)^[n]) α) (((picardStep t₀ hf x)^[n]) β) ≤
      (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! * dist α β := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply le_trans (picard_iterate_point_bound t₀ hf hLip x α β n t)
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity

theorem exists_picard_fixed_point (x : E) :
    ∃ α : C(Icc a b, E), IsFixedPt (picardStep t₀ hf x) α := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (b - t₀.1) (t₀.1 - a))
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : ℝ) ≤ (K * max (b - t₀.1) (t₀.1 - a)) ^ n / n ! := by
    have hmax : 0 ≤ max (b - t₀.1) (t₀.1 - a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
    positivity
  let C : ℝ≥0 := ⟨(K * max (b - t₀.1) (t₀.1 - a)) ^ n / n !, hnonneg⟩
  have hcontract : ContractingWith C ((picardStep t₀ hf x)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun α β => picard_iterate_bound t₀ hf hLip x α β n⟩
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- A globally Lipschitz time-dependent vector field has a solution on
every finite interval.  Full derivatives also hold at the endpoints. -/
theorem exists_solution_on_compact_interval (x : E) :
    ∃ α : ℝ → E, α t₀.1 = x ∧
      ∀ t ∈ Icc a b, HasDerivAt α (f t (α t)) t := by
  obtain ⟨α, hfixed⟩ := exists_picard_fixed_point t₀ hf hLip x
  let u : ℝ → E := fun t => x + ∫ s in t₀.1..t, f s (extendCurve t₀ α s)
  have heq : ∀ t ∈ Icc a b, u t = extendCurve t₀ α t := by
    intro t ht
    have hh := congrArg (fun v : C(Icc a b, E) => v ⟨t, ht⟩) hfixed
    rw [extendCurve_of_mem t₀ α ht]
    exact hh
  have hc := continuous_comp_extendCurve t₀ hf α
  refine ⟨u, by simp [u], ?_⟩
  intro t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := t₀.1) (b := t) (hc.intervalIntegrable t₀.1 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x
  change HasDerivAt u (f t (u t)) t
  rw [heq t ht]
  exact hd

end GlobalPicard

/-- Global existence for a jointly continuous vector field with a uniform
global Lipschitz constant in the state variable.  Finite-interval solutions
are glued using the proved ODE uniqueness theorem. -/
theorem exists_global_solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {K : ℝ≥0}
    (hf : Continuous (uncurry f)) (hLip : ∀ t, LipschitzWith K (f t)) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f t (u t)) t := by
  classical
  have hlocal : ∀ R : ℝ, 0 < R → ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-R) R, HasDerivAt u (f t (u t)) t := by
    intro R hR
    let t₀ : Icc (-R) R := ⟨0, by constructor <;> linarith⟩
    exact exists_solution_on_compact_interval t₀ hf hLip x
  choose v hv0 hvd using hlocal
  let u : ℝ → E := fun t => v (|t| + 1) (by positivity) t
  have hagree : ∀ R (hR : 0 < R), EqOn u (v R hR) (Ioo (-R) R) := by
    intro R hR s hs
    let R' := |s| + 1
    have hR' : 0 < R' := by dsimp [R']; positivity
    let B := min R R'
    have hB : 0 < B := lt_min hR hR'
    have hBR : B ≤ R := min_le_left _ _
    have hBR' : B ≤ R' := min_le_right _ _
    have hzero : (0 : ℝ) ∈ Ioo (-B) B := by constructor <;> linarith
    have hsB : s ∈ Ioo (-B) B := by
      apply abs_lt.mp
      apply lt_min (abs_lt.mpr hs)
      dsimp [R']
      linarith
    have heq := ODE_solution_unique_of_mem_Ioo (v := f) (s := fun _ => (univ : Set E))
      (fun t _ => (hLip t).lipschitzOnWith) hzero
      (fun t ht => ⟨hvd R hR t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (fun t ht => ⟨hvd R' hR' t (by constructor <;> linarith [ht.1, ht.2]), mem_univ _⟩)
      (by rw [hv0 R hR, hv0 R' hR'])
    exact (heq hsB).symm
  refine ⟨u, ?_, ?_⟩
  · exact hv0 (|0| + 1) (by positivity)
  · intro t
    let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      apply abs_lt.mp
      dsimp [R]
      linarith
    have heq : u =ᶠ[𝓝 t] v R hR := Filter.eventually_of_mem
      (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hagree R hR hs)
    have hd := hvd R hR t (Ioo_subset_Icc_self ht)
    rw [hagree R hR ht]
    exact hd.congr_of_eventuallyEq heq

/-- The displacement coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientA (β t : ℝ) : ℝ :=
  2 * (1 - β * (β * t ^ 2)) / (1 + (β * t ^ 2) ^ 2)

/-- The velocity coefficient in the first-order form of equation (30). -/
noncomputable def scalarCoefficientB (β t : ℝ) : ℝ :=
  -(4 * β ^ 2 * t ^ 3) / (1 + (β * t ^ 2) ^ 2)

/-- The scalar equation as a globally Lipschitz two-dimensional system. -/
noncomputable def scalarVectorField (β t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)

theorem scalar_coefficient_bounds
    {β t : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    |scalarCoefficientA β t| ≤ 3 ∧ |scalarCoefficientB β t| ≤ 4 := by
  have hD : 0 < 1 + (β * t ^ 2) ^ 2 := by positivity
  have hx : 0 ≤ β * t ^ 2 := mul_nonneg hβ (sq_nonneg t)
  have hβx : β * (β * t ^ 2) ≤ β * t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hβupper hx
    simpa only [one_mul] using hh
  have hβx0 : 0 ≤ β * (β * t ^ 2) := mul_nonneg hβ hx
  constructor
  · unfold scalarCoefficientA
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    apply abs_le.mpr
    constructor <;> nlinarith only [hβx, hβx0, sq_nonneg (β * t ^ 2 - 1), sq_nonneg (β * t ^ 2)]
  · have hβ2 : β ^ 2 ≤ 1 := by nlinarith only [hβ, hβupper]
    have ht3 : β ^ 2 * |t| ^ 3 ≤ 1 + (β * t ^ 2) ^ 2 := by
      by_cases ht : |t| ≤ 1
      · have hh : |t| ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ (abs_nonneg t) ht 3
        have hm := mul_le_mul hβ2 hh (pow_nonneg (abs_nonneg t) 3) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith only [hm, sq_nonneg (β * t ^ 2)]
      · have hh : |t| ^ 3 ≤ |t| ^ 4 := pow_le_pow_right₀ (le_of_not_ge ht) (by decide)
        have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg β)
        have ht4 : |t| ^ 4 = t ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)]
        rw [ht4] at hm
        nlinarith only [hm]
    unfold scalarCoefficientB
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (sq_nonneg β), abs_pow, abs_of_pos hD, div_le_iff₀ hD]
    nlinarith only [ht3]

theorem continuous_scalarVectorField (β : ℝ) : Continuous (uncurry (scalarVectorField β)) := by
  have hden : ∀ p : ℝ × (ℝ × ℝ), 1 + (β * p.1 ^ 2) ^ 2 ≠ 0 := by intro p; positivity
  unfold scalarVectorField scalarCoefficientA scalarCoefficientB Function.uncurry
  fun_prop

theorem lipschitz_scalarVectorField
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (t : ℝ) :
    LipschitzWith 7 (scalarVectorField β t) := by
  obtain ⟨ha, hb⟩ := scalar_coefficient_bounds (t := t) hβ hβupper
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hfst : |x.1 - y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsnd : |x.2 - y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  change max (dist x.2 y.2)
    (dist (scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2)
      (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2)) ≤ (7 : ℝ) * dist x y
  apply max_le
  · rw [Real.dist_eq]
    nlinarith only [hsnd, dist_nonneg (x := x) (y := y)]
  · rw [Real.dist_eq]
    have h₁ := mul_le_mul ha hfst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    have h₂ := mul_le_mul hb hsnd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    have hh := abs_add_le (scalarCoefficientA β t * (x.1 - y.1))
      (scalarCoefficientB β t * (x.2 - y.2))
    rw [abs_mul, abs_mul] at hh
    have hid : scalarCoefficientA β t * x.1 + scalarCoefficientB β t * x.2 -
        (scalarCoefficientA β t * y.1 + scalarCoefficientB β t * y.2) =
        scalarCoefficientA β t * (x.1 - y.1) + scalarCoefficientB β t * (x.2 - y.2) := by ring
    rw [hid]
    nlinarith only [h₁, h₂, hh]

/-- Global construction of equation (30) for arbitrary real initial data. -/
theorem equation30_exists_global
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) (v₀ v₁ : ℝ) :
    ∃ V V₁ : ℝ → ℝ, V 0 = v₀ ∧ V₁ 0 = v₁ ∧
      (∀ t, HasDerivAt V (V₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - β * (β * t ^ 2)) * V t) t) := by
  obtain ⟨u, hu0, hud⟩ := exists_global_solution (continuous_scalarVectorField β)
    (lipschitz_scalarVectorField hβ hβupper) (v₀, v₁)
  let V : ℝ → ℝ := fun t => (u t).1
  let V₁ : ℝ → ℝ := fun t => (u t).2
  refine ⟨V, V₁, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst hu0
  · exact congrArg Prod.snd hu0
  · intro t
    exact (hud t).fst
  · intro t
    have hV₁ := (hud t).snd
    have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
      convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
      simp only [Pi.pow_apply, id_eq]
      ring
    have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
    apply (hD.mul hV₁).congr_deriv
    dsimp [scalarVectorField, scalarCoefficientA, scalarCoefficientB, V, V₁]
    field_simp
    ring

/-- A constructed primary scalar solution has the exponential growth,
positivity, and uniform logarithmic-slope properties used in the source.
There is no solution-existence hypothesis in this statement. -/
theorem equation30_exists_growing_primary
    {ε lam : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hlam : 0 ≤ lam) :
    ∃ V V₁ : ℝ → ℝ, V 0 = 1 ∧ V₁ 0 = lam ∧
      (∀ t, HasDerivAt V (V₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t) ∧
      Real.exp (1 / (4 * ε)) ≤ V (1 / ε) ∧
      (∀ t, 0 ≤ t → 0 < V t) ∧
      (∀ t, 1 ≤ t → |V₁ t / V t| ≤ 4) ∧
      (∀ y, 0 < y → y ≤ 1 / 2 →
        let z := -ε * EulerPacketGrowth.invertedScalarDeriv ε V V₁ y /
          EulerPacketGrowth.invertedScalar ε V y
        |z ^ 2 - 2 / (1 + y ^ 4)| ≤ 360 * ε) := by
  have hβ : ε ^ 2 ≤ 1 := by nlinarith only [hε, hεsmall]
  obtain ⟨V, V₁, hV0, hV₁0, hV, hflux⟩ := equation30_exists_global (sq_nonneg ε) hβ 1 lam
  have hV₁0pos : 0 ≤ V₁ 0 := by rw [hV₁0]; exact hlam
  have hgrowth := EulerPacketGrowth.equation30_endpoint_exponential (sq_pos_of_pos hε)
    (by nlinarith only [hε, hεsmall] : ε ^ 2 ≤ 1 / 16)
    (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  rw [Real.sqrt_sq hε.le] at hgrowth
  refine ⟨V, V₁, hV0, hV₁0, hV, hflux, hgrowth, ?_, ?_, ?_⟩
  · exact EulerPacketGrowth.equation30_global_positive hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  · exact EulerPacketFrameStability.equation30_primary_logderivative_bound hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos
  · exact EulerPacketGrowth.equation30_inverted_riccati_error hε hεsmall
      (fun t _ => hV t) (fun t _ => hflux t) hV0 hV₁0pos

/-- Construction of the two exact fundamental solutions required by the
relative propagator and Duhamel estimates. -/
theorem equation30_exists_fundamental_system
    {β : ℝ} (hβ : 0 ≤ β) (hβupper : β ≤ 1) :
    ∃ F F₁ G G₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ G 0 = 0 ∧ G₁ 0 = 1 ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧
      (∀ t, HasDerivAt G (G₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - β * (β * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (β * s ^ 2) ^ 2) * G₁ s)
        (2 * (1 - β * (β * t ^ 2)) * G t) t) := by
  obtain ⟨F, F₁, hF0, hF₁0, hF, hfluxF⟩ := equation30_exists_global hβ hβupper 1 0
  obtain ⟨G, G₁, hG0, hG₁0, hG, hfluxG⟩ := equation30_exists_global hβ hβupper 0 1
  exact ⟨F, F₁, G, G₁, hF0, hF₁0, hG0, hG₁0, hF, hG, hfluxF, hfluxG⟩

end EulerPacketExistence

end

section

open Set

namespace EulerPacketStage

open Real EulerPacketGrowth EulerPacketRay EulerPacketBridge EulerPacketFrameStability
  EulerPacketFrameRenewal EulerPacketFrameQuantitative EulerPacketExistence

/-- Absolute relative-stability constant obtained from the propagator
bound and the primary-solution lower comparison. -/
noncomputable def stabilityConstant : ℝ := 320000000 * exp 6

theorem stabilityConstant_ge : 320000000 ≤ stabilityConstant := by
  have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
  unfold stabilityConstant
  nlinarith only [hh]

/-- The controlled velocity system has an exact scalar comparison
solution, constructed from the axioms rather than supplied as a hypothesis. -/
theorem controlled_stage_references
    {σ Θ T e ε lam : ℝ} {U V P Q N : ℝ → ℝ} {R A C : ℝ → Fin 3 → Fin 3 → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hΘ : 1 ≤ Θ)
    (hT0 : 0 ≤ T) (hT : T ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hlam : 0 ≤ lam) (hsmall : 1000000 * stabilityConstant * e * Θ ^ 40 ≤ 1)
    (hRc : ∀ i j, ContinuousOn (fun t => R t i j) (Icc 0 T))
    (hAc : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hCc : ∀ i j, ContinuousOn (fun t => C t i j) (Icc 0 T))
    (hP : ∀ t ∈ Icc 0 T, HasDerivAt P
      (R t 0 0 * P t + R t 0 1 * Q t + R t 0 2 * N t) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivAt Q
      (R t 1 0 * P t + R t 1 1 * Q t + R t 1 2 * N t) t)
    (hN : ∀ t ∈ Icc 0 T, HasDerivAt N
      (R t 2 0 * P t + R t 2 1 * Q t + R t 2 2 * N t) t)
    (hU : ∀ t ∈ Icc 0 T, HasDerivAt U
      (velocityFirstRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hV : ∀ t ∈ Icc 0 T, HasDerivAt V
      (velocitySecondRhs (A t) (C t) ε (P t) (Q t) (N t) (U t) (V t)) t)
    (hRclose : ∀ t ∈ Icc 0 T, ∀ i j, |R t i j - idealRayEntry (σ ^ 2) i j| ≤ 4 * e)
    (hAclose : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e)
    (hCclose : ∀ t ∈ Icc 0 T, ∀ i j, |C t i j - idealUnprojectedEntry i j| ≤ 5 * e)
    (hrayInitial : norm3 (P 0) (Q 0) (N 0 - 1) ≤ e)
    (hU0 : U 0 = -lam) (hV0 : V 0 = 1) :
    ∃ F F₁ Z Z₁ : ℝ → ℝ,
      F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = lam ∧
      (∀ t, HasDerivAt F (F₁ t) t) ∧ (∀ t, HasDerivAt Z (Z₁ t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t) ∧
      (∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t) ∧
      (∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤
        160000000 * e * Θ ^ 29 * (1 + lam) * F t) ∧
      (∀ t ∈ Icc 1 T, 0 < V t ∧
        |V t / Z t - 1| ≤ stabilityConstant * e * Θ ^ 29 ∧
        |U t / V t + Z₁ t / Z t| ≤ 10 * (stabilityConstant * e * Θ ^ 29)) := by
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, G, G₁, hF0, hF₁0, _, hG₁0, hF, hG, hfluxF, hfluxG⟩ :=
    equation30_exists_fundamental_system (sq_nonneg σ) hσ2
  obtain ⟨Z, Z₁, hZ0, hZ₁0, hZ, hfluxZ⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 lam
  have hK := stabilityConstant_ge
  have hΘ0 : 0 ≤ Θ := by linarith
  have hpow21 : Θ ^ 21 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hpow29 : Θ ^ 29 ≤ Θ ^ 40 := pow_le_pow_right₀ hΘ (by decide)
  have hsmallODE : 8000000 * e * Θ ^ 21 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow21 he
    have hKmul := mul_nonneg (show 0 ≤ stabilityConstant - 8 by linarith)
      (mul_nonneg he (pow_nonneg hΘ0 40))
    nlinarith only [hsmall, hm, hKmul]
  have herror := controlled_velocity_relative_error hσ hσsmall hΘ hT0 hT he hε hεe hlam hsmallODE
    (fun t _ => hF t) (fun t _ => hG t) (fun t _ => hfluxF t) (fun t _ => hfluxG t)
    hF0 hF₁0 hG₁0 hRc hAc hCc hP hQ hN hU hV hRclose hAclose hCclose
    (fun t _ => hZ t) (fun t _ => hfluxZ t) hrayInitial hU0 hV0 hZ0 hZ₁0
  refine ⟨F, F₁, Z, Z₁, hF0, hF₁0, hZ0, hZ₁0, hF, hZ, hfluxF, hfluxZ, herror, ?_⟩
  intro t ht
  let δ := 160000000 * e * Θ ^ 29
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hrelSmall : 4 * exp 6 * δ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hpow29 (by positivity : 0 ≤ stabilityConstant * e)
    have hn : 0 ≤ stabilityConstant * e * Θ ^ 40 := by positivity
    dsimp [δ]
    unfold stabilityConstant at hm hn hsmall
    nlinarith only [hm, hn, hsmall]
  have herror' : |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t :=
    herror t ⟨by linarith [ht.1], ht.2⟩
  have hc := equation30_relative_state_consequences hσ hσsmall hlam ht.1 hδ hrelSmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 herror'
  refine ⟨hc.1, ?_, ?_⟩
  · dsimp [δ] at hc
    unfold stabilityConstant
    nlinarith only [hc.2.1]
  · dsimp [δ] at hc
    unfold stabilityConstant
    nlinarith only [hc.2.2]

/-- Early forward amplitudes are exponentially small relative to target
amplitude, with the initial slope cancelling from the estimate.  This is
the finite-ODE amplification mechanism underlying equation (36). -/
theorem early_forward_exponential_suppression
    {σ Θ T lam δ : ℝ} {F F₁ Z Z₁ U V : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (_hΘ : 1 ≤ Θ) (hT : T ≤ Θ)
    (hTtarget : 1 / σ ≤ T) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hδsmall : 4 * exp 6 * δ ≤ 1)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hZ : ∀ t, HasDerivAt Z (Z₁ t) t)
    (hfluxF : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * F₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * F t) t)
    (hfluxZ : ∀ t, HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
      (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (herror : ∀ t ∈ Icc 0 T, |V t - Z t| + |U t + Z₁ t| ≤ δ * (1 + lam) * F t) :
    0 < V T ∧ ∀ s ∈ Icc 0 1,
      (|U s| + |V s|) / V T ≤ 84 * exp 9 * Θ * exp (-(1 / (4 * σ))) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity : 0 < 1 / σ) hTtarget
  have hT1 : 1 ≤ T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh, hσ, hσsmall, hTpos]
  have hx : 1 ≤ σ * T := by
    have hh := (div_le_iff₀ hσ).mp hTtarget
    nlinarith only [hh]
  have hxpos : 0 < σ * T := by positivity
  have hF₁0pos : 0 ≤ F₁ 0 := by rw [hF₁0]
  have hZ₁0pos : 0 ≤ Z₁ 0 := by rw [hZ₁0]; exact hlam
  have hZpos := equation30_global_positive hσ hσsmall (fun t _ => hZ t)
    (fun t _ => hfluxZ t) hZ0 hZ₁0pos T hTpos.le
  have hc := equation30_relative_state_consequences hσ hσsmall hlam hT1 hδ hδsmall
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 (herror T ⟨hTpos.le, le_rfl⟩)
  have hVpos := hc.1
  have hVlower : Z T / 2 ≤ V T := by
    have hh := (abs_le.mp hc.2.1).1
    have hη : 2 * exp 6 * δ ≤ 1 / 2 := by nlinarith only [hδsmall]
    have hratio : (1 : ℝ) / 2 ≤ V T / Z T := by nlinarith only [hh, hη]
    have hm := (le_div_iff₀ hZpos).mp hratio
    nlinarith only [hm]
  have hZlower := equation30_slope_uniform_lower hσ hσsmall hlam
    (fun t _ => hF t) (fun t _ => hZ t) (fun t _ => hfluxF t) (fun t _ => hfluxZ t)
    hF0 hF₁0 hZ0 hZ₁0 T hT1
  have hgrowth := equation30_endpoint_exponential (sq_pos_of_pos hσ)
    (by nlinarith only [hσ, hσsmall] : σ ^ 2 ≤ 1 / 16)
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos
  rw [sqrt_sq hσ.le] at hgrowth
  have hpost := (equation30_post_inversion_lower hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0pos (σ * T) hx).1
  rw [mul_div_cancel_left₀ T hσne] at hpost
  have hFtarget : exp (1 / (4 * σ)) ≤ (σ * T) * F T := by
    have hh := (div_le_iff₀ hxpos).mp hpost
    nlinarith only [hgrowth, hh]
  have hexp6 : 0 < exp (6 : ℝ) := exp_pos _
  have hZscaled : (1 + lam) * F T ≤ 2 * exp 6 * Z T := by
    have hm := mul_le_mul_of_nonneg_left hZlower (by positivity : 0 ≤ 2 * exp (6 : ℝ))
    have hid : (2 * exp 6) * (((1 + lam) / (2 * exp 6)) * F T) = (1 + lam) * F T := by field_simp
    rw [hid] at hm
    nlinarith only [hm]
  have htarget : (1 + lam) * exp (1 / (4 * σ)) ≤ 4 * exp 6 * (σ * T) * V T := by
    have h₁ := mul_le_mul_of_nonneg_left hFtarget (by positivity : 0 ≤ 1 + lam)
    have h₂ := mul_le_mul_of_nonneg_left hZscaled hxpos.le
    have h₃ := mul_le_mul_of_nonneg_left hVlower (by positivity : 0 ≤ 4 * exp 6 * (σ * T))
    nlinarith only [h₁, h₂, h₃]
  refine ⟨hVpos, ?_⟩
  intro s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hT1⟩
  have hFpos := equation30_global_positive hσ hσsmall (fun t _ => hF t)
    (fun t _ => hfluxF t) hF0 hF₁0pos s hs.1
  have hFsmall := equation30_zero_slope_prefix_upper hσ hσsmall
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 s hs
  have hZstate := equation30_relative_propagator hσ hσsmall (by norm_num : (1 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hs.1 hs.2
    (fun t _ => hF t) (fun t _ => hfluxF t) hF0 hF₁0 (fun t _ => hZ t) (fun t _ => hfluxZ t)
  simp only [hF0, hZ0, hZ₁0, one_pow, div_one, abs_one, abs_of_nonneg hlam, mul_one] at hZstate
  have hδ1 : δ ≤ 1 := by
    have hh : (1 : ℝ) ≤ exp 6 := one_le_exp_iff.mpr (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hh hδ
    nlinarith only [hm, hδsmall]
  have hUtri := abs_add_le (U s + Z₁ s) (-Z₁ s)
  have hVtri := abs_add_le (V s - Z s) (Z s)
  rw [abs_neg] at hUtri
  have hUid : U s + Z₁ s + -Z₁ s = U s := by ring
  have hVid : V s - Z s + Z s = V s := by ring
  rw [hUid] at hUtri
  rw [hVid] at hVtri
  have hnorm : |U s| + |V s| ≤ 21 * exp 3 * (1 + lam) := by
    have herr := herror s hsT
    have hmδ := mul_le_mul_of_nonneg_right hδ1 (by positivity : 0 ≤ (1 + lam) * F s)
    have hmF := mul_le_mul_of_nonneg_right hFsmall (by positivity : 0 ≤ 21 * (1 + lam))
    nlinarith only [hUtri, hVtri, herr, hZstate, hmδ, hmF]
  have hscaled := mul_le_mul_of_nonneg_left htarget
    (by positivity : 0 ≤ 21 * exp 3 * exp (-(1 / (4 * σ))))
  have hexpCancel : exp (-(1 / (4 * σ))) * exp (1 / (4 * σ)) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  have hexp9 : exp (9 : ℝ) = exp 3 * exp 6 := by rw [← exp_add]; norm_num
  have hscaled' : 21 * exp 3 * (1 + lam) ≤ 84 * exp 9 * (σ * T) * exp (-(1 / (4 * σ))) * V T := by
    have hid : (21 * exp 3 * exp (-(1 / (4 * σ)))) * ((1 + lam) * exp (1 / (4 * σ))) =
        21 * exp 3 * (1 + lam) := by
      calc
        _ = (21 * exp 3 * (1 + lam)) * (exp (-(1 / (4 * σ))) * exp (1 / (4 * σ))) := by ring
        _ = _ := by rw [hexpCancel, mul_one]
    rw [hid] at hscaled
    rw [hexp9]
    nlinarith only [hscaled]
  have hxΘ : σ * T ≤ Θ := by
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hTpos.le
    nlinarith only [hm, hT]
  have hmΘ := mul_le_mul_of_nonneg_right hxΘ
    (by positivity : 0 ≤ 84 * exp 9 * exp (-(1 / (4 * σ))) * V T)
  apply (div_le_iff₀ hVpos).mpr
  nlinarith only [hnorm, hscaled', hmΘ]

end EulerPacketStage

end

section

open Set

namespace EulerPacketCoefficientControl

open Real EulerPacketGrowth EulerPacketPerturbation EulerPacketRay EulerPacketStage

/-- A derivative bound controls the change of a scalar coefficient on
the entire finite time interval. -/
theorem motion_displacement_bound
    {Θ L : ℝ} {f f₁ : ℝ → ℝ} (_hΘ : 0 ≤ Θ) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc 0 Θ, HasDerivAt f (f₁ t) t)
    (hb : ∀ t ∈ Icc 0 Θ, |f₁ t| ≤ L) :
    ∀ t ∈ Icc 0 Θ, |f t - f 0| ≤ L * Θ := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hf t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht))
  intro t ht
  have h := hh t ht
  simp only [Real.norm_eq_abs, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hL)

/-- A multiplicative differential bound keeps the normalized shear near
one.  Positivity or an a priori shear bound is not assumed. -/
theorem multiplicative_motion_bound
    {Θ k : ℝ} {H H₁ : ℝ → ℝ}
    (hΘ : 0 ≤ Θ) (hk : 0 ≤ k) (hsmall : k * Θ ≤ 1 / 2)
    (hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t)
    (hH0 : H 0 = 1) (hb : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H t|) :
    ∀ t ∈ Icc 0 Θ, |H t| ≤ 2 ∧ |H t - 1| ≤ 2 * k * Θ := by
  have hc : ContinuousOn H (Icc 0 Θ) := fun t ht => (hH t ht).continuousAt.continuousWithinAt
  obtain ⟨c, hci, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hΘ⟩⟩ hc.abs
  have hbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ k * |H c| := by
    intro t ht
    exact (hb t ht).trans (mul_le_mul_of_nonneg_left (hmax ht) hk)
  have hdiff := motion_displacement_bound hΘ (mul_nonneg hk (abs_nonneg _)) hH hbound
  have hcdiff := hdiff c hci
  rw [hH0] at hcdiff
  have htri := abs_add_le (H c - 1) 1
  norm_num at htri
  have hscaled := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (H c))
  have hM : |H c| ≤ 2 := by nlinarith only [hcdiff, htri, hscaled]
  intro t ht
  refine ⟨(hmax ht).trans hM, ?_⟩
  have hh := hdiff t ht
  rw [hH0] at hh
  have hm := mul_le_mul_of_nonneg_right hM (mul_nonneg hk hΘ)
  nlinarith only [hh, hm]

/-- Raw moving-frame coefficient motion implies the normalized error
bounds used in the ray and velocity reductions. -/
theorem normalized_motion_errors
    {a ε Θ G d β : ℝ} {B E : ℝ → Fin 3 → Fin 3 → ℝ}
    {h h₁ b₁ k₁ : ℝ → ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 < ε) (hΘ : 1 ≤ Θ) (hG : 1 ≤ G) (hd : 0 ≤ d)
    (hsmall : 16 * (ε * Θ * G ^ 2 + d) ≤ 1)
    (hB : ∀ t ∈ Icc 0 Θ, ∀ i j, |B t i j| ≤ G)
    (hE : ∀ t ∈ Icc 0 Θ, ∀ i j, |E t i j| ≤ d)
    (hb : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 0 1) (b₁ t) t)
    (hk : ∀ t ∈ Icc 0 Θ, HasDerivAt (fun s => B s 2 1) (k₁ t) t)
    (hbBound : ∀ t ∈ Icc 0 Θ, |b₁ t| ≤ 2 * ε * G ^ 2)
    (hkBound : ∀ t ∈ Icc 0 Θ, |k₁ t| ≤ 2 * ε * G ^ 2)
    (hShear : ∀ t ∈ Icc 0 Θ, HasDerivAt h (h₁ t) t)
    (hShearBound : ∀ t ∈ Icc 0 Θ, |h₁ t| ≤ (4 * ε * G) * |h t|)
    (hb0 : B 0 0 1 = a) (hk0 : B 0 2 1 = a * β) (hh0 : h 0 = a / ε ^ 2) :
    let e := 16 * (ε * Θ * G ^ 2 + d)
    ε ≤ e ∧ ∀ t ∈ Icc 0 Θ,
      (∀ i j, |ε * B t i j / a| ≤ e) ∧
      (∀ i j, |E t i j / a| ≤ e) ∧
      |ε ^ 2 * h t / a - 1| ≤ e ∧
      |B t 0 1 / a - 1| ≤ e ∧ |B t 2 1 / a - β| ≤ e := by
  let e := 16 * (ε * Θ * G ^ 2 + d)
  have haPos : 0 < a := by linarith
  have haNe : a ≠ 0 := ne_of_gt haPos
  have hεNe : ε ≠ 0 := ne_of_gt hε
  have hΘ0 : 0 ≤ Θ := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hG2 : G ≤ G ^ 2 := by nlinarith only [hG]
  have hΘG2 : G ^ 2 ≤ Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hΘ (sq_nonneg G)
    nlinarith only [hh]
  have hεG : ε * G ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hG2.trans hΘG2) hε.le
    nlinarith only [hh]
  have hεBase : ε ≤ ε * Θ * G ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hG hε.le
    nlinarith only [hh, hεG]
  have hbase0 : 0 ≤ ε * Θ * G ^ 2 := by positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hεe : ε ≤ e := by dsimp [e]; nlinarith only [hεBase, hd, hε]
  have hShearSmall : (4 * ε * G) * Θ ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    nlinarith only [hh, hsmall, hd]
  let H : ℝ → ℝ := fun t => ε ^ 2 * h t / a
  let H₁ : ℝ → ℝ := fun t => ε ^ 2 * h₁ t / a
  have hH : ∀ t ∈ Icc 0 Θ, HasDerivAt H (H₁ t) t := by
    intro t ht
    exact ((hShear t ht).const_mul (ε ^ 2)).div_const a
  have hH0 : H 0 = 1 := by dsimp [H]; rw [hh0]; field_simp
  have hHbound : ∀ t ∈ Icc 0 Θ, |H₁ t| ≤ (4 * ε * G) * |H t| := by
    intro t ht
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hShearBound t ht) (sq_nonneg ε)) haPos.le
    dsimp [H₁, H]
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos,
      abs_div, abs_mul, abs_of_nonneg (sq_nonneg ε), abs_of_pos haPos]
    convert! hm using 1
    ring
  have hHclose := multiplicative_motion_bound hΘ0 (by positivity : 0 ≤ 4 * ε * G)
    hShearSmall hH hH0 hHbound
  have hBclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hb hbBound
  have hKclose := motion_displacement_bound hΘ0 (by positivity : 0 ≤ 2 * ε * G ^ 2) hk hkBound
  refine ⟨hεe, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [abs_div, abs_mul, abs_of_pos hε, abs_of_pos haPos, div_le_iff₀ haPos]
    have hm := mul_le_mul_of_nonneg_left (hB t ht i j) hε.le
    have heA := mul_le_mul_of_nonneg_left ha he
    dsimp [e] at heA ⊢
    nlinarith only [hm, heA, hεG, hd, hbase0]
  · intro i j
    rw [abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hbb := hE t ht i j
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hbb, heA, hpos, hd]
  · have hh := (hHclose t ht).2
    have hm := mul_le_mul_of_nonneg_left hG2 (by positivity : 0 ≤ ε * Θ)
    dsimp [H, e] at hh ⊢
    nlinarith only [hh, hm, hd, hbase0]
  · have hh := hBclose t ht
    rw [hb0] at hh
    have hid : B t 0 1 / a - 1 = (B t 0 1 - a) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]
  · have hh := hKclose t ht
    rw [hk0] at hh
    have hid : B t 2 1 / a - β = (B t 2 1 - a * β) / a := by field_simp
    rw [hid, abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
    have heA := mul_le_mul_of_nonneg_left ha he
    have hpos : 0 ≤ ε * Θ * G ^ 2 := by positivity
    dsimp [e] at heA ⊢
    nlinarith only [hh, heA, hd, hpos]

/-- The exact raw moving-frame matrices satisfy the coefficient-error
hypotheses of the controlled-stage theorem. -/
theorem raw_frame_matrix_errors
    {a ε e β h : ℝ} {B E : Fin 3 → Fin 3 → ℝ}
    (ha : a ≠ 0) (hε : 0 < ε) (hεe : ε ≤ e) (he : 0 ≤ e) (heSmall : e ≤ 1)
    (hB : ∀ i j, |ε * B i j / a| ≤ e) (hE : ∀ i j, |E i j / a| ≤ e)
    (hH : |ε ^ 2 * h / a - 1| ≤ e) (hα : |B 0 1 / a - 1| ≤ e)
    (hκ : |B 2 1 / a - β| ≤ e) :
    (∀ i j, |scaledRayEntry a ε (parentEntry B E h) (frameSkew B) i j - idealRayEntry β i j| ≤ 4 * e) ∧
    (∀ i j, |scaledVelocityEntry a ε (parentEntry B E h) i j - idealVelocityEntry β i j| ≤ 3 * e) ∧
    (∀ j,
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 0 j -
        idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |scaledVelocityEntry a ε (fun i j => parentEntry B E h i j + frameSkew B i j) 1 j -
        idealUnprojectedEntry 1 j| ≤ 5 * e) := by
  have hεupper : ε ≤ 1 := hεe.trans heSmall
  refine ⟨scaled_ray_entry_error ha hε hεupper he hB hE hH hκ, ?_, ?_⟩
  · intro i j
    rw [scaled_velocity_entry_identity ha]
    exact normalized_velocity_entry_error hε.le hεupper he hB hE hH hα hκ i j
  · intro j
    have hids := scaled_unprojected_entry_identity (B := B) (E := E) (h := h) (ε := ε) ha j
    have hbound := normalized_unprojected_entry_error hε.le hεe he heSmall hB hE hH hα
    constructor
    · rw [hids.1]
      exact hbound 0 j
    · rw [hids.2]
      exact hbound 1 j

end EulerPacketCoefficientControl

end

section

open Set

namespace EulerPacketTargetCompression

open Real EulerPacketRay EulerPacketFrameRenewal EulerPacketFrameQuantitative

/-- The common `Θ^40` smallness regime guarantees every sign and
denominator condition used in the perturbed target compression estimate. -/
theorem target_compression_order40
    {β t Θ K e ε H P Q N : ℝ}
    (hβ : 0 < β) (hβupper : β ≤ 1) (ht : 0 < t) (htΘ : t ≤ Θ)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e) (hH : 0 ≤ H)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1) (hscale : 1 ≤ β * t ^ 2)
    (hP : |P - β * t ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * β * t| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    0 < rayDenominator ε P Q N ∧
      H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  let ρ := 800 * e * Θ ^ 5
  let M := K * e * Θ ^ 40
  have hΘpos : 0 < Θ := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; nlinarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hρsmall : ρ ≤ 1 / 2 := by
    have hh := hp 5 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hρΘ : ρ * Θ ≤ 1 := by
    have hh := hp 6 (by decide)
    dsimp [ρ]
    nlinarith only [hh, hMb]
  have hβtΘ : 1 ≤ β * t * Θ := by
    have hh := mul_le_mul_of_nonneg_left htΘ (mul_nonneg hβ.le ht.le)
    nlinarith only [hh, hscale]
  have hρQ : ρ ≤ β * t := by
    apply (mul_le_mul_iff_right₀ hΘpos).mp
    nlinarith only [hρΘ, hβtΘ]
  have hQ₀ : |-2 * β * t| ≤ 2 * Θ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos ht]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hh := mul_le_mul_of_nonneg_right hβupper ht.le
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    nlinarith only [hh, htΘ, hΘ2]
  have hQabs : |Q| ≤ 3 * Θ ^ 2 := by
    have hh := abs_add_le (Q + 2 * β * t) (-2 * β * t)
    have hid : Q + 2 * β * t + -2 * β * t = Q := by ring
    rw [hid] at hh
    have hΘ2 : 1 ≤ Θ ^ 2 := one_le_pow₀ hΘ
    change |Q + 2 * β * t| ≤ ρ at hQ
    nlinarith only [hh, hQ, hQ₀, hρsmall, hΘ2]
  have hεQ : |ε * Q| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hε]
    have hh := mul_le_mul hεe hQabs (abs_nonneg Q) he
    have hm := hp 2 (by decide)
    nlinarith only [hh, hm, hMb]
  have hPpos : 0 < P := by
    have hh := (abs_le.mp hP).1
    change ρ ≤ 1 / 2 at hρsmall
    dsimp [ρ] at hρsmall
    nlinarith only [hh, hρsmall, hscale]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  exact ⟨hDpos, perturbed_target_compression hβ ht hε hH hscale hρ hρsmall hρQ hP hQ hN hεQ⟩

/-- The full parent matrix has strictly negative target-ray compression
once its shear contribution dominates the older-gradient error. -/
theorem full_target_compression_negative
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G t : ℝ}
    (ht : 0 < t) (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G)
    (hShear : H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t))
    (hdominates : 30 * G * t < H * ε) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N < 0 := by
  have hfull := parent_ray_compression (H := H) hD hB
  have hdom : 3 * G < H * ε / (10 * t) := (lt_div_iff₀ (by positivity : 0 < 10 * t)).mpr
    (by nlinarith only [hdominates])
  rw [neg_div] at hShear
  nlinarith only [hfull, hShear, hdom]

end EulerPacketTargetCompression

end

section

/-!
Convergence estimates for the actual quadratic scale recurrence in (37).
The sequence is reindexed so that `x 0 = x_{J-1}` and
`x (n+1) = (J+n)^2 x n`; hence `J+n` is the stage index in the source.
-/

namespace EulerScale

open Filter
open scoped Topology

/-- Positivity propagates through the scale recurrence from any positive initial scale. -/
theorem quadratic_growth_pos (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 0 < x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
      positivity

/-- The reciprocal of the stage index tends to zero. -/
theorem stage_inv_tendsto_zero (J : ℕ) :
    Tendsto (fun n : ℕ => (((J + n : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using
    ((tendsto_add_atTop_iff_nat J).2
      (tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0)))

/-- Every fixed polynomial in the stage index divided by the scale is summable. -/
theorem polynomial_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  have hlim : Tendsto
      (fun n : ℕ => (1 + (((J + n : ℕ) : ℝ))⁻¹) ^ A *
        ((((J + n : ℕ) : ℝ))⁻¹) ^ 2) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (stage_inv_tendsto_zero J)).pow A).mul
      ((stage_inv_tendsto_zero J).pow 2)
    simpa using h
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Eventually.of_forall fun n => ne_of_gt (div_pos (pow_pos (hjp n) _) (hxp n))
  · apply hlim.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp (n + 1)).le _) (hxp (n + 1)).le),
      Real.norm_of_nonneg (div_nonneg (pow_nonneg (hjp n).le _) (hxp n).le), hx]
    have hj : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hj]
    have hi : 1 + (((J + n : ℕ) : ℝ))⁻¹ =
        (((J + n : ℕ) : ℝ) + 1) / ((J + n : ℕ) : ℝ) := by
      field_simp [ne_of_gt (hjp n)]
    rw [hi, div_pow]
    field_simp [ne_of_gt (hjp n), ne_of_gt (hxp n)]

/-- A simple exponential majorization requiring no numerical approximations. -/
theorem exp_neg_le_reciprocal (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ 1 / t := by
  have he : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le ht he

/-- Every exponential decay in a scale divided by a fixed natural power is summable. -/
theorem exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) (b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx A).mul_left (1 / b)
  apply hs.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have ht : 0 < b * (x n / ((J + n : ℕ) : ℝ) ^ A) :=
    mul_pos hb (div_pos (hxp n) (pow_pos hj _))
  calc
    _ = Real.exp (-(b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by congr 1; ring
    _ ≤ 1 / (b * (x n / ((J + n : ℕ) : ℝ) ^ A)) := exp_neg_le_reciprocal _ ht
    _ = (1 / b) * (((J + n : ℕ) : ℝ) ^ A / x n) := by field_simp

/-- The same decay conclusion holds for every real power, including `7/2`. -/
theorem exponential_decay_real_power_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  apply (exponential_decay_summable J hJ x hx0 hx N b hb).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj
  have hpow : ((J + n : ℕ) : ℝ) ^ A ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hj hN.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (div_le_div_of_nonneg_left (hxp n).le (Real.rpow_pos_of_pos hjp A) hpow) (by linarith)

/-- The logarithm of the rapidly growing scale still has a quadratic polynomial bound. -/
theorem abs_log_growth_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, |Real.log (x n)| ≤ (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  intro n
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hJ2 : (1 : ℝ) ≤ (J : ℝ) ^ 2 := one_le_pow₀ hJr
      calc
        _ ≤ |Real.log (x 0)| + 2 := by linarith
        _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hJ2 (by positivity : 0 ≤ |Real.log (x 0)| + 2)
  | succ n ih =>
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj1
      have hlog : 0 ≤ Real.log ((J + n : ℕ) : ℝ) := Real.log_nonneg hj1
      have hlogle : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
        (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
      have hjnext : (((J + (n + 1) : ℕ) : ℝ)) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hx, Real.log_mul (pow_ne_zero _ hjp.ne') (hxp n).ne', Real.log_pow]
      calc
        _ ≤ |(2 : ℝ) * Real.log ((J + n : ℕ) : ℝ)| + |Real.log (x n)| := abs_add_le _ _
        _ = 2 * Real.log ((J + n : ℕ) : ℝ) + |Real.log (x n)| := by rw [abs_of_nonneg (by positivity)]
        _ ≤ 2 * ((J + n : ℕ) : ℝ) +
            (|Real.log (x 0)| + 2) * ((J + n : ℕ) : ℝ) ^ 2 := by linarith
        _ ≤ _ := by
          rw [hjnext]
          nlinarith [abs_nonneg (Real.log (x 0)),
            mul_nonneg (abs_nonneg (Real.log (x 0))) hjp.le]

/-- Every polynomial weight times `|log x|/x` is summable. -/
theorem polynomial_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) : Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * |Real.log (x n)| / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hs := (polynomial_over_growth_summable J hJ x hx0 hx (A + 2)).mul_left
    (|Real.log (x 0)| + 2)
  apply hs.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (hxp n).le)
  intro n
  have h := mul_le_mul_of_nonneg_left (abs_log_growth_le J hJ x hx0 hx n)
    (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)
  have hd := div_le_div_of_nonneg_right h (hxp n).le
  simpa only [pow_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd

/-- The logarithmic term on the right side of (39) tends to zero with every fixed polynomial weight. -/
theorem polynomial_log_over_growth_tendsto_zero (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) :
    Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * Real.log (x n) / x n) atTop (𝓝 0) := by
  have hs := polynomial_log_over_growth_summable J hJ x hx0 hx A
  have hn : Tendsto (fun n => -(((J + n : ℕ) : ℝ) ^ A * |Real.log (x n)| / x n))
      atTop (𝓝 0) := by simpa using hs.tendsto_atTop_zero.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hn hs.tendsto_atTop_zero
  · intro n
    have hxp := quadratic_growth_pos J hJ x hx0 hx n
    have h := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (x n)))
      (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)
    simpa only [mul_neg, neg_div] using div_le_div_of_nonneg_right h hxp.le
  · intro n
    have hxp := quadratic_growth_pos J hJ x hx0 hx n
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self (Real.log (x n))) (by positivity)) hxp.le

/-- The logarithm of the stage index is also harmless in every polynomially weighted scale sum. -/
theorem polynomial_stage_log_over_growth_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A : ℕ) :
    Summable (fun n => ((J + n : ℕ) : ℝ) ^ A * Real.log ((J + n : ℕ) : ℝ) / x n) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : ∀ n, (1 : ℝ) ≤ (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 1 ≤ J + n by omega)
  apply (polynomial_over_growth_summable J hJ x hx0 hx (A + 1)).of_nonneg_of_le
  · intro n
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (hj1 n))) (hxp n).le
  · intro n
    have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one (hj1 n)
    have hl : Real.log ((J + n : ℕ) : ℝ) ≤ (J + n : ℕ) :=
      (Real.log_le_sub_one_of_pos hjp).trans (by linarith)
    simpa only [pow_succ] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (show 0 ≤ ((J + n : ℕ) : ℝ) ^ A by positivity)) (hxp n).le

/-- A power at least three in the denominator dominates the square from `1/log k_j`. -/
theorem stage_sq_div_real_power_tendsto_zero (J : ℕ) (hJ : 1 ≤ J)
    (A : ℝ) (hA : 3 ≤ A) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ 2 / ((J + n : ℕ) : ℝ) ^ A)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (stage_inv_tendsto_zero J)
  · intro n
    positivity
  · intro n
    have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hjp : (0 : ℝ) < (J + n : ℕ) := lt_of_lt_of_le zero_lt_one hj1
    have hp : ((J + n : ℕ) : ℝ) ^ 3 ≤ ((J + n : ℕ) : ℝ) ^ A := by
      simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hj1 hA
    calc
      _ ≤ ((J + n : ℕ) : ℝ) ^ 2 / ((J + n : ℕ) : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hjp _) hp
      _ = _ := by field_simp

/-- The previous-stage frequency and shear terms have vanishing relative logarithms. -/
theorem stage_sq_div_predecessor_power_tendsto_zero (J : ℕ) (hJ : 2 ≤ J)
    (A : ℕ) (hA : 3 ≤ A) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ 2 / ((J - 1 + n : ℕ) : ℝ) ^ A)
      atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun n : ℕ => (1 + (((J - 1 + n : ℕ) : ℝ))⁻¹) ^ 2 *
        ((((J - 1 + n : ℕ) : ℝ))⁻¹) ^ (A - 2)) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add
      (stage_inv_tendsto_zero (J - 1))).pow 2).mul
      ((stage_inv_tendsto_zero (J - 1)).pow (A - 2))
    simpa only [add_zero, one_pow, zero_pow (show A - 2 ≠ 0 by omega), mul_zero] using h
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by exact_mod_cast (show 0 < J - 1 + n by omega)
  have hj : (((J + n : ℕ) : ℝ)) = ((J - 1 + n : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show J + n = (J - 1 + n) + 1 by omega)
  have hi : 1 + (((J - 1 + n : ℕ) : ℝ))⁻¹ =
      (((J - 1 + n : ℕ) : ℝ) + 1) / ((J - 1 + n : ℕ) : ℝ) := by field_simp
  have hpow : ((J - 1 + n : ℕ) : ℝ) ^ A =
      ((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 1 + n : ℕ) : ℝ) ^ (A - 2) := by
    rw [← pow_add, show 2 + (A - 2) = A by omega]
  rw [hj, hi, hpow, div_pow]
  field_simp [hp.ne']
  simp only [one_div, ← mul_pow, inv_mul_cancel₀ hp.ne', one_pow]

/-- A finite sum of positive exponential scales has an explicit logarithmic upper bound. -/
theorem log_sum_exp_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    0 ≤ Real.log (∑ i, Real.exp (a i)) ∧
      Real.log (∑ i, Real.exp (a i)) ≤ Real.log (Fintype.card ι : ℝ) + ∑ i, a i := by
  classical
  have hpos : 0 < ∑ i, Real.exp (a i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hone : 1 ≤ ∑ i, Real.exp (a i) :=
    (Real.one_le_exp (ha (Classical.arbitrary ι))).trans
      (Finset.single_le_sum (fun i _ => (Real.exp_pos (a i)).le) (Finset.mem_univ _))
  constructor
  · exact Real.log_nonneg hone
  · have hs : (∑ i, Real.exp (a i)) ≤ (Fintype.card ι : ℝ) * Real.exp (∑ i, a i) := by
      calc
        _ ≤ ∑ _i : ι, Real.exp (∑ i, a i) := by
          apply Finset.sum_le_sum
          intro i _hi
          exact Real.exp_monotone (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
        _ = _ := by simp
    calc
      _ ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (∑ i, a i)) := Real.log_le_log hpos hs
      _ = _ := by rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp]

/-- Finite aggregation preserves a logarithmic scale separation proved for each explicit term. -/
theorem log_sum_exp_mul_tendsto_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ → ℝ) (r : ℕ → ℝ) (ha : ∀ i n, 0 ≤ a i n) (hr : ∀ n, 0 ≤ r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (halim : ∀ i, Tendsto (fun n => a i n * r n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (∑ i, Real.exp (a i n)) * r n) atTop (𝓝 0) := by
  classical
  have hs : Tendsto (fun n => ∑ i, a i n * r n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => halim i)
  have hu : Tendsto (fun n => (Real.log (Fintype.card ι : ℝ) + ∑ i, a i n) * r n)
      atTop (𝓝 0) := by
    have h := (hrlim.const_mul (Real.log (Fintype.card ι : ℝ))).add hs
    simpa only [mul_zero, add_zero, add_mul, Finset.sum_mul] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact mul_nonneg (log_sum_exp_bounds (fun i => a i n) (fun i => ha i n)).1 (hr n)
  · intro n
    exact mul_le_mul_of_nonneg_right (log_sum_exp_bounds (fun i => a i n) (fun i => ha i n)).2 (hr n)

/-- A starting scale at least one stays at least one. -/
theorem quadratic_growth_one_le (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 1 ≤ x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, 1 ≤ x n := by
  intro n
  induction n with
  | zero => exact hx0
  | succ n ih =>
      rw [hx]
      have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) ih

/--
The logarithms of the eight terms in the source's aggregate parameter: the fixed
base constant; the previous frequency power; inverse support and spike scales;
the present and previous shears; and the present and previous geometric sizes.
-/
noncomputable def sourceParameterExponent (J : ℕ) (Cbase Cstar : ℝ) (x : ℕ → ℝ) (i : Fin 8) (n : ℕ) : ℝ :=
  ![Real.log Cbase,
    Cstar * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4,
    x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ),
    x n / ((J + n : ℕ) : ℝ) ^ 3,
    x n / ((J + n : ℕ) : ℝ) ^ 5,
    x n / ((J - 1 + n : ℕ) : ℝ) ^ 7,
    Real.log (((J + n : ℕ) : ℝ) ^ 2 * x n),
    Real.log (x n)] i

/-- The sum of precisely those eight positive parameter terms. -/
noncomputable def sourceParameterAggregate (J : ℕ) (Cbase Cstar : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 8, Real.exp (sourceParameterExponent J Cbase Cstar x i n)

theorem sourceParameterExponent_nonneg (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ i n, 0 ≤ sourceParameterExponent J Cbase Cstar x i n := by
  intro i n
  have hxn : 1 ≤ x n := quadratic_growth_one_le J (by omega) x hx0 hx n
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hprod : 1 ≤ ((J + n : ℕ) : ℝ) ^ 2 * x n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) hxn
  fin_cases i
  · simpa [sourceParameterExponent] using Real.log_nonneg hCbase
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simp [sourceParameterExponent]
    positivity
  · simpa [sourceParameterExponent] using Real.log_nonneg hprod
  · simpa [sourceParameterExponent] using Real.log_nonneg hxn

/-- Every explicitly defined parameter term is negligible on the logarithmic frequency scale. -/
theorem sourceParameterExponent_relative_tendsto_zero (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ i, Tendsto (fun n => sourceParameterExponent J Cbase Cstar x i n *
      (((J + n : ℕ) : ℝ) ^ 2 / x n)) atTop (𝓝 0) := by
  intro i
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x hx0 hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  have hlx := polynomial_log_over_growth_tendsto_zero J hJ1 x hx0 hx 2
  fin_cases i
  · simpa [sourceParameterExponent] using
      ((polynomial_over_growth_summable J hJ1 x hx0 hx 2).tendsto_atTop_zero.const_mul (Real.log Cbase))
  · have h := (stage_sq_div_predecessor_power_tendsto_zero J hJ 4 (by omega)).const_mul Cstar
    simp only [mul_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 (7 / 2) (by norm_num)
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 3 (by norm_num)
    simp only [Real.rpow_ofNat] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_real_power_tendsto_zero J hJ1 5 (by norm_num)
    simp only [Real.rpow_ofNat] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := stage_sq_div_predecessor_power_tendsto_zero J hJ 7 (by omega)
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    field_simp [(hxp n).ne']
  · have h := ((polynomial_stage_log_over_growth_summable J hJ1 x hx0 hx 2).tendsto_atTop_zero.const_mul 2).add hlx
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    have hjp' : (0 : ℝ) < (J : ℝ) + n := by simpa using hjp n
    rw [Real.log_mul (pow_ne_zero _ hjp'.ne') (hxp n).ne', Real.log_pow]
    push_cast
    ring
  · apply hlx.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    simp [sourceParameterExponent]
    ring

/-- Expansion of the aggregate into the scales listed immediately before (39). -/
theorem sourceParameterAggregate_eq (J : ℕ) (hJ : 1 ≤ J) (Cbase Cstar : ℝ)
    (hCbase : 0 < Cbase) (x : ℕ → ℝ) (hxp : ∀ n, 0 < x n) (n : ℕ) :
    sourceParameterAggregate J Cbase Cstar x n = Cbase +
      Real.exp (Cstar * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ 3) +
      Real.exp (x n / ((J + n : ℕ) : ℝ) ^ 5) +
      Real.exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) +
      ((J + n : ℕ) : ℝ) ^ 2 * x n + x n := by
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have hprod : 0 < ((J + n : ℕ) : ℝ) ^ 2 * x n := mul_pos (pow_pos hj _) (hxp n)
  have hprod' : 0 < ((J : ℝ) + n) ^ 2 * x n := by simpa using hprod
  simp [sourceParameterAggregate, sourceParameterExponent, Fin.sum_univ_succ,
    Real.exp_log hCbase, Real.exp_log (hxp n), Real.exp_log hprod']
  ring

/--
The full logarithmic separation in (39), for the explicit aggregate of all eight
scales. Its hypotheses contain only the scale recurrence and fixed positivity
conditions; the logarithmic separation is a conclusion.
-/
theorem source_parameters_separated (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Tendsto (fun n => Real.log (sourceParameterAggregate J Cbase Cstar x n) /
      (x n / ((J + n : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hJ1 : 1 ≤ J := by omega
  have hx0p : 0 < x 0 := lt_of_lt_of_le zero_lt_one hx0
  have hxp := quadratic_growth_pos J hJ1 x hx0p hx
  have hlim := log_sum_exp_mul_tendsto_zero
    (sourceParameterExponent J Cbase Cstar x)
    (fun n => ((J + n : ℕ) : ℝ) ^ 2 / x n)
    (sourceParameterExponent_nonneg J hJ Cbase Cstar hCbase hCstar x hx0 hx)
    (fun n => div_nonneg (sq_nonneg _) (hxp n).le)
    (polynomial_over_growth_summable J hJ1 x hx0p hx 2).tendsto_atTop_zero
    (sourceParameterExponent_relative_tendsto_zero J hJ Cbase Cstar x hx0p hx)
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [sourceParameterAggregate]
  field_simp

/-- Exponential scale decay remains summable after a quantitatively vanishing relative error. -/
theorem perturbed_exponential_decay_summable (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ)
    (hx0 : 0 < x 0) (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b : ℝ) (hb : 0 < b) (e : ℕ → ℝ)
    (he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0)) :
    Summable (fun n => Real.exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) + e n)) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hb2 : 0 < b / 2 := by linarith
  apply (exponential_decay_real_power_summable J hJ x hx0 hx A (b / 2) hb2).of_norm_bounded_eventually_nat
  filter_upwards [he.eventually_le_const hb2] with n hn
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  have hy : 0 < x n / ((J + n : ℕ) : ℝ) ^ A := div_pos (hxp n) (Real.rpow_pos_of_pos hj A)
  have herror := (div_le_iff₀ hy).mp hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  linarith

/--
Both initial-increment exponential bounds after (22) are summable. In particular,
the mean estimate needs no extra power of the oscillation frequency.
-/
theorem initial_increment_majorants_summable (J : ℕ) (hJ : 2 ≤ J)
    (Cbase Cstar : ℝ) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (m C b : ℝ) (hb : 0 < b) :
    Summable (fun n => Real.exp (-b * x n +
      m * (x n / ((J + n : ℕ) : ℝ) ^ 2) +
      m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      C * Real.log (sourceParameterAggregate J Cbase Cstar x n))) ∧
    Summable (fun n => Real.exp (-2 * (x n / ((J + n : ℕ) : ℝ) ^ 2) +
      m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
      C * Real.log (sourceParameterAggregate J Cbase Cstar x n))) := by
  have hJ1 : 1 ≤ J := by omega
  have hx0p : 0 < x 0 := lt_of_lt_of_le zero_lt_one hx0
  have hxp := quadratic_growth_pos J hJ1 x hx0p hx
  have hjp : ∀ n, (0 : ℝ) < (J + n : ℕ) := by
    intro n
    exact_mod_cast (show 0 < J + n by omega)
  let e : ℕ → ℝ := fun n => m * (x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
    C * Real.log (sourceParameterAggregate J Cbase Cstar x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := ((stage_sq_div_real_power_tendsto_zero J hJ1 (7 / 2) (by norm_num)).const_mul m).add
      ((source_parameters_separated J hJ Cbase Cstar hCbase hCstar x hx0 hx).const_mul C)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only [e]
    field_simp [(hxp n).ne', (hjp n).ne', (Real.rpow_pos_of_pos (hjp n) (7 / 2)).ne']
  have hmean : Summable (fun n => Real.exp (-2 * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n)) := by
    have h := perturbed_exponential_decay_summable J hJ1 x hx0p hx 2 2 (by norm_num) e
      (by simpa only [Real.rpow_ofNat] using he)
    simpa only [Real.rpow_ofNat] using h
  have hehigh : Tendsto
      (fun n => (m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n) / x n) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := m)).add he).mul ((stage_inv_tendsto_zero J).pow 2)
    simp only [add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    dsimp only
    field_simp [(hxp n).ne', (hjp n).ne']
  have hhigh : Summable (fun n => Real.exp (-b * x n +
      (m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n))) := by
    have h := perturbed_exponential_decay_summable J hJ1 x hx0p hx 0 b hb
      (fun n => m * (x n / ((J + n : ℕ) : ℝ) ^ 2) + e n)
      (by simpa only [Real.rpow_zero, div_one] using hehigh)
    simpa only [Real.rpow_zero, div_one] using h
  constructor
  · simpa only [e, add_assoc] using hhigh
  · simpa only [e, add_assoc] using hmean

end EulerScale

end

section

open Set Filter
open scoped Topology

namespace EulerPacketScaleGeometry

open Real EulerScale

/-- The activation-time interval in (38) follows from the two frame
invariants in (24), with the numerical constants stated in the source. -/
theorem activation_time_bounds
    {a β H x X : ℝ} (ha : 1 / 2 ≤ a) (ha₂ : a ≤ 2)
    (hH : 0 < H) (hx : 0 < x) (hX : 0 ≤ X)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    (3 * X * x / sqrt H) / 6 ≤ X / sqrt (β * a * H) ∧
      X / sqrt (β * a * H) ≤ 2 * (3 * X * x / sqrt H) / 3 := by
  have ha₀ : 0 < a := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hroot : 0 < sqrt (β * a * H) := sqrt_pos.2 (by positivity)
  have hrootH : 0 < sqrt H := sqrt_pos.2 hH
  have hs := sq_sqrt (show 0 ≤ β * a * H by positivity)
  have hsH := sq_sqrt hH.le
  have hprodLow : 1 / 4 ≤ β * x ^ 2 * a := by
    have hh := mul_le_mul hβx ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by positivity : 0 ≤ β * x ^ 2)
    nlinarith only [hh]
  have hprodUp : β * x ^ 2 * a ≤ 4 := by
    have hh := mul_le_mul hβx₂ ha₂ ha₀.le (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have hlo : sqrt H ≤ 2 * x * sqrt (β * a * H) := by
    have hh := mul_le_mul_of_nonneg_right hprodLow hH.le
    have hhroot : 0 ≤ 2 * x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  have hup : x * sqrt (β * a * H) ≤ 2 * sqrt H := by
    have hh := mul_le_mul_of_nonneg_right hprodUp hH.le
    have hhroot : 0 ≤ x * sqrt (β * a * H) := by positivity
    nlinarith only [hh, hs, hsH, hhroot, hrootH]
  constructor
  · have hid : 3 * X * x / sqrt H / 6 = X * x / (2 * sqrt H) := by ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity) hroot).2
    have hh := mul_le_mul_of_nonneg_left hup hX
    nlinarith only [hh]
  · have hid : 2 * (3 * X * x / sqrt H) / 3 = 2 * X * x / sqrt H := by ring
    rw [hid]
    apply (div_le_div_iff₀ hroot hrootH).2
    have hh := mul_le_mul_of_nonneg_left hlo hX
    nlinarith only [hh]

/-- A sufficiently small next time width makes the packet horizons nest. -/
theorem nested_horizon_of_width_ratio
    {t Δ W Wnext : ℝ} (hW : 0 ≤ W)
    (hΔ : Δ ≤ 2 * W / 3) (hnext : Wnext ≤ W / 2) :
    t + Δ + 2 * Wnext ≤ t + 2 * W := by linarith

/-- Powers of a shifted stage index divided by a larger predecessor
power vanish, a basic consequence of the quadratic recurrence geometry. -/
theorem stage_power_div_predecessor_power_tendsto_zero
    (J : ℕ) (hJ : 2 ≤ J) (A B : ℕ) (hAB : A < B) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ A /
      ((J - 1 + n : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add
    (stage_inv_tendsto_zero (J - 1))).pow A).mul
    ((stage_inv_tendsto_zero (J - 1)).pow (B - A))
  simp only [add_zero, one_pow, zero_pow (show B - A ≠ 0 by omega), mul_zero] at hlim
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by
    exact_mod_cast (show 0 < J - 1 + n by omega)
  have hj : (((J + n : ℕ) : ℝ)) = ((J - 1 + n : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show J + n = (J - 1 + n) + 1 by omega)
  have hi : 1 + (((J - 1 + n : ℕ) : ℝ))⁻¹ =
      (((J - 1 + n : ℕ) : ℝ) + 1) / ((J - 1 + n : ℕ) : ℝ) := by field_simp
  have hpw : ((J - 1 + n : ℕ) : ℝ) ^ B =
      ((J - 1 + n : ℕ) : ℝ) ^ A * ((J - 1 + n : ℕ) : ℝ) ^ (B - A) := by
    rw [← pow_add, show A + (B - A) = B by omega]
  dsimp only
  rw [hj, hi, hpw, div_pow]
  field_simp [hp.ne']
  simp only [one_div, ← mul_pow, inv_mul_cancel₀ hp.ne', one_pow]

/-- Exponential decay on any polynomially rescaled quadratic scale
absorbs every fixed polynomial in the scale and the stage index. -/
theorem polynomial_exponential_decay_summable
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A p q : ℕ) (C b : ℝ) (hC : 0 < C) (hb : 0 < b) :
    Summable (fun n => C * ((J + n : ℕ) : ℝ) ^ p * (x n) ^ q *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  let e : ℕ → ℝ := fun n => log C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
    have h := (((polynomial_over_growth_summable J hJ x hx0 hx A).tendsto_atTop_zero.const_mul
      (log C)).add ((polynomial_stage_log_over_growth_summable J hJ x hx0 hx A).tendsto_atTop_zero.const_mul (p : ℝ))).add
      ((polynomial_log_over_growth_tendsto_zero J hJ x hx0 hx A).const_mul (q : ℝ))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    apply Eventually.of_forall
    intro n
    have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
    dsimp [e]
    field_simp [(hxp n).ne', hj.ne']
  have hh := perturbed_exponential_decay_summable J hJ x hx0 hx A b hb e
    (by simpa only [rpow_natCast] using he)
  apply hh.congr
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  simp only [rpow_natCast, e, exp_add, exp_log hC, exp_nat_mul,
    exp_log hj, exp_log (hxp n)]
  ring

/-- The ratio of a stage to any fixed predecessor tends to one. -/
theorem stage_div_shifted_tendsto_one (J d : ℕ) (hJ : d < J) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) /
      ((J - d + n : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := (stage_inv_tendsto_zero (J - d)).const_mul (d : ℝ)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add h
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  have hj : ((J + n : ℕ) : ℝ) = ((J - d + n : ℕ) : ℝ) + d := by
    exact_mod_cast (show J + n = (J - d + n) + d by omega)
  dsimp only
  rw [hj]
  field_simp

/-- A real power below a predecessor's natural power has vanishing
ratio; this includes the source's support exponent `7/2`. -/
theorem stage_rpow_div_shifted_power_tendsto_zero
    (J d B : ℕ) (hJ : d < J) (A : ℝ) (hAB : A < B) :
    Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ) ^ A /
      ((J - d + n : ℕ) : ℝ) ^ B) atTop (𝓝 0) := by
  have hjtop : Tendsto (fun n : ℕ => ((J + n : ℕ) : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm] using tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat J)
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hAB)).comp hjtop
  have hh := ((stage_div_shifted_tendsto_one J d hJ).pow B).mul hp
  simp only [one_pow, mul_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hprev : (0 : ℝ) < (J - d + n : ℕ) := by
    exact_mod_cast (show 0 < J - d + n by omega)
  dsimp only [Function.comp_def]
  rw [neg_sub, rpow_sub hj, rpow_natCast, div_pow]
  field_simp

/-- Polynomial logarithms are negligible relative to `x/j^A`, for every
nonnegative real exponent `A`. -/
theorem polynomial_log_relative_tendsto_zero
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A C p q : ℝ) (_hA : 0 ≤ A) :
    Tendsto (fun n => (C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)) /
      (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt A
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hjp (n : ℕ) : (0 : ℝ) < (J + n : ℕ) := by
    exact_mod_cast (show 0 < J + n by omega)
  have hpoly : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A / x n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (polynomial_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    · intro n
      exact div_nonneg (rpow_nonneg (hjp n).le A) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogx : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log (x n) / x n) atTop (𝓝 0) := by
    have hb := (polynomial_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply squeeze_zero_norm' _ hb
    apply Eventually.of_forall
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (rpow_nonneg (hjp n).le A),
      abs_of_pos (hxp n)]
    apply div_le_div_of_nonneg_right _ (hxp n).le
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hlogj : Tendsto (fun n => ((J + n : ℕ) : ℝ) ^ A * log ((J + n : ℕ) : ℝ) / x n)
      atTop (𝓝 0) := by
    have hb := (polynomial_stage_log_over_growth_summable J hJ x hx0 hx N).tendsto_atTop_zero
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    · intro n
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      exact div_nonneg (mul_nonneg (rpow_nonneg (hjp n).le A) (log_nonneg hj1)) (hxp n).le
    · intro n
      apply div_le_div_of_nonneg_right _ (hxp n).le
      have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
      apply mul_le_mul_of_nonneg_right _ (log_nonneg hj1)
      simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 hN.le
  have hh := ((hpoly.const_mul C).add (hlogj.const_mul p)).add (hlogx.const_mul q)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only
  field_simp [(hxp n).ne', (rpow_pos_of_pos (hjp n) A).ne']

/-- Explicit positive logarithmic errors from older stages are absorbed
by the source's negative exponential scale. No smallness guard is assumed. -/
theorem source_scale_exponential_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C p q : ℝ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) :
    Summable (fun n => exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) := by
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x hx0 hx
  let e : ℕ → ℝ := fun n => c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
    C + p * log ((J + n : ℕ) : ℝ) + q * log (x n)
  have he : Tendsto (fun n => e n / (x n / ((J + n : ℕ) : ℝ) ^ A)) atTop (𝓝 0) := by
    have hh := ((stage_rpow_div_shifted_power_tendsto_zero J d B hJ A hAB).const_mul c).add
      (polynomial_log_relative_tendsto_zero J hJ1 x hx0 hx A C p q hA)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
    have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
    dsimp only [e]
    field_simp [(hxp n).ne', (rpow_pos_of_pos hj A).ne', hp.ne']
    ring
  have hh := perturbed_exponential_decay_summable J hJ1 x hx0 hx A b hb e he
  simpa only [e, add_assoc] using hh

end EulerPacketScaleGeometry

end

section

open Filter
open scoped Topology

namespace EulerPacketSourceScales

open Real EulerScale EulerPacketScaleGeometry

/-- A fixed polynomial majorant for the dimensionless stage horizon. -/
noncomputable def sourceTheta (J : ℕ) (C : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * (1 + ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)

/-- The source upper bound for the square-root inverse parent shear. -/
noncomputable def sourceEpsilon (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  2 * exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The older gradient bound expressed using the quadratic recurrence. -/
noncomputable def sourceOlderGradient (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 + exp (x n / (((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7))

/-- The inverse fourth root of the preceding packet frequency. -/
noncomputable def sourcePriorError (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / (4 * ((J - 1 + n : ℕ) : ℝ) ^ 4))

/-- The neighbor error with the support, frequency, and shear scales of (37). -/
noncomputable def sourceNeighborError (J : ℕ) (c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  exp (-x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ) +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 4 +
    c * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)

/-- The full coefficient error entering the normalized ray and velocity equations. -/
noncomputable def sourceCoefficientError (J : ℕ) (C c : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  16 * (sourceEpsilon J x n * sourceTheta J C x n * sourceOlderGradient J x n ^ 2 +
    sourcePriorError J x n + sourceNeighborError J c x n)

/-- The horizon majorant is bounded by a single monomial. -/
theorem sourceTheta_bounds {J : ℕ} (hJ : 1 ≤ J) {C : ℝ} (hC : 1 ≤ C)
    {x : ℕ → ℝ} (hx : ∀ n, 1 ≤ x n) (n : ℕ) :
    1 ≤ sourceTheta J C x n ∧
      sourceTheta J C x n ≤ 2 * C * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hjx : 1 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj) (one_le_pow₀ (hx n))
  unfold sourceTheta
  have hC₀ : 0 ≤ C := by linarith
  constructor
  · nlinarith only [hC, hjx, mul_nonneg hC₀ (by nlinarith only [hjx] :
      0 ≤ ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2)]
  · have hh := mul_le_mul_of_nonneg_left hjx hC₀
    nlinarith only [hh]

/-- The explicit logarithmic scale comparison also allows an arbitrary
fixed polynomial prefactor. -/
theorem polynomial_source_scale_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (A b c C : ℝ) (p q : ℕ) (hA : 0 ≤ A) (hAB : A < B) (hb : 0 < b) (hC : 0 < C) :
    Summable (fun n => C * ((J + n : ℕ) : ℝ) ^ p * (x n) ^ q *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A) +
        c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))) := by
  have hh := source_scale_exponential_summable J d B hJ x hx0 hx A b c (log C) p q hA hAB hb
  have hxp := quadratic_growth_pos J (by omega) x hx0 hx
  apply hh.congr
  intro n
  have hj : (0 : ℝ) < (J + n : ℕ) := by exact_mod_cast (show 0 < J + n by omega)
  simp only [exp_add, exp_log hC, exp_nat_mul, exp_log hj, exp_log (hxp n)]
  ring

/-- Every polynomially weighted neighbor error in (25) is summable. -/
theorem source_neighbor_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    Summable (fun n => sourceNeighborError J c x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hxp := quadratic_growth_pos J hJ1 x (by linarith) hx
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hC₀ : 0 < C := by linarith
  have hsum := polynomial_source_scale_summable J 1 4 (by omega) x (by linarith) hx
    (7 / 2) 1 (2 * c) ((2 * C) ^ A) (2 * A) (2 * A)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (exp_pos _).le (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A)
  · intro n
    have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hp : (1 : ℝ) ≤ (J - 1 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 1 + n by omega)
    have hp4 : ((J - 1 + n : ℕ) : ℝ) ^ 4 ≤ ((J - 1 + n : ℕ) : ℝ) ^ 7 :=
      pow_le_pow_right₀ hp (by decide)
    have herr : sourceNeighborError J c x n ≤
        exp (-(x n / ((J + n : ℕ) : ℝ) ^ (7 / 2 : ℝ)) +
          2 * c * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 4)) := by
      unfold sourceNeighborError
      apply exp_le_exp.mpr
      have hd := div_le_div_of_nonneg_left (mul_nonneg hc (hxp n).le)
        (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 4) hp4
      simp only [div_eq_mul_inv] at hd ⊢
      nlinarith only [hd]
    have hθ := pow_le_pow_left₀ (by linarith [(sourceTheta_bounds hJ1 hC hx1 n).1] :
      0 ≤ sourceTheta J C x n) (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul herr hθ (pow_nonneg (by linarith [(sourceTheta_bounds hJ1 hC hx1 n).1]) A)
      (exp_pos _).le
    convert! hh using 1
    simp only [neg_one_mul, mul_pow, ← pow_mul]
    ring

/-- Multiplying any decaying source exponential by a fixed horizon power
preserves summability. -/
theorem theta_weighted_source_exponential_summable
    (J d B : ℕ) (hJ : d < J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C a b c : ℝ) (hC : 1 ≤ C) (ha : 0 ≤ a) (haB : a < B) (hb : 0 < b) (A : ℕ) :
    Summable (fun n => sourceTheta J C x n ^ A *
      exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
        c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := polynomial_source_scale_summable J d B hJ x (by linarith) hx a b c
    ((2 * C) ^ A) (2 * A) (2 * A) ha haB hb (by positivity)
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A) (exp_pos _).le
  · intro n
    have hθ := pow_le_pow_left₀ (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1)
      (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul_of_nonneg_right hθ (exp_pos
      (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) + c * (x n / ((J - d + n : ℕ) : ℝ) ^ B))).le
    convert! hh using 1
    simp only [mul_pow, ← pow_mul]

/-- The parent-frequency error is summable with every horizon power. -/
theorem source_prior_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) :
    Summable (fun n => sourcePriorError J x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := theta_weighted_source_exponential_summable J 0 5 (by omega) x hx0 hx
    C 4 (1 / 4) 0 hC (by norm_num) (by norm_num) (by norm_num) A
  simp only [rpow_ofNat, zero_mul, add_zero] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    exact mul_nonneg (exp_pos _).le (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A)
  · intro n
    have hp : (0 : ℝ) < (J - 1 + n : ℕ) := by exact_mod_cast (show 0 < J - 1 + n by omega)
    have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (show J - 1 + n ≤ J + n by omega)
    have hpow := pow_le_pow_left₀ hp.le hpj 4
    have hd := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < 4 * ((J - 1 + n : ℕ) : ℝ) ^ 4)
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4))
    have he : sourcePriorError J x n ≤ exp (-(1 / 4) * (x n / ((J + n : ℕ) : ℝ) ^ 4)) := by
      unfold sourcePriorError
      apply exp_le_exp.mpr
      convert! neg_le_neg hd using 1 <;> ring
    have hh := mul_le_mul_of_nonneg_right he
      (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) A)
    simpa only [mul_comm] using hh

/-- The source shear/older-gradient product has an explicit decaying
exponential majorant at every normal stage after the two base exceptions. -/
theorem source_shear_gradient_bound
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) (n : ℕ) :
    sourceEpsilon J x n * sourceOlderGradient J x n ^ 2 ≤
      8 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7) +
        2 * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9)) := by
  have ho : (1 : ℝ) ≤ (J - 2 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 2 + n by omega)
  have hop : ((J - 2 + n : ℕ) : ℝ) ≤ ((J - 1 + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 2 + n ≤ J - 1 + n by omega)
  have hp : (0 : ℝ) < (J - 1 + n : ℕ) := lt_of_lt_of_le (by linarith : (0 : ℝ) < (J - 2 + n : ℕ)) hop
  have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by
    exact_mod_cast (show J - 1 + n ≤ J + n by omega)
  have hpow := pow_le_pow_left₀ hp.le hpj 7
  have hd := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < 2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)
    (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
  have he : sourceEpsilon J x n ≤ 2 * exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 7)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply exp_le_exp.mpr
    convert! neg_le_neg hd using 1 <;> ring
  have hden : ((J - 2 + n : ℕ) : ℝ) ^ 9 ≤
      ((J - 1 + n : ℕ) : ℝ) ^ 2 * ((J - 2 + n : ℕ) : ℝ) ^ 7 := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one ho) hop 2)
      (by positivity : 0 ≤ ((J - 2 + n : ℕ) : ℝ) ^ 7)
    simpa only [← pow_add] using hh
  have hdG := div_le_div_of_nonneg_left (hx n)
    (by positivity : 0 < ((J - 2 + n : ℕ) : ℝ) ^ 9) hden
  have hg : sourceOlderGradient J x n ≤ 2 * exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) := by
    have hle := exp_le_exp.mpr hdG
    have h1 : 1 ≤ exp (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) :=
      one_le_exp_iff.mpr (div_nonneg (hx n) (by positivity))
    unfold sourceOlderGradient
    linarith
  have hg₀ : 0 ≤ sourceOlderGradient J x n := by unfold sourceOlderGradient; positivity
  have hh := mul_le_mul he (pow_le_pow_left₀ hg₀ hg 2) (sq_nonneg _) (by positivity)
  convert! hh using 1
  rw [exp_add, show (2 : ℝ) * (x n / ((J - 2 + n : ℕ) : ℝ) ^ 9) =
    x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 + x n / ((J - 2 + n : ℕ) : ℝ) ^ 9 by ring, exp_add]
  ring

/-- The change of the parent shear and older coefficients obeys every
polynomial smallness regime required by the ray analysis. -/
theorem source_shear_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) :
    Summable (fun n => sourceEpsilon J x n * sourceTheta J C x n *
      sourceOlderGradient J x n ^ 2 * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := (theta_weighted_source_exponential_summable J 2 9 (by omega) x hx0 hx
    C 7 (1 / 2) 2 hC (by norm_num) (by norm_num) (by norm_num) (A + 1)).mul_left 8
  simp only [rpow_ofNat] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    have hθ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold sourceEpsilon sourceOlderGradient
    positivity
  · intro n
    have hh := mul_le_mul_of_nonneg_right
      (source_shear_gradient_bound J hJ x (fun m => le_trans zero_le_one (hx1 m)) n)
      (pow_nonneg (le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1) (A + 1))
    convert! hh using 1 <;> simp only [pow_succ] <;> ring

/-- The complete error specified by the logarithmic scales is summable
after multiplication by any fixed horizon power. -/
theorem source_coefficient_error_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) (A : ℕ) :
    Summable (fun n => sourceCoefficientError J C c x n * sourceTheta J C x n ^ A) := by
  have hh := (((source_shear_error_summable J hJ x hx0 hx C hC A).add
    (source_prior_error_summable J hJ x hx0 hx C hC A)).add
    (source_neighbor_error_summable J hJ x hx0 hx C c hC hc A)).mul_left 16
  convert! hh using 1
  ext n
  unfold sourceCoefficientError
  ring

/-- In particular the actual source scales eventually satisfy the
quantitative `Θ^40` guard needed by the complete ODE frame analysis. -/
theorem source_coefficient_error_eventually_small
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C c K : ℝ) (hC : 1 ≤ C) (hc : 0 ≤ c) :
    ∀ᶠ n in atTop, 1000000 * K * sourceCoefficientError J C c x n * sourceTheta J C x n ^ 40 ≤ 1 := by
  have hh := (source_coefficient_error_summable J hJ x hx0 hx C c hC hc 40).tendsto_atTop_zero.const_mul
    (1000000 * K)
  simp only [mul_zero] at hh
  have hh' := hh.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh'] with n hn
  nlinarith only [hn]

end EulerPacketSourceScales

end

section

open Filter
open scoped Topology

namespace EulerPacketSourceTime

open Real EulerScale EulerPacketScaleGeometry EulerPacketSourceScales

/-- The preceding two shear logarithms are exactly those obtained by
substituting the quadratic recurrence into (37). -/
theorem preceding_scale_identities {p q x X Y : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hx : x = p ^ 2 * X) (hX : X = q ^ 2 * Y) :
    X / p ^ 5 = x / p ^ 7 ∧ Y / q ^ 5 = x / (p ^ 2 * q ^ 7) := by
  constructor
  · rw [hx]
    field_simp
  · rw [hx, hX]
    field_simp

/-- A frame normalization `a≤2` gives the explicit source epsilon bound. -/
theorem epsilon_of_shear_bound {a L : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    sqrt (a / exp L) ≤ 2 * exp (-L / 2) := by
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  rw [sqrt_div ha, ← exp_half]
  have hid : -L / 2 = -(L / 2) := by ring
  rw [hid, exp_neg]
  change sqrt a / exp (L / 2) ≤ 2 / exp (L / 2)
  exact div_le_div_of_nonneg_right hs (exp_pos (L / 2)).le

/-- The current time width in (37), after exact substitution of the scales. -/
noncomputable def sourceTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * ((J + n : ℕ) : ℝ) ^ 2 * (x n) ^ 2 *
    exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- The following time width, using `x_j=j²x_{j-1}` twice. -/
noncomputable def sourceNextTimeWidth (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))

/-- The exact quotient of consecutive time widths. -/
noncomputable def sourceTimeRatio (J : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 2 *
    exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) +
      x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))

/-- Exact cancellation computes the consecutive time-width quotient. -/
theorem source_time_ratio_identity (J : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    sourceNextTimeWidth J x n = sourceTimeRatio J x n * sourceTimeWidth J x n := by
  unfold sourceNextTimeWidth sourceTimeRatio sourceTimeWidth
  rw [exp_add]
  have hc : exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      exp (-x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) = 1 := by
    rw [← exp_add]
    convert! exp_zero using 1
    ring_nf
  linear_combination -(3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 *
    (x n) ^ 2 * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) * hc

/-- Consecutive time-width ratios are summable, so they tend to zero. -/
theorem source_time_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (sourceTimeRatio J x) := by
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) 4 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, pow_zero, mul_one] at hsum
  apply hsum.of_nonneg_of_le
  · intro n; unfold sourceTimeRatio; positivity
  · intro n
    have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
    have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hj]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ((J + n : ℕ) : ℝ))
    have hh' := mul_le_mul_of_nonneg_right hh (exp_pos
      (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7))).le
    unfold sourceTimeRatio
    have hid : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) + x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) + (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by ring
    rw [hid] at hh' ⊢
    convert! hh' using 1
    ring

/-- The actual next time width is eventually at most half of the current width. -/
theorem source_time_width_eventually_contracts
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ᶠ n in atTop, sourceNextTimeWidth J x n ≤ sourceTimeWidth J x n / 2 := by
  have hh := (source_time_ratio_summable J hJ x hx0 hx).tendsto_atTop_zero.eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hh] with n hn
  rw [source_time_ratio_identity]
  have hW : 0 ≤ sourceTimeWidth J x n := by unfold sourceTimeWidth; positivity
  have hb := mul_le_mul_of_nonneg_right hn hW
  nlinarith only [hb]

/-- The extra normalized horizon length has the explicit polynomial/exponential
bound asserted after (39). -/
theorem source_extra_time_bound
    (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) * sourceNextTimeWidth J x n ≤
      48 * ((J + n : ℕ) : ℝ) ^ 6 * (x n) ^ 2 *
        exp (-(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) +
          (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hj : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hs : sqrt a ≤ 2 := (sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hroot : sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) ≤
      2 * exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
    rw [sqrt_mul ha, ← exp_half]
    have hh := mul_le_mul_of_nonneg_right hs (exp_pos ((x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) / 2)).le
    convert! hh using 1
    congr 2
    ring
  have hp : (((J + n : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((J + n : ℕ) : ℝ) ^ 2 := by nlinarith only [hj]
  have hW : 0 ≤ sourceNextTimeWidth J x n := by unfold sourceNextTimeWidth; positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 2)) hW
  have hp' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 12 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7)) * exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5)))
  unfold sourceNextTimeWidth at hh
  have hpE : x n / (2 * ((J - 1 + n : ℕ) : ℝ) ^ 7) =
      (1 / 2) * (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) := by ring
  have hnE : -x n / (2 * ((J + n : ℕ) : ℝ) ^ 5) =
      -(1 / 2) * (x n / ((J + n : ℕ) : ℝ) ^ 5) := by ring
  rw [hpE, hnE] at hh hp'
  rw [exp_add]
  change 2 * sqrt (a * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
    (3 * (((J + n : ℕ) : ℝ) + 1) ^ 2 * ((J + n : ℕ) : ℝ) ^ 4 * (x n) ^ 2 *
      exp (-x n / (2 * ((J + n : ℕ) : ℝ) ^ 5))) ≤ _
  rw [hnE]
  refine hh.trans ?_
  convert! hp' using 1 <;> ring

/-- Every horizon power times the extra normalized length is summable. -/
theorem source_extra_time_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C : ℝ) (hC : 1 ≤ C) (A : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2) :
    Summable (fun n => 2 * sqrt (a n * exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) *
      sourceNextTimeWidth J x n * sourceTheta J C x n ^ A) := by
  have hJ1 : 1 ≤ J := by omega
  have hx1 := quadratic_growth_one_le J hJ1 x hx0 hx
  have hsum := polynomial_source_scale_summable J 1 7 (by omega) x (by linarith) hx
    5 (1 / 2) (1 / 2) (48 * (2 * C) ^ A) (6 + 2 * A) (2 + 2 * A)
    (by norm_num) (by norm_num) (by norm_num) (by positivity)
  simp only [rpow_ofNat] at hsum
  apply hsum.of_nonneg_of_le
  · intro n
    have hθ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold sourceNextTimeWidth
    positivity
  · intro n
    have hθ₀ := le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 n).1
    have hθ := pow_le_pow_left₀ hθ₀ (sourceTheta_bounds hJ1 hC hx1 n).2 A
    have hh := mul_le_mul (source_extra_time_bound J hJ1 x n (ha n) (ha₂ n)) hθ
      (pow_nonneg hθ₀ A) (by positivity)
    convert! hh using 1
    simp only [mul_pow, pow_add, ← pow_mul]
    ring

/-- The parent-shear square is negligible relative to the newly chosen shear. -/
theorem source_parent_shear_square_ratio_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (2 * x n / ((J - 1 + n : ℕ) : ℝ) ^ 7) /
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5)) := by
  have hh := source_scale_exponential_summable J 1 7 (by omega) x (by linarith) hx
    5 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hh
  apply hh.congr
  intro n
  rw [← exp_sub]
  congr 1
  ring

/-- The good-interval pressure costs of the source are summable. -/
theorem source_good_interval_cost_summable
    (J : ℕ) (hJ : 3 ≤ J) (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    Summable (fun n => exp (-x n / ((J + n : ℕ) : ℝ) ^ 3) *
      exp (x n / ((J + n : ℕ) : ℝ) ^ 5) *
      exp (x n / ((J - 1 + n : ℕ) : ℝ) ^ 7)) := by
  have hsum := source_scale_exponential_summable J 1 5 (by omega) x (by linarith) hx
    3 1 2 0 0 0 (by norm_num) (by norm_num) (by norm_num)
  simp only [rpow_ofNat, neg_one_mul, zero_mul, add_zero] at hsum
  have hx1 := quadratic_growth_one_le J (by omega) x hx0 hx
  apply hsum.of_nonneg_of_le
  · intro n; positivity
  · intro n
    have hp : (1 : ℝ) ≤ (J - 1 + n : ℕ) := by exact_mod_cast (show 1 ≤ J - 1 + n by omega)
    have hpj : ((J - 1 + n : ℕ) : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (show J - 1 + n ≤ J + n by omega)
    have hd₁ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_left₀ (by linarith) hpj 5)
    have hd₂ := div_le_div_of_nonneg_left (le_trans zero_le_one (hx1 n))
      (by positivity : 0 < ((J - 1 + n : ℕ) : ℝ) ^ 5) (pow_le_pow_right₀ hp (by decide : 5 ≤ 7))
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    simp only [div_eq_mul_inv] at hd₁ hd₂ ⊢
    nlinarith only [hd₁, hd₂]

end EulerPacketSourceTime

end

section

open Filter
open scoped Topology

namespace EulerPacketBaseScales

open Real

/-- A negative total real power absorbs a fixed monomial horizon. -/
theorem base_power_decay (T p : ℝ) (m k : ℕ)
    (hp : p + 2 * m + k < 0) :
    Tendsto (fun x : ℝ => x ^ p * (T * x ^ 2) ^ m * x ^ k) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).const_mul (T ^ m)
  simp only [neg_neg, mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring

/-- Exponential decay absorbs every fixed real polynomial power and
every fixed monomial horizon power. -/
theorem base_exponential_decay (T p b : ℝ) (m k : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ p * exp (-b * x) * (T * x ^ 2) ^ m * x ^ k)
      atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 2 * m + k) b hb).const_mul (T ^ m)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [rpow_add hx, rpow_add hx]
  have hm : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
  rw [hm, rpow_natCast, rpow_natCast]
  simp only [mul_pow, pow_mul]
  ring

/-- The first normal stage has `h=x₀^1000`, hence epsilon of order
`x₀^-500`; its complete coefficient error beats `x₀^-10 Θ^-60`. -/
theorem first_stage_coefficient_error_tendsto_zero
    (T D N b : ℝ) (hD : 1000 ≤ D) (hb : 0 < b) :
    Tendsto (fun x : ℝ =>
      (16 * (8 * x ^ (-500 : ℝ) * (T * x ^ 2) +
        x ^ (-D / 4) + x ^ N * exp (-b * x))) * (T * x ^ 2) ^ 60 * x ^ 10)
      atTop (𝓝 0) := by
  have h₁ := (base_power_decay T (-500) 61 10 (by norm_num)).const_mul 8
  have h₂ := base_power_decay T (-D / 4) 60 10 (by push_cast; linarith)
  have h₃ := base_exponential_decay T N b 60 10 hb
  have hh := ((h₁.add h₂).add h₃).const_mul 16
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [show (61 : ℕ) = 60 + 1 from rfl, pow_succ]
  ring

/-- At the special second stage the older gradient is polynomial in
the base scale, while the new inverse shear is exponentially small. -/
theorem second_stage_shear_error_tendsto_zero
    (T b : ℝ) (hb : 0 < b) (A : ℕ) :
    Tendsto (fun x : ℝ => exp (-b * x) * (1 + x ^ (1000 : ℕ)) ^ 2 *
      (T * x ^ 2) ^ A) atTop (𝓝 0) := by
  have h₀ := base_exponential_decay T 0 b A 0 hb
  have h₁ := (base_exponential_decay T 1000 b A 0 hb).const_mul 2
  have h₂ := base_exponential_decay T 2000 b A 0 hb
  have hh := (h₀.add h₁).add h₂
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro x
  dsimp only
  simp only [rpow_zero, rpow_ofNat, pow_zero, mul_one, one_mul]
  have hp : x ^ (2000 : ℕ) = (x ^ (1000 : ℕ)) ^ 2 := by rw [← pow_mul]
  rw [hp]
  ring

/-- The exact base horizon `6 J² x₀^(2-1000/2)` tends to zero. -/
theorem base_horizon_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => 6 * J ^ 2 * x ^ (2 - 1000 / 2 : ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 498)).const_mul (6 * J ^ 2)
  norm_num at hh ⊢
  exact hh

/-- The core-volume guard `h r³ Sbase`, with `r=x₀^-1000`,
also tends to zero from the explicit base choices. -/
theorem base_core_volume_cost_tendsto_zero (J : ℝ) :
    Tendsto (fun x : ℝ => x ^ (1000 : ℕ) * (x ^ (-1000 : ℝ)) ^ 3 *
      (6 * J ^ 2 * x ^ (-498 : ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2498)).const_mul (6 * J ^ 2)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hid : (-2498 : ℝ) = 1000 + (-1000) * 3 + (-498) := by norm_num
  rw [hid, rpow_add hx, rpow_add hx, rpow_mul hx.le]
  norm_num only [rpow_ofNat]
  ring

end EulerPacketBaseScales

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleSums

open Real EulerScale

/-- Once the initial stage dominates the fixed polynomial exponent,
the rescaled quadratic sequence grows by at least a factor two at every step. -/
theorem polynomial_scale_doubles
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) (n : ℕ) :
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤ x (n + 1) / ((J + (n + 1) : ℕ) : ℝ) ^ A := by
  have hxp := quadratic_growth_pos J hJ x hx0 hx
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hJj : (J : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show J ≤ J + n by omega)
  have hJ₀ : (0 : ℝ) ≤ J := by positivity
  have hpower : (2 : ℝ) ^ (A + 1) ≤ ((J + n : ℕ) : ℝ) ^ 2 :=
    hJA.trans (pow_le_pow_left₀ hJ₀ hJj 2)
  have hn : ((J + (n + 1) : ℕ) : ℝ) = ((J + n : ℕ) : ℝ) + 1 := by push_cast; ring
  have hden : (((J + n : ℕ) : ℝ) + 1) ^ A ≤ (2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A := by
    have hh := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (J + n : ℕ) + 1)
      (by linarith : ((J + n : ℕ) : ℝ) + 1 ≤ 2 * ((J + n : ℕ) : ℝ)) A
    simpa only [mul_pow] using hh
  rw [hx, hn]
  calc
    2 * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
        (((J + n : ℕ) : ℝ) ^ 2 / (2 : ℝ) ^ A) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (hxp n).le (pow_nonneg hj.le A))
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ A)).2
      simpa only [pow_succ, mul_comm] using hpower
    _ = (((J + n : ℕ) : ℝ) ^ 2 * x n) / ((2 : ℝ) ^ A * ((J + n : ℕ) : ℝ) ^ A) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (hxp n).le)
      (by positivity : 0 < (((J + n : ℕ) : ℝ) + 1) ^ A) hden

/-- The entire positive exponent sequence is bounded below by its first
term times `2^n`, uniformly in the initial scale. -/
theorem polynomial_scale_geometric_lower
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) :
    ∀ n, (2 : ℝ) ^ n * (x 0 / (J : ℝ) ^ A) ≤ x n / ((J + n : ℕ) : ℝ) ^ A := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
      have hd := polynomial_scale_doubles J A hJ hJA x hx0 hx n
      rw [pow_succ]
      nlinarith only [hh, hd]

/-- A simple exact comparison between binary growth and the stage count. -/
theorem stage_count_le_two_pow (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      push_cast
      rw [pow_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith only [ih, hn]

/-- Every term of the source exponential series is bounded by one
explicit geometric series whose ratio depends only on the first scale. -/
theorem source_exponential_geometric_majorant
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) (n : ℕ) :
    exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A)) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) * exp (-b * (x 0 / (J : ℝ) ^ A)) ^ n := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hd := polynomial_scale_geometric_lower J A hJ hJA x hx0 hx n
  have hn := mul_le_mul_of_nonneg_right (stage_count_le_two_pow n)
    (div_nonneg hx0.le (pow_nonneg hJp.le A))
  have he : -b * (x n / ((J + n : ℕ) : ℝ) ^ A) ≤
      -b * (x 0 / (J : ℝ) ^ A) + (n : ℝ) * (-b * (x 0 / (J : ℝ) ^ A)) := by
    have hh := mul_le_mul_of_nonpos_left (hn.trans hd) (neg_nonpos.mpr hb.le)
    nlinarith only [hh]
  have hh := exp_le_exp.mpr he
  simpa only [exp_add, exp_nat_mul] using hh

/-- The full exponential-cost sum has an explicit upper bound tending
to zero as the initial scale increases. This makes the uniform small-sum
choice in the source quantitative. -/
theorem source_exponential_tsum_bound
    (J A : ℕ) (hJ : 1 ≤ J) (hJA : (2 : ℝ) ^ (A + 1) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 0 < x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (b : ℝ) (hb : 0 < b) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ A))) ≤
      exp (-b * (x 0 / (J : ℝ) ^ A)) / (1 - exp (-b * (x 0 / (J : ℝ) ^ A))) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let r := exp (-b * (x 0 / (J : ℝ) ^ A))
  have hr₀ : 0 ≤ r := (exp_pos _).le
  have hr : |r| < 1 := by
    rw [abs_of_nonneg hr₀]
    apply exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hb) (div_pos hx0 (pow_pos hJp A))
  have hgeom := (summable_geometric_of_abs_lt_one hr).mul_left r
  have hsum := exponential_decay_summable J hJ x hx0 hx A b hb
  have hh := hsum.tsum_le_tsum (source_exponential_geometric_majorant J A hJ hJA x hx0 hx b hb) hgeom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hr] at hh
  simpa only [r, div_eq_mul_inv] using hh

/-- The explicit geometric-series bound vanishes as `x₀` tends to infinity. -/
theorem source_exponential_bound_tendsto_zero (J A : ℕ) (hJ : 1 ≤ J)
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A)) /
      (1 - exp (-b * (X / (J : ℝ) ^ A)))) atTop (𝓝 0) := by
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hh := EulerPacketBaseScales.base_exponential_decay 1 0 (b / (J : ℝ) ^ A) 0 0
    (div_pos hb (pow_pos hJp A))
  simp only [rpow_zero, one_mul, pow_zero, mul_one] at hh
  have hh' : Tendsto (fun X : ℝ => exp (-b * (X / (J : ℝ) ^ A))) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    congr 1
    ring
  have hd := hh'.div (tendsto_const_nhds.sub hh') (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, zero_div] at hd
  convert! hd using 1

end EulerPacketUniformScaleSums

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformLogBounds

open Real EulerScale EulerPacketUniformScaleSums

/-- Every fixed polynomial logarithm is bounded by a simple product of
the stage and the square root of the scale. -/
theorem polynomial_log_bound {j X C p q : ℝ} (hj : 1 ≤ j) (hX : 1 ≤ X) :
    C + p * log j + q * log X ≤ (|C| + |p| + 2 * |q|) * j * sqrt X := by
  have hjp : 0 < j := by linarith
  have hXp : 0 < X := by linarith
  have hs : 1 ≤ sqrt X := one_le_sqrt.mpr hX
  have hsj : 1 ≤ j * sqrt X := one_le_mul_of_one_le_of_one_le hj hs
  have hlj : 0 ≤ log j := log_nonneg hj
  have hlX : 0 ≤ log X := log_nonneg hX
  have hljb : log j ≤ j := (log_le_sub_one_of_pos hjp).trans (by linarith)
  have hlXb : log X ≤ 2 * sqrt X := by
    have hh := log_le_sub_one_of_pos (sqrt_pos.mpr hXp)
    rw [log_sqrt hXp.le] at hh
    linarith
  have hCb : C ≤ |C| * j * sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hsj (abs_nonneg C)
    nlinarith only [hh, le_abs_self C]
  have hp₁ := mul_le_mul_of_nonneg_right (le_abs_self p) hlj
  have hp₂ := mul_le_mul_of_nonneg_left hljb (abs_nonneg p)
  have hp₃ := mul_le_mul_of_nonneg_left hs (mul_nonneg (abs_nonneg p) hjp.le)
  have hq₁ := mul_le_mul_of_nonneg_right (le_abs_self q) hlX
  have hq₂ := mul_le_mul_of_nonneg_left hlXb (abs_nonneg q)
  have hq₃ := mul_le_mul_of_nonneg_right hj (mul_nonneg (by positivity : 0 ≤ 2 * |q|) (sqrt_nonneg X))
  nlinarith only [hCb, hp₁, hp₂, hp₃, hq₁, hq₂, hq₃]

/-- A single explicit lower bound on the initial scale absorbs the
polynomial logarithms at every subsequent quadratic stage. -/
theorem polynomial_logs_uniformly_absorbed
    (J A : ℕ) (hJ : 1 ≤ J)
    (hJA : (2 : ℝ) ^ (2 * A + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (C p q b : ℝ) (hb : 0 < b)
    (hlarge : (2 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * A + 2) ≤ x 0) :
    ∀ n, C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) := by
  let S := |C| + |p| + 2 * |q|
  let L := 2 * S / b
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJp : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hgeom := polynomial_scale_geometric_lower J (2 * A + 2) hJ
    (by simpa only [show 2 * A + 2 + 1 = 2 * A + 3 by omega] using hJA) x (by linarith) hx
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hstart : L ^ 2 ≤ x 0 / (J : ℝ) ^ (2 * A + 2) := by
    apply (le_div_iff₀ (pow_pos hJp _)).2
    exact hlarge
  have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hone
    (div_nonneg (le_trans zero_le_one hx0) (pow_nonneg hJp.le (2 * A + 2)))
  have hscale : L ^ 2 ≤ x n / ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
    nlinarith only [hstart, hbase, hgeom n]
  have hsquare := (le_div_iff₀ (pow_pos hj (2 * A + 2))).mp hscale
  have hroot : L * ((J + n : ℕ) : ℝ) ^ (A + 1) ≤ sqrt (x n) := by
    have hp : (((J + n : ℕ) : ℝ) ^ (A + 1)) ^ 2 = ((J + n : ℕ) : ℝ) ^ (2 * A + 2) := by
      rw [← pow_mul]
      congr 1
      omega
    have hs := sq_sqrt (le_trans zero_le_one (hx1 n))
    have hn : 0 ≤ L * ((J + n : ℕ) : ℝ) ^ (A + 1) := by positivity
    nlinarith only [hsquare, hp, hs, hn, sqrt_nonneg (x n)]
  have hlog := polynomial_log_bound (C := C) (p := p) (q := q) hj1 (hx1 n)
  have hlogmul := mul_le_mul_of_nonneg_right hlog (pow_nonneg hj.le A)
  have hrootmul := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg (div_nonneg hb.le (by norm_num : (0 : ℝ) ≤ 2)) (sqrt_nonneg (x n)))
  have hLS : (b / 2) * L = S := by dsimp [L]; field_simp
  have hid : (b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ A) =
      ((b / 2) * x n) / ((J + n : ℕ) : ℝ) ^ A := by ring
  rw [hid]
  apply (le_div_iff₀ (pow_pos hj A)).2
  have hmul : S * ((J + n : ℕ) : ℝ) ^ (A + 1) * sqrt (x n) ≤ (b / 2) * x n := by
    calc
      _ = (L * ((J + n : ℕ) : ℝ) ^ (A + 1)) * ((b / 2) * sqrt (x n)) := by rw [← hLS]; ring
      _ ≤ sqrt (x n) * ((b / 2) * sqrt (x n)) := hrootmul
      _ = (b / 2) * (sqrt (x n)) ^ 2 := by ring
      _ = _ := by rw [sq_sqrt (le_trans zero_le_one (hx1 n))]
  rw [pow_succ] at hmul
  dsimp only [S] at hmul
  nlinarith only [hlogmul, hmul]

end EulerPacketUniformLogBounds

end

section

open Filter
open scoped Topology

namespace EulerPacketUniformScaleChoice

open Real EulerScale EulerPacketScaleGeometry EulerPacketUniformScaleSums EulerPacketUniformLogBounds

/-- One sufficiently large initial stage makes every predecessor-log
coefficient small, uniformly over all subsequent stages. -/
theorem exists_uniform_stage_choice (d B N : ℕ) (a c b : ℝ)
    (haB : a < B) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ d < J ∧ (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2 ∧
      ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4 := by
  have hh := (stage_rpow_div_shifted_power_tendsto_zero (d + 1) d B (by omega) a haB).const_mul c
  simp only [mul_zero] at hh
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hh.eventually_le_const (by positivity : (0 : ℝ) < b / 4))
  let R : ℕ := 2 ^ (2 * N + 3) + 3
  let J : ℕ := (d + 1) + M + R
  have hR3 : 3 ≤ R := Nat.le_add_left 3 _
  have hJ3 : 3 ≤ J := by dsimp [J]; omega
  have hdJ : d < J := by dsimp [J]; omega
  have hpJ : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) := by
    exact_mod_cast (show 2 ^ (2 * N + 3) ≤ J by dsimp [J, R]; omega)
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  refine ⟨J, hJ3, hdJ, by nlinarith only [hpJ, hJr], ?_⟩
  intro n
  have h := hM (M + R + n) (by omega)
  have hj : d + 1 + (M + R + n) = J + n := by dsimp [J]; omega
  have hp : d + 1 - d + (M + R + n) = J - d + n := by dsimp [J]; omega
  simpa only [hj, hp] using h

/-- For a stage chosen above, one explicit lower bound on the initial
scale controls all logarithmic scale errors at once. -/
theorem uniform_source_exponent_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    ∀ n, -b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n) ≤
      -(b / 2) * (x n / ((J + n : ℕ) : ℝ) ^ N) := by
  have hx1 := quadratic_growth_one_le J hJ x hx0 hx
  have hlog := polynomial_logs_uniformly_absorbed J N hJ hJN x hx0 hx C p q (b / 2)
    (by positivity) (by convert! hlarge using 1; ring)
  intro n
  have hj1 : (1 : ℝ) ≤ (J + n : ℕ) := by exact_mod_cast (show 1 ≤ J + n by omega)
  have hj : (0 : ℝ) < (J + n : ℕ) := by linarith
  have hp : (0 : ℝ) < (J - d + n : ℕ) := by exact_mod_cast (show 0 < J - d + n by omega)
  have hxn : 0 < x n := by linarith [hx1 n]
  have hpow : ((J + n : ℕ) : ℝ) ^ a ≤ ((J + n : ℕ) : ℝ) ^ N := by
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le hj1 haN
  have hscales := div_le_div_of_nonneg_left hxn.le (rpow_pos_of_pos hj a) hpow
  have hcm := mul_le_mul_of_nonneg_right (hcoeff n)
    (div_nonneg hxn.le (rpow_nonneg hj.le a))
  have hct : c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) ≤
      (b / 4) * (x n / ((J + n : ℕ) : ℝ) ^ a) := by
    convert! hcm using 1
    field_simp [(rpow_pos_of_pos hj a).ne', hp.ne']
  have hscaleB := mul_le_mul_of_nonneg_left hscales hb.le
  have hl := hlog n
  nlinarith only [hct, hscaleB, hl]

/-- The complete logarithmic source cost has a uniform geometric-series
bound after choosing the stage and then the initial scale. -/
theorem uniform_source_cost_tsum_bound
    (J d B N : ℕ) (hJ : 1 ≤ J) (hdJ : d < J)
    (hJN : (2 : ℝ) ^ (2 * N + 3) ≤ (J : ℝ) ^ 2)
    (x : ℕ → ℝ) (hx0 : 1 ≤ x 0)
    (hx : ∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n)
    (a b c C p q : ℝ) (haN : a ≤ N) (hb : 0 < b)
    (hcoeff : ∀ n, c * (((J + n : ℕ) : ℝ) ^ a / ((J - d + n : ℕ) : ℝ) ^ B) ≤ b / 4)
    (hlarge : (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2) ≤ x 0) :
    (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
      c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
      C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤
      exp (-(b / 2) * (x 0 / (J : ℝ) ^ N)) /
        (1 - exp (-(b / 2) * (x 0 / (J : ℝ) ^ N))) := by
  have hmajor := fun n => exp_le_exp.mpr
    (uniform_source_exponent_bound J d B N hJ hdJ hJN x hx0 hx a b c C p q haN hb hcoeff hlarge n)
  have hsum := exponential_decay_summable J hJ x (by linarith) hx N (b / 2) (by positivity)
  have hcost := hsum.of_nonneg_of_le (fun _ => (exp_pos _).le) hmajor
  have hh := hcost.tsum_le_tsum hmajor hsum
  have hpower : (2 : ℝ) ^ (N + 1) ≤ (J : ℝ) ^ 2 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : N + 1 ≤ 2 * N + 3)).trans hJN
  exact hh.trans (source_exponential_tsum_bound J N hJ hpower x (by linarith) hx (b / 2) (by positivity))

/-- The source's order of parameter choice is valid: first one chooses
the stage `J`, then the base scale `x₀`, and the whole infinite sum is
arbitrarily small. This includes the real support exponent `7/2`. -/
theorem source_uniform_small_sum_choice
    (d B N : ℕ) (a b c C p q : ℝ) (haB : a < B) (haN : a ≤ N) (hb : 0 < b) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) →
        (∑' n, exp (-b * (x n / ((J + n : ℕ) : ℝ) ^ a) +
          c * (x n / ((J - d + n : ℕ) : ℝ) ^ B) +
          C + p * log ((J + n : ℕ) : ℝ) + q * log (x n))) ≤ δ := by
  obtain ⟨J, hJ3, hdJ, hJN, hcoeff⟩ := exists_uniform_stage_choice d B N a c b haB hb
  have hJ : 1 ≤ J := by omega
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hh := source_exponential_bound_tendsto_zero J N hJ (b / 2) (by positivity)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (hh.eventually_le_const hδ)
  let L := (4 * (|C| + |p| + 2 * |q|) / b) ^ 2 * (J : ℝ) ^ (2 * N + 2)
  let X₀ := max 1 (max L Y)
  have hX₀ : 1 ≤ X₀ := le_max_left _ _
  refine ⟨X₀, hX₀, ?_⟩
  intro x hx0 hx
  have hx1 : 1 ≤ x 0 := hX₀.trans hx0
  have hlarge : L ≤ x 0 := (le_trans (le_max_left L Y) (le_max_right 1 (max L Y))).trans hx0
  have hYx : Y ≤ x 0 := (le_trans (le_max_right L Y) (le_max_right 1 (max L Y))).trans hx0
  exact (uniform_source_cost_tsum_bound J d B N hJ hdJ hJN x hx1 hx a b c C p q
    haN hb hcoeff hlarge).trans (hY (x 0) hYx)

end EulerPacketUniformScaleChoice

end

section

open Filter
open scoped Topology

namespace EulerPacketFiniteScaleChoice

open Real EulerPacketUniformScaleChoice EulerPacketUniformScaleSums

/-- Every finite collection of scale inequalities allows the same
choices of `J` and then `x₀`. Thus the source's different coefficient,
neighbor, time, and pressure-cost requirements can be imposed together. -/
theorem finite_source_uniform_small_sum_choice
    {ι : Type*} [Fintype ι] (d B N : ι → ℕ) (a b c C p q : ι → ℝ)
    (haB : ∀ i, a i < B i) (haN : ∀ i, a i ≤ N i) (hb : ∀ i, 0 < b i) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
      ∀ x : ℕ → ℝ, X₀ ≤ x 0 →
        (∀ n, x (n + 1) = ((J + n : ℕ) : ℝ) ^ 2 * x n) → ∀ i,
        (∑' n, exp (-(b i) * (x n / ((J + n : ℕ) : ℝ) ^ (a i)) +
          c i * (x n / ((J - d i + n : ℕ) : ℝ) ^ (B i)) +
          C i + p i * log ((J + n : ℕ) : ℝ) + q i * log (x n))) ≤ δ := by
  classical
  choose Ji hJi3 hJid hJiN hJiC using fun i =>
    exists_uniform_stage_choice (d i) (B i) (N i) (a i) (c i) (b i) (haB i) (hb i)
  let J := max 3 (Finset.univ.sup Ji)
  have hJ3 : 3 ≤ J := le_max_left _ _
  have hJ1 : 1 ≤ J := by omega
  have hJiLe (i : ι) : Ji i ≤ J :=
    (Finset.le_sup (f := Ji) (Finset.mem_univ i)).trans (le_max_right _ _)
  have hdJ (i : ι) : d i < J := lt_of_lt_of_le (hJid i) (hJiLe i)
  have hJN (i : ι) : (2 : ℝ) ^ (2 * N i + 3) ≤ (J : ℝ) ^ 2 := by
    exact (hJiN i).trans (pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast hJiLe i) 2)
  have hcoeff (i : ι) (n : ℕ) :
      c i * (((J + n : ℕ) : ℝ) ^ (a i) / ((J - d i + n : ℕ) : ℝ) ^ (B i)) ≤ b i / 4 := by
    have hh := hJiC i (J - Ji i + n)
    have hj : Ji i + (J - Ji i + n) = J + n := by have hi := hJiLe i; omega
    have hp : Ji i - d i + (J - Ji i + n) = J - d i + n := by
      have hi := hJiLe i
      have hid := hJid i
      omega
    simpa only [hj, hp] using hh
  refine ⟨J, hJ3, ?_⟩
  intro δ hδ
  have hboth : ∀ᶠ X : ℝ in atTop, ∀ i : ι,
      (4 * (|C i| + |p i| + 2 * |q i|) / b i) ^ 2 * (J : ℝ) ^ (2 * N i + 2) ≤ X ∧
      exp (-(b i / 2) * (X / (J : ℝ) ^ N i)) /
        (1 - exp (-(b i / 2) * (X / (J : ℝ) ^ N i))) ≤ δ := by
    apply eventually_all.2
    intro i
    have hi := source_exponential_bound_tendsto_zero J (N i) hJ1 (b i / 2)
      (div_pos (hb i) (by norm_num))
    exact (eventually_ge_atTop _).and (hi.eventually_le_const hδ)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hboth
  refine ⟨max 1 X, le_max_left _ _, ?_⟩
  intro x hx0 hx i
  have hx1 : 1 ≤ x 0 := (le_max_left 1 X).trans hx0
  have hall := hX (x 0) ((le_max_right 1 X).trans hx0) i
  exact (uniform_source_cost_tsum_bound J (d i) (B i) (N i) hJ1 (hdJ i) (hJN i)
    x hx1 hx (a i) (b i) (c i) (C i) (p i) (q i) (haN i) (hb i) (hcoeff i) hall.1).trans hall.2

end EulerPacketFiniteScaleChoice

end

section

namespace EulerPacketScaleActivation

open Real EulerPacketScaleGeometry

/-- The actual quadratic target and frame invariant imply every basic
small-beta and target-time guard used in the scalar ODE estimates. -/
theorem source_activation_ode_guards {j x β : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    0 < β ∧ β ≤ 1 / 16 ∧ 0 < sqrt β ∧ sqrt β ≤ 1 / 4 ∧
    1 / sqrt β ≤ (j ^ 2 * x) / sqrt β ∧
    (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 ∧
    0 < 1 / (j ^ 2 * x) ∧ 1 / (j ^ 2 * x) ≤ 1 / 2 := by
  have hxp : 0 < x := by linarith
  have hjp : 0 < j := by linarith
  have hβ : 0 < β := by nlinarith only [hβx, sq_nonneg x]
  have hx64 : 64 ≤ x ^ 2 := by nlinarith only [hx]
  have hm := mul_le_mul_of_nonneg_left hx64 hβ.le
  have hβsmall : β ≤ 1 / 16 := by nlinarith only [hm, hβx₂]
  have hσ : 0 < sqrt β := sqrt_pos.mpr hβ
  have hσsmall : sqrt β ≤ 1 / 4 := (sqrt_le_iff).2 ⟨by norm_num, by nlinarith only [hβsmall]⟩
  have hj2 : 9 ≤ j ^ 2 := by nlinarith only [hj]
  have hX : 2 ≤ j ^ 2 * x := by
    have hh := mul_le_mul hj2 hx (by norm_num : (0 : ℝ) ≤ 8) (sq_nonneg j)
    nlinarith only [hh]
  have htLow : 1 / sqrt β ≤ (j ^ 2 * x) / sqrt β :=
    div_le_div_of_nonneg_right (by linarith only [hX]) hσ.le
  have htime := activation_time_bounds (a := 1) (H := 1) (β := β) (x := x) (X := j ^ 2 * x)
    (by norm_num) (by norm_num) (by norm_num) hxp (by positivity) hβx hβx₂
  norm_num only [mul_one, sqrt_one, div_one] at htime
  have htUp : (j ^ 2 * x) / sqrt β ≤ 2 * j ^ 2 * x ^ 2 := by nlinarith only [htime.2]
  have hy : 0 < 1 / (j ^ 2 * x) := by positivity
  have hy₂ : 1 / (j ^ 2 * x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < j ^ 2 * x)).2
    nlinarith only [hX]
  exact ⟨hβ, hβsmall, hσ, hσsmall, htLow, htUp, hy, hy₂⟩

/-- The source polynomial horizon contains the target activation time. -/
theorem source_activation_within_horizon {j x β C : ℝ}
    (hj : 3 ≤ j) (hx : 8 ≤ x) (hC : 2 ≤ C)
    (hβx : 1 / 2 ≤ β * x ^ 2) (hβx₂ : β * x ^ 2 ≤ 2) :
    1 ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      (j ^ 2 * x) / sqrt β ≤ C * (1 + j ^ 2 * x ^ 2) ∧
      β * ((j ^ 2 * x) / sqrt β) ^ 2 = (j ^ 2 * x) ^ 2 := by
  obtain ⟨hβ, _, _, _, _, ht, _, _⟩ := source_activation_ode_guards hj hx hβx hβx₂
  have hn : 0 ≤ j ^ 2 * x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hC (by nlinarith only [hn] : 0 ≤ 1 + j ^ 2 * x ^ 2)
  refine ⟨by nlinarith only [hh, hn], by nlinarith only [ht, hh], ?_⟩
  rw [div_pow, sq_sqrt hβ.le]
  field_simp

end EulerPacketScaleActivation

end

end

