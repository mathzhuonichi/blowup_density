import Formal.R3RealLocalMildSolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit quantitative lifespan for the R³ endpoint-safe projected mild equation

The abstract Picard theorem produces *some* positive horizon.  This file makes the horizon
explicit for the concrete contract.

The concrete smoothing majorant is `k(τ) = 1 + (√((2π)²ντ))⁻¹`, so the cumulative smoothing
mass evaluates in closed form:

`K(T) = T + √T / (π √ν)`.

Writing `c = (π √ν)⁻¹`, `r = ‖u₀‖`, and `δ = δ(r)` for the smallness threshold of the
abstract theorem, the explicit lifespan

`T₀ = (δ / (1 + c + δ))²`

satisfies `0 < T₀ ≤ δ² ≤ 1` and `K(T₀) = √T₀ (√T₀ + c) < δ`, because
`√T₀ = δ / (1 + c + δ) ≤ δ < 1 + δ`.  Feeding `T₀` into the quantitative abstract theorem
yields a mild solution on the explicit horizon `[0, T₀]`, depending only on `ν` and `‖u₀‖`,
with the ball bound and ball uniqueness — and a physically real version for real data.

Scope guard: this is a quantitative *local* statement.  It proves no unconditional
uniqueness, no continuation criterion, and no Clay statement.
-/

namespace MNS2

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- The explicit smallness threshold of the abstract Picard theorem, as a function of the
initial-datum norm `r`: `δ(r) = min (1/(‖B‖(r+1)²+1)) (1/(2(‖B‖·2(r+1)+1)))`. -/
def r3MildSmallnessThreshold (r : ℝ) : ℝ :=
  min (1 / (‖r3ProjectedConvectionH3ToH2‖ * (r + 1) ^ 2 + 1))
    (1 / (2 * (‖r3ProjectedConvectionH3ToH2‖ * (2 * (r + 1)) + 1)))

/-- The explicit lifespan `T₀(ν, r) = (δ(r) / (1 + (π√ν)⁻¹ + δ(r)))²`, depending only on the
viscosity and the initial-datum norm. -/
def r3MildLifespan (nu r : ℝ) : ℝ :=
  (r3MildSmallnessThreshold r /
    (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r)) ^ 2

theorem r3MildSmallnessThreshold_pos {r : ℝ} (hr : 0 ≤ r) :
    0 < r3MildSmallnessThreshold r := by
  have hB : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  refine lt_min (div_pos one_pos ?_) (div_pos one_pos ?_)
  · have h1 : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ * (r + 1) ^ 2 :=
      mul_nonneg hB (sq_nonneg _)
    linarith
  · have h1 : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ * (2 * (r + 1)) :=
      mul_nonneg hB (by linarith)
    linarith

theorem r3MildSmallnessThreshold_le_one (r : ℝ) :
    r3MildSmallnessThreshold r ≤ 1 := by
  have h1 : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ * (r + 1) ^ 2 :=
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (sq_nonneg _)
  refine (min_le_left _ _).trans ?_
  rw [div_le_one (by linarith)]
  linarith

theorem r3MildLifespan_pos {nu r : ℝ} (hnu : 0 < nu) (hr : 0 ≤ r) :
    0 < r3MildLifespan nu r := by
  have hδ : 0 < r3MildSmallnessThreshold r := r3MildSmallnessThreshold_pos hr
  have hc : 0 < (Real.pi * Real.sqrt nu)⁻¹ :=
    inv_pos.mpr (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hnu))
  have hD : (0 : ℝ) < 1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r := by
    linarith
  exact pow_pos (div_pos hδ hD) 2

theorem r3MildLifespan_le_one {nu r : ℝ} (hnu : 0 < nu) (hr : 0 ≤ r) :
    r3MildLifespan nu r ≤ 1 := by
  have hδ : 0 < r3MildSmallnessThreshold r := r3MildSmallnessThreshold_pos hr
  have hδ1 : r3MildSmallnessThreshold r ≤ 1 := r3MildSmallnessThreshold_le_one r
  have hc : 0 < (Real.pi * Real.sqrt nu)⁻¹ :=
    inv_pos.mpr (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hnu))
  have hD : (0 : ℝ) < 1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r := by
    linarith
  have hfrac0 : (0 : ℝ) ≤ r3MildSmallnessThreshold r /
      (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r) := (div_pos hδ hD).le
  have hfrac1 : r3MildSmallnessThreshold r /
      (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r) ≤ 1 := by
    rw [div_le_one hD]
    linarith
  calc r3MildLifespan nu r ≤ 1 ^ 2 := pow_le_pow_left₀ hfrac0 hfrac1 2
    _ = 1 := one_pow 2

/-- Closed-form evaluation of the cumulative smoothing mass of the concrete contract:
`K(T) = T + √T / (π √ν)`. -/
theorem r3EndpointSafeProjected_kernelPrimitive_eq {nu : ℝ} (hnu : 0 < nu) {T : ℝ}
    (hT : 0 ≤ T) :
    (r3EndpointSafeProjectedDuhamelContract hnu).kernelPrimitive T =
      T + (Real.pi * Real.sqrt nu)⁻¹ * Real.sqrt T := by
  have hsqrtc : Real.sqrt ((2 * Real.pi) ^ 2 * nu) = 2 * Real.pi * Real.sqrt nu := by
    rw [Real.sqrt_mul (by positivity) nu, Real.sqrt_sq (by positivity)]
  -- interval integrability of the inverse square root
  have hsqrtInt : IntervalIntegrable (fun τ : ℝ => (Real.sqrt τ)⁻¹) volume 0 T := by
    have hrpow : IntervalIntegrable (fun τ : ℝ => τ ^ (-1 / 2 : ℝ)) volume 0 T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    refine hrpow.congr ?_
    intro τ hτ
    have hτ0 : 0 ≤ τ := by
      rw [Set.uIoc_of_le hT] at hτ
      exact hτ.1.le
    change τ ^ (-1 / 2 : ℝ) = (Real.sqrt τ)⁻¹
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hτ0, Real.sqrt_eq_rpow]
  -- the safe kernel agrees with the explicit integrand on the integration interval
  have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) T,
      (r3EndpointSafeProjectedDuhamelContract hnu).safeKernel τ =
        1 + (2 * Real.pi * Real.sqrt nu)⁻¹ * (Real.sqrt τ)⁻¹ := by
    intro τ hτ
    have hker : (r3EndpointSafeProjectedDuhamelContract hnu).safeKernel τ =
        r3StokesH2H3TimeKernel nu τ := by
      show endpointSafePositiveMajorant (r3StokesH2H3TimeKernel nu) τ =
        r3StokesH2H3TimeKernel nu τ
      exact endpointSafePositiveMajorant_of_pos _ hτ.1
    rw [hker]
    unfold r3StokesH2H3TimeKernel r3StokesH2H3SmoothingScale
    rw [Real.sqrt_mul (mul_nonneg (by positivity) hnu.le) τ, hsqrtc, mul_inv]
  -- replace the safe kernel by the explicit integrand
  have hcongr : (r3EndpointSafeProjectedDuhamelContract hnu).kernelPrimitive T =
      ∫ τ in (0 : ℝ)..T, (1 + (2 * Real.pi * Real.sqrt nu)⁻¹ * (Real.sqrt τ)⁻¹) := by
    show (∫ τ in (0 : ℝ)..T, (r3EndpointSafeProjectedDuhamelContract hnu).safeKernel τ) = _
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun τ hτ => ?_)
    rw [Set.uIoc_of_le hT] at hτ
    exact hpoint τ hτ
  -- evaluate the inverse-square-root integral
  have hsqrtEval : (∫ τ in (0 : ℝ)..T, (Real.sqrt τ)⁻¹) = 2 * Real.sqrt T := by
    have hcong2 : (∫ τ in (0 : ℝ)..T, (Real.sqrt τ)⁻¹) =
        ∫ τ in (0 : ℝ)..T, τ ^ (-1 / 2 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun τ hτ => ?_)
      rw [Set.uIoc_of_le hT] at hτ
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hτ.1.le,
        Real.sqrt_eq_rpow]
    rw [hcong2, integral_rpow (Or.inl (by norm_num)),
      Real.zero_rpow (by norm_num : (-1 / 2 + 1 : ℝ) ≠ 0),
      show (-1 / 2 + 1 : ℝ) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
    ring
  rw [hcongr,
    intervalIntegral.integral_add intervalIntegrable_const
      (hsqrtInt.const_mul ((2 * Real.pi * Real.sqrt nu)⁻¹)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hsqrtEval]
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hν : Real.sqrt nu ≠ 0 := (Real.sqrt_pos.mpr hnu).ne'
  simp only [smul_eq_mul, sub_zero, mul_one]
  field_simp

/-- Pure algebra behind the lifespan choice: with `s = δ/(1+c+δ)` one has
`s² + c s = s (s + c) < δ` because `s ≤ δ < 1 + δ`. -/
theorem endpointSafe_lifespan_sq_add_lt {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    (δ / (1 + c + δ)) ^ 2 + c * (δ / (1 + c + δ)) < δ := by
  have hD : (0 : ℝ) < 1 + c + δ := by linarith
  set s : ℝ := δ / (1 + c + δ) with hs
  have hs0 : 0 < s := div_pos hδ hD
  have hsle : s ≤ δ := div_le_self hδ.le (by linarith)
  have hsD : s * (1 + c + δ) = δ := div_mul_cancel₀ δ hD.ne'
  have h1 : s * s ≤ s * δ := mul_le_mul_of_nonneg_left hsle hs0.le
  have h2 : s + s * c + s * δ = δ := by linear_combination hsD
  have h3 : s ^ 2 = s * s := sq s
  linarith

/-- The cumulative smoothing mass at the explicit lifespan is strictly below the smallness
threshold: `K(T₀) < δ`. -/
theorem r3EndpointSafeProjected_kernelPrimitive_mildLifespan_lt {nu r : ℝ} (hnu : 0 < nu)
    (hr : 0 ≤ r) :
    (r3EndpointSafeProjectedDuhamelContract hnu).kernelPrimitive (r3MildLifespan nu r) <
      r3MildSmallnessThreshold r := by
  have hδ : 0 < r3MildSmallnessThreshold r := r3MildSmallnessThreshold_pos hr
  have hc : 0 < (Real.pi * Real.sqrt nu)⁻¹ :=
    inv_pos.mpr (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hnu))
  have hD : (0 : ℝ) < 1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r := by
    linarith
  have hs0 : (0 : ℝ) ≤ r3MildSmallnessThreshold r /
      (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r) := (div_pos hδ hD).le
  have hunfold : r3MildLifespan nu r =
      (r3MildSmallnessThreshold r /
        (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r)) ^ 2 := rfl
  rw [hunfold, r3EndpointSafeProjected_kernelPrimitive_eq hnu (sq_nonneg _),
    Real.sqrt_sq hs0]
  exact endpointSafe_lifespan_sq_add_lt hc.le hδ

/--
**Explicit-lifespan local existence** on the complex Bessel-coordinate carrier: on the
horizon `T₀(ν, ‖u₀‖) = (δ/(1+(π√ν)⁻¹+δ))²` there is a mild solution with the ball bound
and ball uniqueness.
-/
theorem r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan {nu : ℝ} (hnu : 0 < nu)
    (u0 : R3HsVelocity 3) :
    ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu (r3MildLifespan nu ‖u0‖) u0 u ∧
      (∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), ‖u t‖ ≤ ‖u0‖ + 1) ∧
      ∀ v : ℝ → R3HsVelocity 3,
        IsR3EndpointSafeProjectedMildSolutionOn hnu (r3MildLifespan nu ‖u0‖) u0 v →
        (∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), ‖v t‖ ≤ ‖u0‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), v t = u t :=
  (r3EndpointSafeProjectedDuhamelContract hnu).exists_isMildSolutionOn_of_kernelPrimitive_lt
    (fun t x => norm_r3StokesH3Evolution_apply_le hnu.le t x) u0
    (r3MildLifespan_pos hnu (norm_nonneg u0))
    (r3EndpointSafeProjected_kernelPrimitive_mildLifespan_lt hnu (norm_nonneg u0))

/--
**Explicit-lifespan physically real local existence**: for real initial data the mild
solution on the explicit horizon is itself pointwise real.
-/
theorem r3EndpointSafeProjected_exists_realMildSolutionOn_mildLifespan {nu : ℝ}
    (hnu : 0 < nu) {u0 : R3HsVelocity 3} (hu0 : IsR3RealVelocity u0) :
    ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu (r3MildLifespan nu ‖u0‖) u0 u ∧
      (∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), ‖u t‖ ≤ ‖u0‖ + 1) ∧
      (∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), IsR3RealVelocity (u t)) ∧
      ∀ v : ℝ → R3HsVelocity 3,
        IsR3EndpointSafeProjectedMildSolutionOn hnu (r3MildLifespan nu ‖u0‖) u0 v →
        (∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), ‖v t‖ ≤ ‖u0‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖), v t = u t := by
  obtain ⟨u, hmild, hball, huniq⟩ :=
    r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan hnu u0
  refine ⟨u, hmild, hball, ?_, huniq⟩
  have hvmild := hmild.r3L2Conj_comp hnu hu0
  have hvball : ∀ t ∈ Icc (0 : ℝ) (r3MildLifespan nu ‖u0‖),
      ‖r3L2Conj (u t)‖ ≤ ‖u0‖ + 1 := fun t ht => by
    rw [norm_r3L2Conj]
    exact hball t ht
  have hfix := huniq (fun τ => r3L2Conj (u τ)) hvmild hvball
  intro t ht
  show r3L2Conj (u t) = u t
  exact hfix t ht

end

end MNS2
