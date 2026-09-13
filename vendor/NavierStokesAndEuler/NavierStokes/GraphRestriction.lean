import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Graph restriction and auxiliary averaging

Sections 8.1 and 11 of the candidate manuscript distinguish the pointwise
restriction of an auxiliary lift from its auxiliary average. This file proves
three independent facts:

* uniform pointwise majorants on a lift survive restriction to any graph;
* summable uniform majorants give convergent graph-restricted series;
* even a smooth periodic lift with zero auxiliary average can restrict to the
  constant function one on a prescribed graph.

The first derivative chain rule is also recorded. None of these statements
supplies the manuscript's claimed all-order residual estimates.
-/

noncomputable section

namespace NavierStokes.GraphRestriction

open scoped BigOperators

/-- Evaluate an auxiliary lift on a graph. -/
def pullback {X Y E : Type*} (F : X → Y → E) (γ : X → Y) (x : X) : E :=
  F x (γ x)

section UniformBounds

variable {X Y E : Type*} [NormedAddCommGroup E]

/-- The essential hypothesis is a bound at every auxiliary point. -/
theorem pullback_norm_le (F : X → Y → E) (γ : X → Y) (B : X → ℝ)
    (hF : ∀ x y, ‖F x y‖ ≤ B x) (x : X) :
    ‖pullback F γ x‖ ≤ B x :=
  hF x (γ x)

/-- Uniform errors also remain bounded on every graph. -/
theorem pullback_sub_norm_le (F G : X → Y → E) (γ : X → Y) (B : X → ℝ)
    (hFG : ∀ x y, ‖F x y - G x y‖ ≤ B x) (x : X) :
    ‖pullback F γ x - pullback G γ x‖ ≤ B x :=
  hFG x (γ x)

theorem pullback_sum {ι : Type*} (s : Finset ι) (F : ι → X → Y → E)
    (γ : X → Y) (x : X) :
    pullback (fun x y => ∑ i ∈ s, F i x y) γ x =
      ∑ i ∈ s, pullback (F i) γ x := rfl

/-- This is pointwise convergence on the physical graph under a genuinely
uniform, summable bound on the auxiliary lift. -/
theorem summable_pullback [CompleteSpace E] {ι : Type*}
    (F : ι → X → Y → E) (γ : X → Y) (B : ι → ℝ)
    (hB : Summable B) (hF : ∀ i x y, ‖F i x y‖ ≤ B i) (x : X) :
    Summable (fun i => pullback (F i) γ x) :=
  Summable.of_norm_bounded hB (fun i => hF i x (γ x))

/-- Quantitative control of a graph-restricted sum. The normed group need
not be complete for this bound; completeness in `summable_pullback` supplies
actual convergence. -/
theorem norm_tsum_pullback_le {ι : Type*}
    (F : ι → X → Y → E) (γ : X → Y) (B : ι → ℝ)
    (hB : Summable B) (hF : ∀ i x y, ‖F i x y‖ ≤ B i) (x : X) :
    ‖∑' i, pullback (F i) γ x‖ ≤ ∑' i, B i :=
  tsum_of_norm_bounded hB.hasSum (fun i => hF i x (γ x))

end UniformBounds

section Derivative

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph derivative includes the derivative in the auxiliary direction.
Here `D` is the complete derivative of the lift at the graph point. -/
theorem hasDerivAt_pullback (F : ℝ × A → E) (γ : ℝ → A)
    (x : ℝ) (γ' : A) (D : (ℝ × A) →L[ℝ] E)
    (hF : HasFDerivAt F D (x, γ x)) (hγ : HasDerivAt γ γ' x) :
    HasDerivAt (fun t => F (t, γ t)) (D (1, γ')) x := by
  exact hF.comp_hasDerivAt x ((hasDerivAt_id x).prodMk hγ)

/-- A derivative bound must account for the speed of the graph. -/
theorem graph_derivative_norm_le (D : (ℝ × A) →L[ℝ] E) (γ' : A) :
    ‖D (1, γ')‖ ≤ ‖D‖ * max 1 ‖γ'‖ := by
  simpa only [Prod.norm_def, norm_one] using D.le_opNorm (1, γ')

end Derivative

section ZeroMeanExample

/-- The normalized average on a two-dimensional torus of period `2π`.
Writing it as an iterated integral avoids imposing a quotient presentation.
The example below is periodic in each auxiliary coordinate. -/
def auxiliaryMean (f : (ℝ × ℝ) → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..(2 * Real.pi),
    ∫ y in (0 : ℝ)..(2 * Real.pi), f (y, z)) / (2 * Real.pi) ^ 2

/-- A lift adapted to an arbitrary prescribed graph. -/
def zeroMeanLift {X : Type*} (γ : X → ℝ × ℝ) (x : X) (y : ℝ × ℝ) : ℝ :=
  Real.cos (y.1 - (γ x).1)

theorem zeroMeanLift_periodic_first {X : Type*} (γ : X → ℝ × ℝ)
    (x : X) (y z : ℝ) :
    zeroMeanLift γ x (y + 2 * Real.pi, z) = zeroMeanLift γ x (y, z) := by
  unfold zeroMeanLift
  dsimp only
  rw [add_sub_right_comm, Real.cos_add_two_pi]

theorem zeroMeanLift_periodic_second {X : Type*} (γ : X → ℝ × ℝ)
    (x : X) (y z : ℝ) :
    zeroMeanLift γ x (y, z + 2 * Real.pi) = zeroMeanLift γ x (y, z) := rfl

theorem integral_shifted_cos (a : ℝ) :
    (∫ y in (0 : ℝ)..(2 * Real.pi), Real.cos (y - a)) = 0 := by
  rw [intervalIntegral.integral_comp_sub_right, integral_cos]
  simp only [zero_sub, Real.sin_two_pi_sub, Real.sin_neg, sub_self]

/-- Exact zero auxiliary mean, for every value of the physical variable. -/
theorem auxiliaryMean_zeroMeanLift {X : Type*} (γ : X → ℝ × ℝ) (x : X) :
    auxiliaryMean (zeroMeanLift γ x) = 0 := by
  unfold auxiliaryMean zeroMeanLift
  simp only [integral_shifted_cos, intervalIntegral.integral_zero, zero_div]

/-- Nevertheless, its graph restriction has value one everywhere. -/
theorem pullback_zeroMeanLift {X : Type*} (γ : X → ℝ × ℝ) (x : X) :
    pullback (zeroMeanLift γ) γ x = 1 := by
  simp only [pullback, zeroMeanLift, sub_self, Real.cos_zero]

/-- The example preserves the prescribed graph's differentiability order,
including smoothness when `n = ∞`. -/
theorem contDiff_zeroMeanLift {n : WithTop ℕ∞} (γ : ℝ → ℝ × ℝ)
    (hγ : ContDiff ℝ n γ) :
    ContDiff ℝ n
      (fun p : ℝ × (ℝ × ℝ) => zeroMeanLift γ p.1 p.2) := by
  unfold zeroMeanLift
  exact Real.contDiff_cos.comp
    ((contDiff_fst.comp contDiff_snd).sub
      ((contDiff_fst.comp hγ).comp contDiff_fst))

/-- For any prescribed graph, auxiliary mean cancellation alone cannot
imply cancellation after graph restriction. -/
theorem zero_mean_does_not_force_zero (γ : ℝ → ℝ × ℝ) :
    ¬ (∀ F : ℝ → (ℝ × ℝ) → ℝ,
      (∀ x, auxiliaryMean (F x) = 0) → ∀ x, pullback F γ x = 0) := by
  intro h
  have hzero := h (zeroMeanLift γ) (auxiliaryMean_zeroMeanLift γ) 0
  rw [pullback_zeroMeanLift] at hzero
  exact one_ne_zero hzero

end ZeroMeanExample

end NavierStokes.GraphRestriction
