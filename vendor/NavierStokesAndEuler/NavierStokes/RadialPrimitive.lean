import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.Ring

/-!
# An actual compact radial primitive

The cutoff is the interval integral of a normalized compactly supported density.
All integrals below are genuine Lebesgue interval integrals. No inverse operator
or antiderivative is assumed. This is the scalar, unshifted part of Definition
9.6; Fourier estimates for the translated auxiliary-torus integral are separate.
-/

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff Interval

namespace NavierStokes.RadialPrimitive

/-- The ordinary radial primitive, with a specified lower endpoint. -/
def primitive (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ s in a..x, f s

/-- The mass removed by compactification. -/
def mass (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ s in a..b, f s

/-- The cutoff constructed from its density, rather than assumed to exist. -/
def cutoff (a : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ := primitive a ρ

/-- The compact primitive `I f - η J f`, with `η = I ρ`. -/
def compactPrimitive (a b : ℝ) (ρ f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => primitive a f x - cutoff a ρ x * mass a b f

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (primitive a f) (f x) x :=
  (hf.integral_hasStrictDerivAt a x).hasDerivAt

theorem cutoff_hasDerivAt {ρ : ℝ → ℝ} (hρ : Continuous ρ) (a x : ℝ) :
    HasDerivAt (cutoff a ρ) (ρ x) x :=
  primitive_hasDerivAt hρ a x

/-- Exact reconstruction with the mass defect. -/
theorem compactPrimitive_hasDerivAt {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (a b x : ℝ) :
    HasDerivAt (compactPrimitive a b ρ f) (f x - ρ x * mass a b f) x :=
  (primitive_hasDerivAt hf a x).sub ((cutoff_hasDerivAt hρ a x).mul_const _)

theorem deriv_compactPrimitive {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (a b x : ℝ) :
    deriv (compactPrimitive a b ρ f) x = f x - ρ x * mass a b f :=
  (compactPrimitive_hasDerivAt hρ hf a b x).deriv

theorem primitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (primitive a f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (primitive_hasDerivAt hf.continuous a x).differentiableAt, ?_⟩
  have hderiv : deriv (primitive a f) = f :=
    funext fun x => (primitive_hasDerivAt hf.continuous a x).deriv
  rw [hderiv]
  exact hf

theorem cutoff_contDiff {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (a : ℝ) :
    ContDiff ℝ ∞ (cutoff a ρ) := primitive_contDiff hρ a

theorem compactPrimitive_contDiff {ρ f : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (compactPrimitive a b ρ f) :=
  (primitive_contDiff hf a).sub ((cutoff_contDiff hρ a).mul contDiff_const)

/-- A continuous function supported in a closed interval also vanishes at its endpoints. -/
theorem support_subset_open_interval {a b : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hs : support f ⊆ Icc a b) : support f ⊆ Ioo a b := by
  simpa only [interior_Icc] using hf.isOpen_support.subset_interior_iff.mpr hs

theorem primitive_eq_zero_of_le {a b x : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hs : support f ⊆ Icc a b) (hx : x ≤ a) :
    primitive a f x = 0 := by
  have hzero : EqOn f (fun _ => 0) (uIcc a x) := by
    intro s hmem
    rw [uIcc_of_ge hx] at hmem
    by_contra hne
    exact (not_lt_of_ge hmem.2) ((support_subset_open_interval hf hs hne).1)
  change (∫ s in a..x, f s) = 0
  rw [intervalIntegral.integral_congr hzero]
  exact intervalIntegral.integral_zero

theorem integral_right_eq_zero {a b x : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hs : support f ⊆ Icc a b) (hx : b ≤ x) :
    (∫ s in b..x, f s) = 0 := by
  have hzero : EqOn f (fun _ => 0) (uIcc b x) := by
    intro s hmem
    rw [uIcc_of_le hx] at hmem
    by_contra hne
    exact (not_lt_of_ge hmem.1) ((support_subset_open_interval hf hs hne).2)
  rw [intervalIntegral.integral_congr hzero]
  exact intervalIntegral.integral_zero

theorem primitive_eq_mass_of_ge {a b x : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hs : support f ⊆ Icc a b) (hx : b ≤ x) :
    primitive a f x = mass a b f := by
  change (∫ s in a..x, f s) = ∫ s in a..b, f s
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable a b) (hf.intervalIntegrable b x),
    integral_right_eq_zero hf hs hx, add_zero]

theorem cutoff_eq_zero_of_le {a b x : ℝ} {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hs : support ρ ⊆ Icc a b) (hx : x ≤ a) :
    cutoff a ρ x = 0 := primitive_eq_zero_of_le hρ hs hx

theorem cutoff_eq_one_of_ge {a b x : ℝ} {ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hs : support ρ ⊆ Icc a b)
    (hm : mass a b ρ = 1) (hx : b ≤ x) : cutoff a ρ x = 1 := by
  change primitive a ρ x = 1
  rw [primitive_eq_mass_of_ge hρ hs hx, hm]

theorem compactPrimitive_eq_zero_of_le {a b x : ℝ} {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f)
    (hρs : support ρ ⊆ Icc a b) (hfs : support f ⊆ Icc a b) (hx : x ≤ a) :
    compactPrimitive a b ρ f x = 0 := by
  simp only [compactPrimitive, primitive_eq_zero_of_le hf hfs hx,
    cutoff_eq_zero_of_le hρ hρs hx, zero_mul, sub_self]

theorem compactPrimitive_eq_zero_of_ge {a b x : ℝ} {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f)
    (hρs : support ρ ⊆ Icc a b) (hfs : support f ⊆ Icc a b)
    (hm : mass a b ρ = 1) (hx : b ≤ x) : compactPrimitive a b ρ f x = 0 := by
  simp only [compactPrimitive, primitive_eq_mass_of_ge hf hfs hx,
    cutoff_eq_one_of_ge hρ hρs hm hx, one_mul, sub_self]

theorem compactPrimitive_support_subset {a b : ℝ} {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f)
    (hρs : support ρ ⊆ Icc a b) (hfs : support f ⊆ Icc a b)
    (hm : mass a b ρ = 1) : support (compactPrimitive a b ρ f) ⊆ Icc a b := by
  intro x hx
  change compactPrimitive a b ρ f x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (compactPrimitive_eq_zero_of_le hρ hf hρs hfs (le_of_not_ge h))
  · by_contra h
    exact hx (compactPrimitive_eq_zero_of_ge hρ hf hρs hfs hm (le_of_not_ge h))

theorem compactPrimitive_hasCompactSupport {a b : ℝ} {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f)
    (hρs : support ρ ⊆ Icc a b) (hfs : support f ⊆ Icc a b)
    (hm : mass a b ρ = 1) : HasCompactSupport (compactPrimitive a b ρ f) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (compactPrimitive_support_subset hρ hf hρs hfs hm)

/-- A zero-mass source has an exact compact antiderivative. -/
theorem compactPrimitive_hasDerivAt_of_mass_zero {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (a b x : ℝ) (hm : mass a b f = 0) :
    HasDerivAt (compactPrimitive a b ρ f) (f x) x := by
  simpa only [hm, mul_zero, sub_zero] using compactPrimitive_hasDerivAt hρ hf a b x

/-- Compactification is the ordinary primitive of the mass-corrected source. -/
theorem compactPrimitive_eq_primitive_corrected {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (a b x : ℝ) :
    compactPrimitive a b ρ f x =
      primitive a (fun s => f s - ρ s * mass a b f) x := by
  unfold compactPrimitive cutoff primitive
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable a x)
    ((hρ.fun_mul continuous_const).intervalIntegrable a x), intervalIntegral.integral_mul_const]

theorem mass_corrected_eq_zero {ρ f : ℝ → ℝ}
    (hρ : Continuous ρ) (hf : Continuous f) (a b : ℝ) (hm : mass a b ρ = 1) :
    mass a b (fun s => f s - ρ s * mass a b f) = 0 := by
  change (∫ s in a..b, f s - ρ s * mass a b f) = 0
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable a b)
    ((hρ.fun_mul continuous_const).intervalIntegrable a b), intervalIntegral.integral_mul_const]
  change mass a b f - mass a b ρ * mass a b f = 0
  rw [hm, one_mul, sub_self]

/-- The reconstruction is linear in the source, with the cutoff held fixed. -/
theorem compactPrimitive_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b x : ℝ) (ρ : ℝ → ℝ) :
    compactPrimitive a b ρ (fun s => f s + g s) x =
      compactPrimitive a b ρ f x + compactPrimitive a b ρ g x := by
  unfold compactPrimitive primitive mass
  rw [intervalIntegral.integral_add (hf.intervalIntegrable a x) (hg.intervalIntegrable a x),
    intervalIntegral.integral_add (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)]
  ring

theorem compactPrimitive_const_mul (a b x c : ℝ) (ρ f : ℝ → ℝ) :
    compactPrimitive a b ρ (fun s => c * f s) x = c * compactPrimitive a b ρ f x := by
  unfold compactPrimitive primitive mass
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Differentiation of an actual parameter integral under a uniform local derivative bound.
The bound is only required on the fixed interval of integration. -/
theorem primitive_hasDerivAt_parameter {F F' : ℝ → ℝ → ℝ} {p₀ ε : ℝ}
    (hε : 0 < ε) (hF : ∀ p, Continuous (F p)) (hF' : Continuous (F' p₀))
    (hd : ∀ s p, p ∈ Metric.ball p₀ ε → HasDerivAt (fun q => F q s) (F' p s) p)
    (a x C : ℝ)
    (hb : ∀ s ∈ uIcc a x, ∀ p ∈ Metric.ball p₀ ε, |F' p s| ≤ C) :
    HasDerivAt (fun p => primitive a (F p) x) (primitive a (F' p₀) x) p₀ := by
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := fun _ => C) (Metric.ball_mem_nhds _ hε)
    (Filter.Eventually.of_forall fun p => (hF p).aestronglyMeasurable)
    ((hF p₀).intervalIntegrable a x) hF'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs p hp => by
      simpa only [Real.norm_eq_abs] using hb s (uIoc_subset_uIcc hs) p hp)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun s _ p hp => hd s p hp)).2

/-- With fixed endpoints and cutoff, parameter differentiation commutes with
the explicitly constructed compact primitive. -/
theorem compactPrimitive_hasDerivAt_parameter {F F' : ℝ → ℝ → ℝ} {p₀ ε : ℝ}
    (hε : 0 < ε) (hF : ∀ p, Continuous (F p)) (hF' : Continuous (F' p₀))
    (hd : ∀ s p, p ∈ Metric.ball p₀ ε → HasDerivAt (fun q => F q s) (F' p s) p)
    (a b x C : ℝ) (ρ : ℝ → ℝ)
    (hb : ∀ s ∈ uIcc a x ∪ uIcc a b,
      ∀ p ∈ Metric.ball p₀ ε, |F' p s| ≤ C) :
    HasDerivAt (fun p => compactPrimitive a b ρ (F p) x)
      (compactPrimitive a b ρ (F' p₀) x) p₀ := by
  have hx := primitive_hasDerivAt_parameter hε hF hF' hd a x C
    (fun s hs => hb s (Or.inl hs))
  have hm := primitive_hasDerivAt_parameter hε hF hF' hd a b C
    (fun s hs => hb s (Or.inr hs))
  exact hx.sub (HasDerivAt.const_mul (cutoff a ρ x) hm)

/-- Existence is witnessed by the integral formula, not postulated as an inverse axiom. -/
theorem exists_smooth_compact_primitive {a b : ℝ} {ρ f : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiff ℝ ∞ f)
    (hρs : support ρ ⊆ Icc a b) (hfs : support f ⊆ Icc a b)
    (hm : mass a b ρ = 1) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ support u ⊆ Icc a b ∧
      ∀ x, HasDerivAt u (f x - ρ x * mass a b f) x := by
  exact ⟨compactPrimitive a b ρ f, compactPrimitive_contDiff hρ hf a b,
    compactPrimitive_hasCompactSupport hρ.continuous hf.continuous hρs hfs hm,
    compactPrimitive_support_subset hρ.continuous hf.continuous hρs hfs hm,
    compactPrimitive_hasDerivAt hρ.continuous hf.continuous a b⟩

end NavierStokes.RadialPrimitive
