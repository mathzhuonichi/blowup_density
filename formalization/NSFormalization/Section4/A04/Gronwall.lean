import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Variable-coefficient Grönwall inequality (A04, unit G3)

This module supplies the **continuous variable-coefficient Grönwall inequality** in
integral form, together with the differential form and the `A04` corollary shape.
It is pure real analysis: no PDE objects, no `ClassicalSolutionR`.

## What is and is not already in tree

Mathlib's ODE Grönwall lemmas
(`Mathlib/Analysis/ODE/Gronwall.lean`, `le_gronwallBound_of_liminf_deriv_right_le`,
`norm_le_gronwallBound_of_norm_deriv_right_le`) all take a **constant** coefficient
`K`, giving the weaker bound `exp (K * (t - t₀))`; `Mathlib/Analysis/ODE/DiscreteGronwall.lean`
is discrete.  A genuinely variable-coefficient Grönwall by the *same* integrating-factor
route already exists in the vendored package,
`EulerOrdinarySobolev.variable_linear_stability`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryVariableGronwall.lean:14`) — but it is
homogeneous (`b = 0`, hence needs no sign condition on the coefficient), only in
differential form, anchored at `t₀ = 0`, and bundles the coefficient as a `C(Icc 0 T, ℝ)`
with `extendPath`/`realIntegral` plumbing, so it cannot state the inhomogeneous `+ b` term
that `higherOrderBound` requires.  The results here are the **inhomogeneous, integral-form**
version with a **general base point `t₀`** and a plain `ContinuousOn` coefficient: they
share the integrating-factor idea but are not derivable from the vendored lemma (the missing
`b` term is the obstruction; see `research/A04/ATTEMPTS_G3.md`).

The sharp bound is `exp (∫ c)`, not `exp (K·(t − t₀))`.  This is what the whole-space
continuation argument of `paper/sections/appendix-a-local-theory.tex`
(eq:highcontinuation, the Grönwall consequence at `:146-147`) needs: there the coefficient
`C_{m,ν} ‖u(t)‖²_{H²}` is only globally `L¹` in time, so a constant-`K` bound would be
false — yet on every compact subinterval of the existence interval `(0, S)` that same
coefficient is in fact **continuous**, which is exactly the regularity assumed below.

## Hypotheses actually used

`y`, `c`, `b` are required `ContinuousOn (Icc t₀ t₁)`, with `c` and `b` nonnegative there;
`y ≥ 0` is **not** needed.  Continuity on each compact subinterval (rather than mere
`L¹`/local integrability) is what the `A04` application provides, because on the open
existence interval the datum path `u` and the force `f` are continuous in time (indeed
`C^∞`), so `‖u(t)‖²_{H²}` and `‖f(t)‖_{H^m}` are continuous on each `[t₀, t₁] ⊂ (0, S)`.
The global `L¹`-in-time character of the coefficient enters only at the assembly stage
(the supremum over `t₁ ↑ S`), not inside these lemmas.  See `research/A04/ATTEMPTS_G3.md`.

## Main results

* `gronwall_integral` — integral form.
* `gronwall_deriv` — differential form, reduced to the integral form via FTC.
* `gronwall_integral_mul` — the `A04` corollary `c = Cgron * k`.
-/

open Set intervalIntegral MeasureTheory
open scoped Topology

namespace NSFormalization.Section4.A04

/-- **Variable-coefficient Grönwall inequality, integral form.**

If `y`, `c`, `b` are continuous on `[t₀, t₁]`, `c` and `b` are nonnegative, and
`y t ≤ y t₀ + ∫_{t₀}^t (c s * y s + b s)` for all `t ∈ [t₀, t₁]`, then
`y t ≤ (y t₀ + ∫_{t₀}^t b) * exp (∫_{t₀}^t c)`.

The proof is the classical integrating-factor argument: the function
`F u = (y t₀ + ∫_{t₀}^u (c y + b)) * exp (-∫_{t₀}^u c) - ∫_{t₀}^u (exp(-∫_{t₀}^s c) * b s)`
has nonpositive derivative because `c ≥ 0` and `y ≤ y t₀ + ∫(c y + b)`, hence is
antitone; `F t ≤ F t₀ = y t₀` then rearranges to the claimed bound using
`exp(-∫c) ≤ 1` and `b ≥ 0`. -/
theorem gronwall_integral {t₀ t₁ : ℝ} {y c b : ℝ → ℝ} (ht : t₀ ≤ t₁)
    (hy : ContinuousOn y (Icc t₀ t₁))
    (hc : ContinuousOn c (Icc t₀ t₁)) (hb : ContinuousOn b (Icc t₀ t₁))
    (hcnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ c t) (hbnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ b t)
    (hstep : ∀ t ∈ Icc t₀ t₁, y t ≤ y t₀ + ∫ s in t₀..t, (c s * y s + b s)) :
    ∀ t ∈ Icc t₀ t₁,
      y t ≤ (y t₀ + ∫ s in t₀..t, b s) * Real.exp (∫ s in t₀..t, c s) := by
  have hgc : ContinuousOn (fun s => c s * y s + b s) (Icc t₀ t₁) := (hc.mul hy).add hb
  have hCcont : ContinuousOn (fun u => ∫ s in t₀..u, c s) (Icc t₀ t₁) := by
    have h := continuousOn_primitive_interval' (μ := volume)
      (hc.intervalIntegrable_of_Icc ht) left_mem_uIcc
    rwa [uIcc_of_le ht] at h
  have hEbc : ContinuousOn (fun s => Real.exp (-(∫ r in t₀..s, c r)) * b s) (Icc t₀ t₁) :=
    (Real.continuous_exp.comp_continuousOn hCcont.neg).mul hb
  -- FTC-1 primitive helper: the indefinite integral of a continuous integrand is
  -- differentiable at every interior point, with the integrand as derivative.
  have hprim : ∀ (g : ℝ → ℝ), ContinuousOn g (Icc t₀ t₁) →
      ∀ x ∈ Ioo t₀ t₁, HasDerivAt (fun u => ∫ s in t₀..u, g s) (g x) x := by
    intro g hg x hx
    have hII : IntervalIntegrable g volume t₀ x :=
      (hg.mono (Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le
    have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
      (hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    exact integral_hasDerivAt_right hII hmeas (hg.continuousAt (Icc_mem_nhds hx.1 hx.2))
  have hprimcont : ∀ (g : ℝ → ℝ), ContinuousOn g (Icc t₀ t₁) →
      ContinuousOn (fun u => ∫ s in t₀..u, g s) (Icc t₀ t₁) := by
    intro g hg
    have h := continuousOn_primitive_interval' (μ := volume)
      (hg.intervalIntegrable_of_Icc ht) left_mem_uIcc
    rwa [uIcc_of_le ht] at h
  -- The integrating-factor combination.
  set F : ℝ → ℝ := fun u =>
    (y t₀ + ∫ s in t₀..u, (c s * y s + b s)) * Real.exp (-(∫ s in t₀..u, c s))
      - ∫ s in t₀..u, (Real.exp (-(∫ r in t₀..s, c r)) * b s) with hFdef
  have hFcont : ContinuousOn F (Icc t₀ t₁) := by
    rw [hFdef]
    exact ((continuousOn_const.add (hprimcont _ hgc)).mul
      (Real.continuous_exp.comp_continuousOn hCcont.neg)).sub (hprimcont _ hEbc)
  have hanti : AntitoneOn F (Icc t₀ t₁) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁) hFcont
    · intro x hxi
      have hx : x ∈ Ioo t₀ t₁ := by simpa only [interior_Icc] using hxi
      have hY : HasDerivAt (fun u => y t₀ + ∫ s in t₀..u, (c s * y s + b s))
          (c x * y x + b x) x := (hprim (fun s => c s * y s + b s) hgc x hx).const_add (y t₀)
      have hC : HasDerivAt (fun u => ∫ s in t₀..u, c s) (c x) x := hprim c hc x hx
      have hE : HasDerivAt (fun u => Real.exp (-(∫ s in t₀..u, c s)))
          (Real.exp (-(∫ s in t₀..x, c s)) * -(c x)) x := hC.neg.exp
      have hK : HasDerivAt (fun u => ∫ s in t₀..u, (Real.exp (-(∫ r in t₀..s, c r)) * b s))
          (Real.exp (-(∫ r in t₀..x, c r)) * b x) x :=
        hprim (fun s => Real.exp (-(∫ r in t₀..s, c r)) * b s) hEbc x hx
      rw [hFdef]
      exact ((hY.mul hE).sub hK).hasDerivWithinAt
    · intro x hxi
      have hx : x ∈ Ioo t₀ t₁ := by simpa only [interior_Icc] using hxi
      have hxIcc : x ∈ Icc t₀ t₁ := ⟨hx.1.le, hx.2.le⟩
      have hcx : 0 ≤ c x := hcnn x hxIcc
      have hyY : y x ≤ y t₀ + ∫ s in t₀..x, (c s * y s + b s) := hstep x hxIcc
      have hepos : 0 < Real.exp (-(∫ s in t₀..x, c s)) := Real.exp_pos _
      nlinarith [mul_nonneg (mul_nonneg hepos.le hcx) (sub_nonneg.mpr hyY), hepos.le, hcx]
  -- Assemble the bound.
  intro t ht'
  have hFbound : F t ≤ F t₀ := hanti ⟨le_rfl, ht⟩ ht' ht'.1
  have hFt : F t = (y t₀ + ∫ s in t₀..t, (c s * y s + b s)) * Real.exp (-(∫ s in t₀..t, c s))
      - ∫ s in t₀..t, (Real.exp (-(∫ r in t₀..s, c r)) * b s) := by rw [hFdef]
  have hFt0 : F t₀ = y t₀ := by
    rw [hFdef]
    simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, add_zero, mul_one, sub_zero]
  rw [hFt, hFt0] at hFbound
  have hA : (y t₀ + ∫ s in t₀..t, (c s * y s + b s)) * Real.exp (-(∫ s in t₀..t, c s))
      ≤ y t₀ + ∫ s in t₀..t, (Real.exp (-(∫ r in t₀..s, c r)) * b s) := by linarith
  -- `∫ (exp(-∫c) * b) ≤ ∫ b`, since `exp(-∫c) ≤ 1` and `b ≥ 0`.
  have hJIb : (∫ s in t₀..t, (Real.exp (-(∫ r in t₀..s, c r)) * b s)) ≤ ∫ s in t₀..t, b s := by
    apply integral_mono_on ht'.1
      ((hEbc.mono (Icc_subset_Icc le_rfl ht'.2)).intervalIntegrable_of_Icc ht'.1)
      ((hb.mono (Icc_subset_Icc le_rfl ht'.2)).intervalIntegrable_of_Icc ht'.1)
    intro x hx
    have hxIcc : x ∈ Icc t₀ t₁ := ⟨hx.1, hx.2.trans ht'.2⟩
    have hcnonneg : (0 : ℝ) ≤ ∫ r in t₀..x, c r :=
      integral_nonneg hx.1 (fun u hu => hcnn u ⟨hu.1, hu.2.trans hxIcc.2⟩)
    have hle1 : Real.exp (-(∫ r in t₀..x, c r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-(∫ r in t₀..x, c r)) * b x
        ≤ 1 * b x := mul_le_mul_of_nonneg_right hle1 (hbnn x hxIcc)
      _ = b x := one_mul _
  -- Multiply `hA` by `exp (∫ c) > 0` and chain.
  have h2 : y t₀ + ∫ s in t₀..t, (c s * y s + b s) ≤
      (y t₀ + ∫ s in t₀..t, (Real.exp (-(∫ r in t₀..s, c r)) * b s)) *
        Real.exp (∫ s in t₀..t, c s) := by
    have hmul := mul_le_mul_of_nonneg_right hA (Real.exp_pos (∫ s in t₀..t, c s)).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  have h3 : (y t₀ + ∫ s in t₀..t, (Real.exp (-(∫ r in t₀..s, c r)) * b s)) *
        Real.exp (∫ s in t₀..t, c s) ≤
      (y t₀ + ∫ s in t₀..t, b s) * Real.exp (∫ s in t₀..t, c s) :=
    mul_le_mul_of_nonneg_right (by linarith [hJIb]) (Real.exp_pos _).le
  have hstep_t : y t ≤ y t₀ + ∫ s in t₀..t, (c s * y s + b s) := hstep t ht'
  linarith [hstep_t, h2, h3]

/-- **Variable-coefficient Grönwall inequality, differential form.**

If `y` is continuous on `[t₀, t₁]` with a right derivative `y'` on `(t₀, t₁)`,
`y'` is interval integrable, `c` and `b` are continuous and nonnegative, and
`y' x ≤ c x * y x + b x` on `(t₀, t₁)`, then the same exponential bound holds.
Reduced to `gronwall_integral` through the fundamental theorem of calculus. -/
theorem gronwall_deriv {t₀ t₁ : ℝ} {y y' c b : ℝ → ℝ} (ht : t₀ ≤ t₁)
    (hy : ContinuousOn y (Icc t₀ t₁))
    (hc : ContinuousOn c (Icc t₀ t₁)) (hb : ContinuousOn b (Icc t₀ t₁))
    (hcnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ c t) (hbnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ b t)
    (hderiv : ∀ x ∈ Ioo t₀ t₁, HasDerivWithinAt y (y' x) (Ici x) x)
    (hy'int : IntervalIntegrable y' volume t₀ t₁)
    (hineq : ∀ x ∈ Ioo t₀ t₁, y' x ≤ c x * y x + b x) :
    ∀ t ∈ Icc t₀ t₁,
      y t ≤ (y t₀ + ∫ s in t₀..t, b s) * Real.exp (∫ s in t₀..t, c s) := by
  have hgc : ContinuousOn (fun s => c s * y s + b s) (Icc t₀ t₁) := (hc.mul hy).add hb
  refine gronwall_integral ht hy hc hb hcnn hbnn ?_
  intro t ht'
  -- `y t - y t₀ = ∫ y'` by FTC, and `∫ y' ≤ ∫ (c y + b)` by monotonicity.
  have hle_uIcc : (uIcc t₀ t) ⊆ uIcc t₀ t₁ :=
    uIcc_subset_uIcc_left (by rw [uIcc_of_le ht]; exact ⟨ht'.1, ht'.2⟩)
  have hFTC : ∫ s in t₀..t, y' s = y t - y t₀ :=
    integral_eq_sub_of_hasDeriv_right_of_le ht'.1 (hy.mono (Icc_subset_Icc le_rfl ht'.2))
      (fun x hx => (hderiv x ⟨hx.1, hx.2.trans_le ht'.2⟩).mono Ioi_subset_Ici_self)
      (hy'int.mono_set hle_uIcc)
  have hmono : (∫ s in t₀..t, y' s) ≤ ∫ s in t₀..t, (c s * y s + b s) :=
    integral_mono_on_of_le_Ioo ht'.1 (hy'int.mono_set hle_uIcc)
      ((hgc.mono (Icc_subset_Icc le_rfl ht'.2)).intervalIntegrable_of_Icc ht'.1)
      (fun x hx => hineq x ⟨hx.1, hx.2.trans_le ht'.2⟩)
  rw [hFTC] at hmono
  linarith

/-- **`A04` corollary shape.**  With the coefficient of the form `Cgron * k` where
`k ≥ 0` is continuous and `Cgron ≥ 0`, the bound reads
`y t ≤ (y t₀ + ∫ b) * exp (Cgron * ∫ k)`.  This is `higherOrderBound`-ready:
`k` will be `‖u(·)‖²_{H²}` and `b` will be `‖f(·)‖_{H^m}`. -/
theorem gronwall_integral_mul {t₀ t₁ Cgron : ℝ} {y k b : ℝ → ℝ} (ht : t₀ ≤ t₁)
    (hCgron : 0 ≤ Cgron)
    (hy : ContinuousOn y (Icc t₀ t₁))
    (hk : ContinuousOn k (Icc t₀ t₁)) (hb : ContinuousOn b (Icc t₀ t₁))
    (hknn : ∀ t ∈ Icc t₀ t₁, 0 ≤ k t) (hbnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ b t)
    (hstep : ∀ t ∈ Icc t₀ t₁, y t ≤ y t₀ + ∫ s in t₀..t, (Cgron * k s * y s + b s)) :
    ∀ t ∈ Icc t₀ t₁,
      y t ≤ (y t₀ + ∫ s in t₀..t, b s) * Real.exp (Cgron * ∫ s in t₀..t, k s) := by
  intro t ht'
  have h := gronwall_integral (c := fun s => Cgron * k s) ht hy
    (continuousOn_const.mul hk) hb
    (fun s hs => mul_nonneg hCgron (hknn s hs)) hbnn hstep t ht'
  rwa [intervalIntegral.integral_const_mul] at h

end NSFormalization.Section4.A04
