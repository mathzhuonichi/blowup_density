import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A04 unit Z1 — ζ-regularized square-root division with a linear term

This is the pure scalar-calculus content of the manuscript's ζ device
(`paper/sections/appendix-a-local-theory.tex:139-146`; the same device is used
for the `L²` packet at `02-preliminaries.tex:140-143`, for the subcritical
bound at `04-whole-space.tex:100-102`, and for eq:RL2 at
`04-whole-space.tex:118-120`).  It realizes `research/A04/COMPARISON.md` unit
**Z1** in two directions: a *linear* term `K(t) E t` (so the regularized square
root obeys a Grönwall-ready linear differential inequality
`(√(E+ζ²))' ≤ K √(E+ζ²) + b`), and the integral form
`√(E t) ≤ √(E t₀) + ∫ (K √E + b)` with **no** initial vanishing `E t₀ = 0`.

No PDE, flow, pressure, or lifespan object appears; everything is `ℝ → ℝ`.

## Relation to `Paper1.sqrt_energy_le_primitive`

`NSFormalization.Paper1.sqrt_energy_le_primitive`
(`formalization/NSFormalization/Paper1/ScalarEnergy.lean:22`) is the template.
The lemmas here **generalize** it in the two directions above, but do **not
subsume** it — they also *restrict* in two ways, so the Paper 1 lemma is not a
corollary and both stay:

* `sqrt_le_primitive_linear` requires `b` (and `K`) `ContinuousOn` the interval;
  `sqrt_energy_le_primitive` asks nothing of `b` beyond nonnegativity on `Ioo`.
* it hard-codes the primitive as the Lebesgue interval integral
  `∫ s in t₀..x, (K √E + b)`; `sqrt_energy_le_primitive` takes an abstract
  primitive `N` with `HasDerivAt N (b t) t`, which is strictly more general (a
  derivative need not be the integrand of its own primitive without
  integrability).

## Hypotheses vs the manuscript

* The forward derivative is stated one-sided, `HasDerivWithinAt E (E' t) (Ici t) t`,
  weaker than a two-sided `HasDerivAt` and matching the manuscript's
  forward-in-time energy derivative (a consumer holding `HasDerivAt` passes
  `.hasDerivWithinAt`).
* `sqrt_le_primitive_linear` requires `E, K, b` `ContinuousOn (Icc t₀ t₁)`.  This
  is **stronger** than the paper, whose Grönwall step (`appendix-a:146`) only
  needs the coefficient `‖u‖²_{H²}` to be `L¹` in time.  Continuity is what the
  everywhere-defined-derivative antitone argument
  (`antitoneOn_of_hasDerivWithinAt_nonpos`, via the fundamental theorem of
  calculus for the primitive) needs; mere `IntervalIntegrable` coefficients give
  only an a.e. derivative, which this technique cannot use.  Along a classical
  solution these norms are continuous in time (unit **N1** of
  `research/A04/COMPARISON.md`), so the hypothesis is available where consumed.
  Nonnegativity of `K` and `b` is needed only at interior times (`Ioo t₀ t₁`);
  `E ≥ 0` is needed on the closed interval (it is used at `t₀`).
-/

namespace NSFormalization.Section4.A04

open Set MeasureTheory Topology

/-- **The ζ-regularized bound, purely algebraic** — no differentiability.

From `d ≤ 2 (K t · E t + b t · √(E t))` with `E t, K t, b t ≥ 0` and `ζ > 0`,
the regularized quotient obeys `d / (2 √(E t + ζ²)) ≤ K t · √(E t + ζ²) + b t`.
When `d = E' t` this is the inequality half of the manuscript's
`appendix-a:139-143` step; it does not use the derivative hypothesis. -/
theorem regularized_sqrt_bound {E K b : ℝ → ℝ} {t ζ d : ℝ}
    (hζ : 0 < ζ) (hEt : 0 ≤ E t) (hKt : 0 ≤ K t) (hbt : 0 ≤ b t)
    (hineq : d ≤ 2 * (K t * E t + b t * Real.sqrt (E t))) :
    d / (2 * Real.sqrt (E t + ζ ^ 2)) ≤ K t * Real.sqrt (E t + ζ ^ 2) + b t := by
  have hpos : 0 < E t + ζ ^ 2 := by positivity
  have hSpos : 0 < Real.sqrt (E t + ζ ^ 2) := Real.sqrt_pos.mpr hpos
  have hS2 : Real.sqrt (E t + ζ ^ 2) ^ 2 = E t + ζ ^ 2 := Real.sq_sqrt hpos.le
  have hle : Real.sqrt (E t) ≤ Real.sqrt (E t + ζ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg ζ])
  have h2 : b t * Real.sqrt (E t) ≤ b t * Real.sqrt (E t + ζ ^ 2) :=
    mul_le_mul_of_nonneg_left hle hbt
  have hKz : 0 ≤ K t * ζ ^ 2 := mul_nonneg hKt (sq_nonneg ζ)
  have hKS2 : K t * Real.sqrt (E t + ζ ^ 2) ^ 2 = K t * (E t + ζ ^ 2) := by rw [hS2]
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hSpos)]
  nlinarith [hineq, hKS2, h2, hKz]

/-- **Forward derivative of the ζ-regularized square root.**

If `E` has a forward derivative `E' t` at `t` and `E t ≥ 0`, then
`r ↦ √(E r + ζ²)` has forward derivative `E' t / (2 √(E t + ζ²))` for every
`ζ > 0`.  Independent of the bound. -/
theorem regularized_sqrt_hasDerivWithinAt {E E' : ℝ → ℝ} {t ζ : ℝ}
    (hζ : 0 < ζ) (hEt : 0 ≤ E t)
    (hdE : HasDerivWithinAt E (E' t) (Ici t) t) :
    HasDerivWithinAt (fun r => Real.sqrt (E r + ζ ^ 2))
      (E' t / (2 * Real.sqrt (E t + ζ ^ 2))) (Ici t) t := by
  have hpos : 0 < E t + ζ ^ 2 := by positivity
  exact (hdE.add_const (ζ ^ 2)).sqrt hpos.ne'

/-- **Combined:** the forward derivative together with its bound — the
manuscript's `appendix-a:139-143` step in one statement.  Consumers that need
only one half may use `regularized_sqrt_hasDerivWithinAt` or
`regularized_sqrt_bound` directly. -/
theorem regularized_sqrt_deriv {E E' K b : ℝ → ℝ} {t ζ : ℝ}
    (hζ : 0 < ζ) (hEt : 0 ≤ E t) (hKt : 0 ≤ K t) (hbt : 0 ≤ b t)
    (hdE : HasDerivWithinAt E (E' t) (Ici t) t)
    (hineq : E' t ≤ 2 * (K t * E t + b t * Real.sqrt (E t))) :
    HasDerivWithinAt (fun r => Real.sqrt (E r + ζ ^ 2))
        (E' t / (2 * Real.sqrt (E t + ζ ^ 2))) (Ici t) t
      ∧ E' t / (2 * Real.sqrt (E t + ζ ^ 2)) ≤
          K t * Real.sqrt (E t + ζ ^ 2) + b t :=
  ⟨regularized_sqrt_hasDerivWithinAt hζ hEt hdE,
    regularized_sqrt_bound hζ hEt hKt hbt hineq⟩

/-- The integrand of the primitive, `s ↦ K s · √(E s) + b s`, is
interval-integrable on `[t₀, t]` for every `t ∈ Icc t₀ t₁`.  This is the
integrability conjunct that A04's `highContinuationIntegral` asserts alongside
the bound (`research/A04/COMPARISON.md:72`); it is what makes the integral in
`sqrt_le_primitive_linear`'s conclusion the genuine Lebesgue integral rather
than Mathlib's junk `0`. -/
theorem primitive_integrand_intervalIntegrable {t₀ t₁ : ℝ} {E K b : ℝ → ℝ}
    (hE : ContinuousOn E (Icc t₀ t₁)) (hK : ContinuousOn K (Icc t₀ t₁))
    (hbc : ContinuousOn b (Icc t₀ t₁)) :
    ∀ t ∈ Icc t₀ t₁,
      IntervalIntegrable (fun s => K s * Real.sqrt (E s) + b s) volume t₀ t := by
  intro t ht
  exact (((hK.mul hE.sqrt).add hbc).mono
    (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1

/-- **ζ↓0 integral form.**

Under `E' ≤ 2 (K E + b √E)` with `E ≥ 0`, `K, b ≥ 0` (at interior times) and
continuity of the coefficients, the square root of the energy is controlled by
its initial value plus the primitive of `K √E + b`, with **no** assumption that
`E t₀ = 0`:  `√(E t) ≤ √(E t₀) + ∫_{t₀}^{t} (K √E + b)`.

The proof regularizes `√(E + δ²)`, shows the regularized difference is antitone
(its forward derivative is `≤ K √E + b`, exactly the integrand), then lets
`δ ↓ 0`. -/
theorem sqrt_le_primitive_linear {t₀ t₁ : ℝ} {E E' K b : ℝ → ℝ}
    (ht : t₀ ≤ t₁)
    (hE : ContinuousOn E (Icc t₀ t₁))
    (hK : ContinuousOn K (Icc t₀ t₁))
    (hbc : ContinuousOn b (Icc t₀ t₁))
    (hEnonneg : ∀ t ∈ Icc t₀ t₁, 0 ≤ E t)
    (hKnonneg : ∀ t ∈ Ioo t₀ t₁, 0 ≤ K t)
    (hbnonneg : ∀ t ∈ Ioo t₀ t₁, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo t₀ t₁, HasDerivAt E (E' t) t)
    (hineq : ∀ t ∈ Ioo t₀ t₁,
      E' t ≤ 2 * (K t * E t + b t * Real.sqrt (E t))) :
    ∀ t ∈ Icc t₀ t₁,
      Real.sqrt (E t) ≤
        Real.sqrt (E t₀) + ∫ s in t₀..t, (K s * Real.sqrt (E s) + b s) := by
  -- The integrand and its primitive.
  let g : ℝ → ℝ := fun s => K s * Real.sqrt (E s) + b s
  let N : ℝ → ℝ := fun x => Real.sqrt (E t₀) + ∫ s in t₀..x, g s
  have hg : ContinuousOn g (Icc t₀ t₁) := (hK.mul hE.sqrt).add hbc
  have hgii : IntervalIntegrable g volume t₀ t₁ :=
    primitive_integrand_intervalIntegrable hE hK hbc t₁ ⟨ht, le_rfl⟩
  have hN : ContinuousOn N (Icc t₀ t₁) := by
    refine continuousOn_const.add ?_
    have h := intervalIntegral.continuousOn_primitive_interval' hgii left_mem_uIcc
    rwa [uIcc_of_le ht] at h
  intro t hmem
  apply le_of_forall_pos_le_add
  intro δ hδ
  let G : ℝ → ℝ := fun x => Real.sqrt (E x + δ ^ 2) - N x
  have hgcont : ContinuousOn G (Icc t₀ t₁) :=
    ((hE.add continuousOn_const).sqrt).sub hN
  -- Forward derivative of G on the interior.
  have hderiv : ∀ x ∈ interior (Icc t₀ t₁),
      HasDerivWithinAt G (E' x / (2 * Real.sqrt (E x + δ ^ 2)) - g x)
        (interior (Icc t₀ t₁)) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hEx : 0 ≤ E x := hEnonneg x (Ioo_subset_Icc_self hx)
    have hpos : 0 < E x + δ ^ 2 := by positivity
    have hΦ : HasDerivAt (fun r => Real.sqrt (E r + δ ^ 2))
        (E' x / (2 * Real.sqrt (E x + δ ^ 2))) x :=
      ((hdE x hx).add_const (δ ^ 2)).sqrt hpos.ne'
    have hii : IntervalIntegrable g volume t₀ x :=
      primitive_integrand_intervalIntegrable hE hK hbc x ⟨hx.1.le, hx.2.le⟩
    have hmeas : StronglyMeasurableAtFilter g (𝓝 x) :=
      ⟨Icc t₀ t₁, Icc_mem_nhds hx.1 hx.2, hg.aestronglyMeasurable measurableSet_Icc⟩
    have hcont : ContinuousAt g x := hg.continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hNd : HasDerivAt N (g x) x :=
      (intervalIntegral.integral_hasDerivAt_right hii hmeas hcont).const_add _
    exact (hΦ.sub hNd).hasDerivWithinAt
  -- The derivative is nonpositive: (√(E+δ²))' ≤ K √E + b = g.
  have hG : AntitoneOn G (Icc t₀ t₁) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁) hgcont hderiv
    intro x hx
    rw [interior_Icc] at hx
    have hxmem : x ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hx
    have hEx : 0 ≤ E x := hEnonneg x hxmem
    have hpos : 0 < E x + δ ^ 2 := by positivity
    have hSpos : 0 < Real.sqrt (E x + δ ^ 2) := Real.sqrt_pos.mpr hpos
    have hle : Real.sqrt (E x) ≤ Real.sqrt (E x + δ ^ 2) :=
      Real.sqrt_le_sqrt (by linarith [sq_nonneg δ])
    have hsqE : Real.sqrt (E x) * Real.sqrt (E x) = E x := Real.mul_self_sqrt hEx
    have hKx : 0 ≤ K x := hKnonneg x hx
    have hbx : 0 ≤ b x := hbnonneg x hx
    have hES : E x ≤ Real.sqrt (E x + δ ^ 2) * Real.sqrt (E x) := by
      nlinarith [hle, hsqE, Real.sqrt_nonneg (E x)]
    have h1 : K x * E x ≤ K x * (Real.sqrt (E x + δ ^ 2) * Real.sqrt (E x)) :=
      mul_le_mul_of_nonneg_left hES hKx
    have h2 : b x * Real.sqrt (E x) ≤ b x * Real.sqrt (E x + δ ^ 2) :=
      mul_le_mul_of_nonneg_left hle hbx
    have hdiv : E' x / (2 * Real.sqrt (E x + δ ^ 2)) ≤ K x * Real.sqrt (E x) + b x := by
      rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hSpos)]
      nlinarith [hineq x hx, h1, h2]
    show E' x / (2 * Real.sqrt (E x + δ ^ 2)) - g x ≤ 0
    simp only [g]
    linarith [hdiv]
  -- Compare G t with G t₀ and let δ ↓ 0.
  have hbound : G t ≤ G t₀ := hG ⟨le_rfl, ht⟩ hmem hmem.1
  have hNt0 : N t₀ = Real.sqrt (E t₀) := by
    simp only [N, intervalIntegral.integral_same, add_zero]
  have hsqrtt0 : Real.sqrt (E t₀ + δ ^ 2) ≤ Real.sqrt (E t₀) + δ := by
    have hE0 : 0 ≤ E t₀ := hEnonneg t₀ ⟨le_rfl, ht⟩
    have key : E t₀ + δ ^ 2 ≤ (Real.sqrt (E t₀) + δ) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (E t₀), hδ.le, Real.sq_sqrt hE0]
    calc Real.sqrt (E t₀ + δ ^ 2)
        ≤ Real.sqrt ((Real.sqrt (E t₀) + δ) ^ 2) := Real.sqrt_le_sqrt key
      _ = Real.sqrt (E t₀) + δ :=
          Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) hδ.le)
  simp only [G] at hbound
  rw [hNt0] at hbound
  have hmono : Real.sqrt (E t) ≤ Real.sqrt (E t + δ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg δ])
  show Real.sqrt (E t) ≤ N t + δ
  linarith [hmono, hbound, hsqrtt0]

end NSFormalization.Section4.A04
