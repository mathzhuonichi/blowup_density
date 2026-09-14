import NSFormalization.Section4.A04.EnergyIdentityHigh
import NSFormalization.Section4.A04.Regularized

/-!
# A04 unit G2 — eq:highcontinuation before the limit (`regularizedNormDerivative`)

`paper/sections/appendix-a-local-theory.tex:139-145`:

> "Young's inequality and division by the regularized norm
> `(‖u‖²_{H^m}+ζ²)^{1/2}`, followed by `ζ↓0`, imply
> `(‖u‖_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖_{H^m} + ‖f‖_{H^m}`."

This module is the two things that happen between eq:Rhigh (`energyIdentityHigh`,
unit **G1**) and eq:highcontinuation, at each **fixed** `ζ > 0` — the only form in
which the manuscript's sentence is a theorem about a differentiable function.  It
realizes `research/A04/COMPARISON.md` §4 unit **G2** and, with the constant it
fixes, `Cgron`/`Cgron_pos`.

Two moves, both explicit here rather than hidden:

* **Young's absorption** (`young_high_real`, and its constant-specialized instance
  `young_absorption_high`).  eq:Rhigh's cross term is absorbed into the
  dissipation:
  `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} ≤ ν‖∇u‖²_{H^m} + C_{m,ν}‖u‖²_{H²}‖u‖²_{H^m}`,
  turning `½(‖u‖²_{H^m})' + ν‖∇u‖²_{H^m} ≤ C_m … + ‖f‖_{H^m}‖u‖_{H^m}` into
  `½(‖u‖²_{H^m})' ≤ C_{m,ν}‖u‖²_{H²}‖u‖²_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`.
  Carrying out the absorption fixes the constant `Cgron m ν = (Chigh m)²/(4ν)`
  (`research/A04/COMPARISON.md` §2; the manuscript displays no formula, so the
  spec pins none and this is the value the derivation gives).

* **The `ζ`-device** (`research/A04/COMPARISON.md` unit **Z1**,
  `Section4/A04/Regularized.lean`).  `energyIdentityHigh` gives a two-sided
  `HasDerivAt` of `r ↦ ‖u(r)‖²_{H^m}`; `HasDerivAt.sqrt` differentiates
  `r ↦ (‖u(r)‖²_{H^m}+ζ²)^{1/2}`, whose derivative is
  `(‖u‖²_{H^m})' / (2(‖u‖²_{H^m}+ζ²)^{1/2})`, and `regularized_sqrt_bound`
  (the freestanding scalar inequality of unit Z1) divides the absorbed bound by
  `2(‖u‖²_{H^m}+ζ²)^{1/2}`, using `‖u‖_{H^m} ≤ (‖u‖²_{H^m}+ζ²)^{1/2}` so the
  forcing term `‖f‖_{H^m}‖u‖_{H^m}/(…) ≤ ‖f‖_{H^m}` loses its `‖u‖_{H^m}` factor.

Note on the derivative side.  The spec field `regularizedNormDerivative`
(`research/A04/Spec.lean:459-470`) states a **two-sided** `HasDerivAt`, matching
`energyIdentityHigh`'s two-sided output; so this module uses the two-sided
`HasDerivAt.sqrt` directly rather than `Regularized.lean`'s one-sided
`regularized_sqrt_hasDerivWithinAt` (which gives only a `HasDerivWithinAt` on the
`Ici` half, and that single half alone cannot be upgraded to a `HasDerivAt` —
an `Ici`+`Iic` pair can, but `Regularized.lean` exports only the `Ici` half, so
routing through it would mean inventing an `Iic` twin for no gain when
`energyIdentityHigh` already hands over a two-sided `HasDerivAt`).  Only
`regularized_sqrt_bound`, the inequality half of unit Z1, is consumed here.

The `ζ↓0` limit itself is not taken here — after it, `‖u‖_{H^m}` need not be
differentiable at a zero, so the manuscript's `(‖u‖_{H^m})'` is a Dini
derivative; that step lands in the integrated field `highContinuationIntegral`
(`research/A04/Spec.lean:471-`), unit **G3**, via the `ζ↓0` integral form
`sqrt_le_primitive_linear` of unit Z1.
-/

noncomputable section

open Set
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

namespace NSFormalization.Section4.A04

/-- eq:highcontinuation's constant `C_{m,ν}` (`appendix-a-local-theory.tex:142-145`).

The manuscript displays no formula for `C_{m,ν}`; the Young absorption that
produces it (`young_high_real`) gives `C_{m,ν} = (C_m)²/(4ν)`, with `C_m = Chigh m`
the constant of eq:Rhigh.  This is the value the spec field `Cgron`
(`research/A04/Spec.lean:354`) leaves an implementer free to use and that
`research/A04/COMPARISON.md` §2 records. -/
def Cgron (m : ℕ) (ν : ℝ) : ℝ := Chigh m ^ 2 / (4 * ν)

/-- `Cgron` is strictly positive at every positive viscosity, from `Chigh_pos`
and `ν > 0`. -/
theorem Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν := by
  intro m ν hν
  exact div_pos (pow_pos (Chigh_pos m) 2) (by linarith)

/-- **Young's inequality, pure real arithmetic** (`appendix-a-local-theory.tex:139-140`).

From `½ d + ν g² ≤ C · a · n · g + F · n` with `ν > 0`, absorb the cross term
`C · a · n · g ≤ ν g² + (C²/(4ν)) a² n²` into the dissipation to get
`½ d ≤ (C²/(4ν)) a² n² + F · n`.

No PDE object: `d, g, a, n, F, ν, C` are arbitrary reals.  The absorption is the
nonnegativity of the perfect square `(2ν g − C·a·n)² / (4ν) ≥ 0`.  Instantiated
along a solution with `d = (‖u‖²_{H^m})'`, `g = ‖∇u‖_{H^m}`, `a = ‖u‖_{H²}`,
`n = ‖u‖_{H^m}`, `F = ‖f‖_{H^m}`, `C = C_m` it is eq:Rhigh's Young step. -/
theorem young_high_real {d g a n F ν C : ℝ} (hν : 0 < ν)
    (h : (1 / 2) * d + ν * g ^ 2 ≤ C * a * n * g + F * n) :
    (1 / 2) * d ≤ C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 + F * n := by
  have hνne : ν ≠ 0 := hν.ne'
  have h4ν : (0 : ℝ) < 4 * ν := by linarith
  have key : 0 ≤ ν * g ^ 2 + C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 - C * a * n * g := by
    have expand : ν * g ^ 2 + C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 - C * a * n * g
        = (2 * ν * g - C * a * n) ^ 2 / (4 * ν) := by
      field_simp
      ring
    rw [expand]
    exact div_nonneg (sq_nonneg _) h4ν.le
  linarith

/-- **Young's absorption on eq:Rhigh**, the instance with the manuscript's
constants (`appendix-a-local-theory.tex:139-140`).  From eq:Rhigh's shape
`½ d + ν g² ≤ Chigh m · a · n · g + F · n` derive
`½ d ≤ Cgron m ν · a² · n² + F · n`, fixing `Cgron m ν = (Chigh m)²/(4ν)`.
This is `young_high_real` at `C := Chigh m`, folding the produced constant into
`Cgron`. -/
theorem young_absorption_high {m : ℕ} {ν d g a n F : ℝ} (hν : 0 < ν)
    (h : (1 / 2) * d + ν * g ^ 2 ≤ Chigh m * a * n * g + F * n) :
    (1 / 2) * d ≤ Cgron m ν * a ^ 2 * n ^ 2 + F * n := by
  have hy := young_high_real (C := Chigh m) hν h
  have hCg : Cgron m ν = Chigh m ^ 2 / (4 * ν) := rfl
  rw [hCg]
  linarith

/-- **The absorbed squared-norm derivative bound** — eq:Rhigh (unit G1) with the
cross term already absorbed by Young (`young_absorption_high`), before the
`ζ`-regularization.  For every integer `m ≥ 3` and interior time `t ∈ (0,T)` of a
smooth-Sobolev-path solution,

`∃ d, HasDerivAt (r ↦ ‖u(r)‖²_{H^m}) d t
        ∧ ½ d ≤ C_{m,ν}‖u‖²_{H²}‖u‖²_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`.

This is the hoist requested by `REVIEW_HIGH_CONTINUATION.md` §5 (finding (a)):
the seven lines that were inline in `regularizedNormDerivative`, now named so the
`ζ↓0` integral field `highContinuationIntegral` (unit **G2b**, `Spec.lean:471-494`)
can consume it directly through `sqrt_le_primitive_linear`'s `hineq`. -/
theorem deriv_normSq_absorbed
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    (m : ℕ) (hm : 3 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ d : ℝ,
      HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
        (1 / 2) * d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
              sobolevNormAt (m : ℝ) w.velocity t ^ 2 +
            sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t := by
  obtain ⟨d₀, hd, hbound⟩ := energyIdentityHigh ν a f T hν ha hf w hpath m hm t ht
  exact ⟨d₀, hd, young_absorption_high hν hbound⟩

/-- The `deriv`-valued form of `deriv_normSq_absorbed`, via `HasDerivAt.deriv`:
the derivative of `r ↦ ‖u(r)‖²_{H^m}` at `t` (which `HasDerivAt` pins uniquely)
obeys the absorbed bound.  Convenient for `highContinuationIntegral` (unit G2b),
whose `sqrt_le_primitive_linear` step feeds on `deriv (fun r => ‖u(r)‖²_{H^m}) t`
directly; doubling it and rewriting `‖u‖_{H^m} = √(‖u‖²_{H^m})` yields exactly that
lemma's `hineq`. -/
theorem deriv_normSq_absorbed_deriv
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    (m : ℕ) (hm : 3 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (1 / 2) * deriv (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) t ≤
        Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
            sobolevNormAt (m : ℝ) w.velocity t ^ 2 +
          sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t := by
  obtain ⟨d₀, hd, habs⟩ := deriv_normSq_absorbed hν ha hf w hpath m hm ht
  rw [hd.deriv]
  exact habs

/-- **eq:highcontinuation before the limit**, unit **G2**
(`appendix-a-local-theory.tex:139-145`) — the spec field
`research/A04/Spec.lean:459-470` `regularizedNormDerivative` **token-for-token**
in the formalization vocabulary (`Chigh m := A03.outerTameConst m`,
`Cgron m ν := (Chigh m)²/(4ν)`).

For every integer `m ≥ 3`, every interior time `t ∈ (0,T)` of a smooth-Sobolev-path
solution, and every `ζ > 0`, the regularized norm `r ↦ (‖u(r)‖²_{H^m}+ζ²)^{1/2}`
is differentiable at `t` with

`(d/dt)(‖u‖²_{H^m}+ζ²)^{1/2}
   ≤ C_{m,ν}‖u‖²_{H²}(‖u‖²_{H^m}+ζ²)^{1/2} + ‖f‖_{H^m}`.

Proof.  `energyIdentityHigh` (unit G1) gives `d₀` with
`HasDerivAt (r ↦ ‖u(r)‖²_{H^m}) d₀ t` and eq:Rhigh's bound.  `young_absorption_high`
absorbs the cross term, giving `½ d₀ ≤ Cgron m ν ‖u‖²_{H²}‖u‖²_{H^m} + ‖f‖_{H^m}‖u‖_{H^m}`,
i.e. (after `√(‖u‖²_{H^m}) = ‖u‖_{H^m}`) exactly `regularized_sqrt_bound`'s hypothesis
`d₀ ≤ 2(K·E + b·√E)` with `E = ‖u‖²_{H^m}`, `K = Cgron m ν ‖u‖²_{H²}`, `b = ‖f‖_{H^m}`.
`HasDerivAt.sqrt` supplies the two-sided derivative and `regularized_sqrt_bound`
the bound on it. -/
theorem regularizedNormDerivative :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
            ∃ d : ℝ,
              HasDerivAt
                  (fun r : ℝ =>
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
                d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
                      Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                    sobolevNormAt (m : ℝ) f t := by
  intro ν a f T hν ha hf w hpath m hm t ht ζ hζ
  -- The absorbed squared-norm derivative bound (unit G1 + Young), now named.
  obtain ⟨d₀, hd, habs⟩ := deriv_normSq_absorbed hν ha hf w hpath m hm ht
  -- The regularized argument is strictly positive (ζ > 0), so its square root has a
  -- two-sided derivative.
  have hpos : 0 < sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2 := by positivity
  have hderiv : HasDerivAt
      (fun r : ℝ => Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2))
      (d₀ / (2 * Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2))) t :=
    (hd.add_const (ζ ^ 2)).sqrt hpos.ne'
  refine ⟨_, hderiv, ?_⟩
  -- Rewrite ‖u‖_{H^m} = √(‖u‖²_{H^m}) to reach `regularized_sqrt_bound`'s `hineq` shape.
  have hnnn : 0 ≤ sobolevNormAt (m : ℝ) w.velocity t := ENNReal.toReal_nonneg
  have hineq : d₀ ≤ 2 * (Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
        sobolevNormAt (m : ℝ) w.velocity t ^ 2 +
      sobolevNormAt (m : ℝ) f t * Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2)) := by
    rw [Real.sqrt_sq hnnn]
    linarith
  -- Divide by 2√(‖u‖²_{H^m}+ζ²): the inequality half of unit Z1.
  exact regularized_sqrt_bound (E := fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2)
    (K := fun _ => Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2)
    (b := fun _ => sobolevNormAt (m : ℝ) f t)
    hζ (sq_nonneg _) (mul_nonneg (Cgron_pos m ν hν).le (sq_nonneg _))
    ENNReal.toReal_nonneg hineq

end NSFormalization.Section4.A04
