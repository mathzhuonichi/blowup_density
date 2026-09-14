import NSFormalization.Section4.A04.HighContinuation
import NSFormalization.Section4.A04.Continuity

/-!
# A04 unit G2b — eq:highcontinuation after `ζ↓0`, integrated (`highContinuationIntegral`)

`paper/sections/appendix-a-local-theory.tex:141-145`, spec field
`research/A04/Spec.lean:471-494` `highContinuationIntegral`.  This is the `ζ↓0`
limit of unit **G2** (`HighContinuation.lean`), in the only form that survives
the limit and that Grönwall consumes: the **integrated** inequality on
`[t₀,t] ⊆ [0,T)`,

`‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m}
   + ∫_{t₀}^{t} (C_{m,ν}‖u(s)‖²_{H²}‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}) ds`,

together with the `IntervalIntegrable` conjunct that makes the Lebesgue interval
integral honest rather than Mathlib's junk `0` on a non-integrable integrand
(`Spec.lean:483-489`, `REVIEW.md` finding 6).

## Why integrated, not differential

After `ζ↓0` the left-hand side is `‖u‖_{H^m}`, which need not be differentiable
at a time where `u` vanishes in `H^m`; the manuscript's `(‖u‖_{H^m})'` is
shorthand for the inequality that survives the limit, and that inequality is this
integrated one.  It is realized by unit **Z1**'s `ζ↓0` integral form
`sqrt_le_primitive_linear` (`Regularized.lean:134`), which regularizes
`√(E+δ²)`, proves the regularized difference antitone, and lets `δ↓0` — with **no**
assumption that `E t₀ = 0`.

## Route (size S, per `research/A04/G1_SPLIT.md` unit G2b)

* **The bound** is `sqrt_le_primitive_linear` at
  `E := fun r => sobolevNormAt m w.velocity r ^ 2` (so `√E = ‖u‖_{H^m}` by
  `Real.sqrt_sq`, since `sobolevNormAt` is a `.toReal ≥ 0`),
  `K := fun s => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2`,
  `b := fun s => sobolevNormAt m f s`.  Its `hineq` is
  `deriv_normSq_absorbed_deriv` (G1 + Young, unit G2's hoist) **doubled** and
  `Real.sqrt_sq`-rewritten; its interior derivatives are
  `deriv_normSq_absorbed`; its `ContinuousOn (Icc t₀ t)` hypotheses are unit
  **N1**'s `continuousOn_sobolevNormAt_velocity` / `_force` mono'd along
  `Icc t₀ t ⊆ Ico 0 T`.
* **The integrability conjunct** is unit **N1**'s
  `intervalIntegrable_highContinuationIntegrand` — free, one application.  It
  carries a `Cgron` parameter, so `A04.Cgron` is passed **explicitly** (a local
  `Cgron` binder would otherwise shadow the def).

The `0 ≤ t₀` endpoint is exactly right: `deriv_normSq_absorbed` gives derivatives
on `Ioo 0 T` and `sqrt_le_primitive_linear` needs them only on
`Ioo t₀ t ⊆ Ioo 0 T`, continuity only on `Icc t₀ t ⊆ Ico 0 T`; the degenerate
`t₀ = t` is handled by `sqrt_le_primitive_linear` itself (empty interior).

`MemL1Hm f` is a spec hypothesis for fidelity (it books the `L¹_t H^m` bound of
the forcing integral) and is not consumed by the proof: integrability is settled
by continuity (N1), not by `MemL1Hm`.
-/

noncomputable section

open Set MeasureTheory
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

namespace NSFormalization.Section4.A04

/-- **eq:highcontinuation after `ζ↓0`, integrated**, unit **G2b**
(`appendix-a-local-theory.tex:141-145`) — the spec field
`research/A04/Spec.lean:471-494` `highContinuationIntegral` **token-for-token**
in the formalization vocabulary (`Cgron m ν := (Chigh m)²/(4ν)`).

For every integer `m ≥ 3` and `0 ≤ t₀ ≤ t < T` of a smooth-Sobolev-path solution
with `L¹_t H^m` forcing, the continuation integrand is `IntervalIntegrable` on
`[t₀,t]` and

`‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m}
   + ∫_{t₀}^{t} (C_{m,ν}‖u(s)‖²_{H²}‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}) ds`.

Proof.  The first conjunct is unit N1's
`intervalIntegrable_highContinuationIntegrand` (with `A04.Cgron` passed
explicitly).  The second is unit Z1's `sqrt_le_primitive_linear` at
`E = ‖u‖²_{H^m}`, `K = Cgron m ν ‖u‖²_{H²}`, `b = ‖f‖_{H^m}`: its `hineq` is
`deriv_normSq_absorbed_deriv` doubled with `√(‖u‖²) = ‖u‖`, its interior
derivatives `deriv_normSq_absorbed`, its continuities N1.  `Real.sqrt_sq` then
turns `√(‖u‖²_{H^m})` into `‖u‖_{H^m}` at both endpoints and inside the
integral. -/
theorem highContinuationIntegral :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
            IntervalIntegrable
                (fun s : ℝ =>
                  Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s)
                volume t₀ t ∧
              sobolevNormAt (m : ℝ) w.velocity t ≤
                sobolevNormAt (m : ℝ) w.velocity t₀ +
                  ∫ s in t₀..t,
                    (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                        sobolevNormAt (m : ℝ) w.velocity s +
                      sobolevNormAt (m : ℝ) f s) := by
  intro ν a f T hν ha hf _hf1 w hpath m hm t₀ t ht₀ htt htT
  -- `sobolevNormAt` is a `.toReal`, hence `≥ 0` at every time; so `√(‖u‖²) = ‖u‖`.
  have hvnn : ∀ s : ℝ, 0 ≤ sobolevNormAt (m : ℝ) w.velocity s := fun _ => ENNReal.toReal_nonneg
  -- `[t₀,t] ⊆ [0,T)`, for the continuity `mono` steps.
  have hsub : Icc t₀ t ⊆ Ico (0 : ℝ) T :=
    fun x hx => ⟨le_trans ht₀ hx.1, lt_of_le_of_lt hx.2 htT⟩
  -- The `IntervalIntegrable` conjunct (unit N1) — free; pass `A04.Cgron` explicitly.
  refine ⟨intervalIntegrable_highContinuationIntegrand hf w A04.Cgron m ht₀ htt htT, ?_⟩
  -- Continuity of `E`, `K`, `b` on `[t₀,t]` (unit N1).
  have hEc : ContinuousOn (fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2) (Icc t₀ t) :=
    ((continuousOn_sobolevNormAt_velocity w m).mono hsub).pow 2
  have hKc : ContinuousOn (fun s => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2) (Icc t₀ t) :=
    continuousOn_const.mul (((continuousOn_sobolevNormAt_velocity w 2).mono hsub).pow 2)
  have hbc : ContinuousOn (fun s => sobolevNormAt (m : ℝ) f s) (Icc t₀ t) :=
    (continuousOn_sobolevNormAt_force hf m T).mono hsub
  -- Interior differentiability of `E = ‖u‖²_{H^m}` (unit G1 via `deriv_normSq_absorbed`).
  have hdE : ∀ s ∈ Ioo t₀ t,
      HasDerivAt (fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2)
        (deriv (fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2) s) s := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T := ⟨lt_of_le_of_lt ht₀ hs.1, lt_trans hs.2 htT⟩
    obtain ⟨d, hd, -⟩ := deriv_normSq_absorbed hν ha hf w hpath m hm hsT
    rw [hd.deriv]; exact hd
  -- The Grönwall-ready differential inequality: `deriv_normSq_absorbed_deriv` doubled,
  -- with `√(‖u‖²_{H^m}) = ‖u‖_{H^m}`.
  have hineq : ∀ s ∈ Ioo t₀ t,
      deriv (fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2) s ≤
        2 * (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                sobolevNormAt (m : ℝ) w.velocity s ^ 2 +
              sobolevNormAt (m : ℝ) f s *
                Real.sqrt (sobolevNormAt (m : ℝ) w.velocity s ^ 2)) := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T := ⟨lt_of_le_of_lt ht₀ hs.1, lt_trans hs.2 htT⟩
    have habs := deriv_normSq_absorbed_deriv hν ha hf w hpath m hm hsT
    rw [Real.sqrt_sq (hvnn s)]
    linarith [habs]
  -- Unit Z1's `ζ↓0` integral form at the upper endpoint `t`.
  have hmain := sqrt_le_primitive_linear (t₀ := t₀) (t₁ := t)
    (E := fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2)
    (E' := fun s => deriv (fun r => sobolevNormAt (m : ℝ) w.velocity r ^ 2) s)
    (K := fun s => Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2)
    (b := fun s => sobolevNormAt (m : ℝ) f s)
    htt hEc hKc hbc
    (fun s _ => sq_nonneg _)
    (fun s _ => mul_nonneg (Cgron_pos m ν hν).le (sq_nonneg _))
    (fun s _ => ENNReal.toReal_nonneg)
    hdE hineq t ⟨htt, le_rfl⟩
  -- The integrand of `hmain` equals the spec integrand: `√(‖u‖²_{H^m}) = ‖u‖_{H^m}`.
  have hintEq :
      (∫ s in t₀..t,
          (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
              Real.sqrt (sobolevNormAt (m : ℝ) w.velocity s ^ 2) +
            sobolevNormAt (m : ℝ) f s))
        = ∫ s in t₀..t,
            (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                sobolevNormAt (m : ℝ) w.velocity s +
              sobolevNormAt (m : ℝ) f s) :=
    intervalIntegral.integral_congr fun s _ => by rw [Real.sqrt_sq (hvnn s)]
  calc sobolevNormAt (m : ℝ) w.velocity t
      = Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2) := (Real.sqrt_sq (hvnn t)).symm
    _ ≤ Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t₀ ^ 2) +
          ∫ s in t₀..t,
            (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                Real.sqrt (sobolevNormAt (m : ℝ) w.velocity s ^ 2) +
              sobolevNormAt (m : ℝ) f s) := hmain
    _ = sobolevNormAt (m : ℝ) w.velocity t₀ +
          ∫ s in t₀..t,
            (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                sobolevNormAt (m : ℝ) w.velocity s +
              sobolevNormAt (m : ℝ) f s) := by
        rw [Real.sqrt_sq (hvnn t₀), hintEq]

end NSFormalization.Section4.A04
