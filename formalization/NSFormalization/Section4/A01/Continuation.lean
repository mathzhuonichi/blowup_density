import NSFormalization.Source.OrdinaryForcedLocal
import Euler.BoundedMildContinuation
import Euler.CorrectionContinuation

/-!
# A01 unit A2b / A3 row A2b-a′ — forced global mild solution from an a-priori bound

This module discharges the "continuation-from-an-a-priori-bound" edge of A01 on the
recommended OpenAI/local spine, as identified by the lane-122 reviewer
(`research/A01/REVIEW_A3.md` §F5, §3), correcting `research/A01/A3_SPLIT.md` §3b's
false claim that the Euler/local layer has no continuation criterion.

The vendored package **does** carry a genuine finite-time continuation of the actual
forced viscous mild solution, on **exactly** the carrier and `Coefficients` bundle of
`NSFormalization.Source.OrdinaryForcedLocal.exists_local`
(`Source/OrdinaryForcedLocal.lean:32`):
`EulerBoundedMildContinuation.exists_global_mild_of_bound`
(`vendor/NavierStokesAndEuler/Euler/BoundedMildContinuation.lean:39`).

## What is proved

* `forced_global_mild_of_bound` — **(S)** the bare statement: for `6 ≤ q`, `ν > 0`,
  `0 < S`, `0 ≤ R`, smooth data `a`, a force path `F` with continuous jets, initial
  norm `≤ R`, and the a-priori bound `‖u‖ ≤ R` on every window `[0,T] ⊆ [0,S]`, there
  is a mild solution on all of `[0,S]` with `‖u‖ ≤ R`, the right initial value and the
  forced Duhamel equation.  One-line application of the vendor theorem.
* `forced_mild_divergenceFree` — **(2a)** the divergence-freeness clause
  `exists_local` carries and `exists_global_mild_of_bound` drops.  Pointwise, via
  `EulerDivergenceFreeHeat.mild_solution_preserves_gradient_zero` — the exact template
  `EulerCorrectionContinuation.correction_mild_divergenceFree` uses.  Works on all of
  `[0,S]`: the Leray-projected source has gradient zero regardless of the unknown
  (`leray_gradient_zero`), so no contraction/uniqueness is needed.
* `forced_ordinary_descent` — **(2c)** the descent to `U : C(Icc 0 S, EulerMeanSolenoidal.L2)`
  with `U 0 = a.toLp`, copying the last eight lines of `exists_local`
  (`ordinaryValue`, `ordinaryValue_lift`).  **Conditional on the angle-invariance of
  `u`**, because `ordinaryValue_lift` itself consumes that invariance.
* `forced_global_of_bound` — **the final theorem in the shape of `exists_local`'s
  conclusion, on the given `S`**, assembling the above.  It exposes the angle-invariance
  clause as the explicit hypothesis `hinv` (see the gap note below); with it discharged,
  A01's A3 can take `T₀ := S` once the a-priori bound `hbound` is supplied.
* `forced_global_of_bound'` — the **preferred** form (reviewer F4): the same, but with the
  free `‖u‖ ≤ R` premise added to `hinv` — a strictly stronger theorem at zero proof cost,
  and the exact shape the window-uniqueness route discharges.
* `forced_uniform_restart_time` — **(H1 lead)** the uniform restart time in the forced
  setting, a direct specialization of `EulerUniformHeatLocal.exists_uniform_restart_time`
  to `coefficients 1 hq (sobolevPath F hF q)`.

## Gap: angle-invariance (unit A2b clause (2b)) is not restored *in this lane*

`exists_local`'s angle-invariance clause `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`
is not carried through the continuation here; it is left as the hypothesis `hinv` of
`forced_global_of_bound` (and, in the weaker/preferred form, `forced_global_of_bound'`).
No *global* mild uniqueness is required to remove it — that framing (in an earlier draft of
this note) was wrong on both counts and is corrected here per the lane-126 review
(`research/A01/REVIEW_A2B.md` §F6):

* There is genuinely no *pointwise* route: the source `leray (f − advection u u)` is
  covariant, not invariant — angle-invariant only when `u` is — so a *uniqueness* step is
  needed (`v := (translate)∘u` solves the same Duhamel equation ⟹ `v = u`).
* But `exists_global_mild_of_bound` is built by iterating windows of length `δ` obtained from
  `exists_positive_time_budget`, and that `δ` *guarantees* `kernelMass δ · L < 1`
  (`Euler/UniformHeatLocal.lean:42-54`): **the continuation's own windows are exactly the
  uniqueness regime of `mild_solution_unique`.**  `kernelMass S · L < 1` being false for large
  `S` is irrelevant — nobody needs it on all of `[0,S]`.  Per-window invariance is proved
  unconditionally (contraction discharged, not assumed) in
  `research/A01/probes/probe_window_invariance.lean` and
  `probe_restart_window_invariance.lean` (reviewer probes, standard three axioms).
* `set_option maxHeartbeats` is not forbidden in this repository (ten merged modules use it);
  the covariance/uniqueness port needs only `300000`–`600000`, not `800000`.  See
  `research/A01/probes/a2b_invariant_port.lean`.

The remaining work is therefore an **M** (≈150–190 lines), not an L campaign: fork
`exists_global_mild_of_bound`'s ~45-line window induction so it carries the invariance clause,
using an invariance-carrying restart (the restart probe) and a `gluePath_invariant` step.  See
`research/A01/ATTEMPTS_A2B.md` (row A2b-b).
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- **(S)** Continuation from an a-priori Sobolev bound: a uniform `‖u‖ ≤ R` over every
window `[0,T] ⊆ [0,S]` yields the forced viscous mild solution on the whole prescribed
`[0,S]`, with the right initial value and the forced Duhamel equation.  One-line
application of `EulerBoundedMildContinuation.exists_global_mild_of_bound` to the same
`ForcedCylinderLocal.coefficients` and initial vector fed by `exists_local`. -/
theorem forced_global_mild_of_bound {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R) :
    ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
      ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t :=
  EulerBoundedMildContinuation.exists_global_mild_of_bound 1 q ν hν S hS R hR _ hu₀
    (coefficients 1 hq (sobolevPath F hF q)) hbound

/-- **(2a)** The divergence-freeness clause of `exists_local`, restored for the continued
solution.  Pointwise via `mild_solution_preserves_gradient_zero`; valid on all of `[0,S]`
because the Leray-projected source has gradient zero for every input. -/
theorem forced_mild_divergenceFree {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) :
    ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0 := by
  have hu₀ : value 1 (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
      ∈ divergenceFreeSpace 1 1 0 :=
    NSFormalization.Source.OrdinaryForcedLocal.initial_divergenceFree (q + 1) a ha
  have hz := mild_solution_preserves_gradient_zero 1 1 0 ν hν S hS.le
    (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
    ((gradientEvaluation_zero_iff 1 1 0 _).mpr hu₀)
    (((coefficients 1 hq (sobolevPath F hF q)).comp (timeInclusion le_rfl)).apply)
    (((coefficients 1 hq (sobolevPath F hF q)).comp (timeInclusion le_rfl)).continuous)
    (fun t v => by
      change gradientProjection 1 1 0
        (value 1 ((coefficients 1 hq (sobolevPath F hF q)).apply (timeInclusion le_rfl t) v)) = 0
      rw [source_eq]
      exact leray_gradient_zero 1 _) u hsol
  exact fun t => (gradientEvaluation_zero_iff 1 1 0 (u t)).mp (hz t)

/-- **(2c)** Ordinary `L²` descent of the continued solution: the same construction as the
last eight lines of `exists_local` (`ordinaryValue`, `ordinaryValue_lift`), producing
`U : C(Icc 0 S, EulerMeanSolenoidal.L2)` with `ordinaryLift (U t) = value 1 (u t)` and
`U 0 = a.toLp`.  **Conditional on the angle-invariance `hinv` of `u`**, which
`ordinaryValue_lift` consumes. -/
theorem forced_ordinary_descent {q : ℕ} (hq : 6 ≤ q) {S : ℝ} (hS : 0 < S)
    (a : SmoothL2Field Space)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hi : u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
    (hinv : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ t, ordinaryLift (U t) = value 1 (u t) := by
  let U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
    ⟨fun t => ordinaryValue (q + 1) (u t), (ordinaryValue (q + 1)).continuous.comp u.continuous⟩
  have hl : ∀ t : Icc (0 : ℝ) S, ordinaryLift (U t) = value 1 (u t) :=
    fun t => ordinaryValue_lift (by omega) (u t) (fun θ => hinv θ t)
  refine ⟨U, ?_, hl⟩
  apply ordinaryLift.injective
  rw [hl, hi]
  exact ordinarySobolev_value _ _ _

/-- **Final theorem, in the shape of `exists_local`'s conclusion but on the prescribed `S`.**
Given the a-priori bound `hbound` and the angle-invariance obligation `hinv` (the unit-A2b
clause (2b) that is *not* restored in this lane — see the module gap note), the continued
solution carries every clause `exists_local` carries: the norm bound, the two initial
values, the ordinary-`L²` descent, divergence-freeness, the forced Duhamel equation and
angle invariance.  So A01's A3 may take `T₀ := S`. -/
theorem forced_global_of_bound {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R)
    (hinv : ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨u, hu, hi, hm⟩ := forced_global_mild_of_bound hq hν hS hR a F hF hu₀ hbound
  have hinvu := hinv u hm
  have hd := forced_mild_divergenceFree hq hν hS a ha F hF u hm
  obtain ⟨U, hU0, hUl⟩ := forced_ordinary_descent hq hS a u hi hinvu
  exact ⟨u, U, hu, hi, hU0, hUl, hd, hm, hinvu⟩

/-- **Preferred form of the final theorem (reviewer F4).**  Identical to
`forced_global_of_bound` except that the invariance obligation `hinv` carries the extra
premise `‖u‖ ≤ R`.  This strictly weakens `hinv` (strictly strengthens the theorem) at zero
proof cost — `hinv` is applied only to the solution returned by `forced_global_mild_of_bound`,
which already satisfies `‖u‖ ≤ R` — and it is the exact shape the window-uniqueness route
(`research/A01/probes/probe_restart_window_invariance.lean`) discharges: per-window invariance
is proved only for `(R+1)`-bounded solutions.  The unrestricted `hinv` of
`forced_global_of_bound` asks the next lane for something strictly harder than it needs. -/
theorem forced_global_of_bound' {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hbound : ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
        (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
        (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R)
    (hinv : ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))), ‖u‖ ≤ R →
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t := by
  obtain ⟨u, hu, hi, hm⟩ := forced_global_mild_of_bound hq hν hS hR a F hF hu₀ hbound
  have hinvu := hinv u hu hm
  have hd := forced_mild_divergenceFree hq hν hS a ha F hF u hm
  obtain ⟨U, hU0, hUl⟩ := forced_ordinary_descent hq hS a u hi hinvu
  exact ⟨u, U, hu, hi, hU0, hUl, hd, hm, hinvu⟩

/-- **(H1 lead)** Uniform restart time in the forced setting: a direct specialization of
`EulerUniformHeatLocal.exists_uniform_restart_time` to the forced coefficient bundle
`coefficients 1 hq (sobolevPath F hF q)`.  The window length `δ` depends only on that
bundle and the data bound `R`, uniformly over restart points.  This is **not literally**
A01's H1 (`A01_SPLIT.md:147`), which wants `δ` as a function of `‖a‖_{H¹}` and
`‖f‖_{L¹H¹}` only: here `R` is a bound in the order-`q+1` cylinder norm.  Recorded as a
candidate lead, not a solution. -/
theorem forced_uniform_restart_time {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (b T : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T) (hbT : b + T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace 1 (q + 1), ‖u₀‖ ≤ R →
          ∃ u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)),
            ‖u‖ ≤ R + 1 ∧ u ⟨0, le_rfl, hT⟩ = u₀ ∧
            ∀ t : Icc (0 : ℝ) T,
              u t = heatOperator 1 (q + 1) (2 * ν * t.val).toNNReal u₀ +
                ∫ r in (0 : ℝ)..t.val, heatKernel 1 q ν hν r
                  ((coefficients 1 hq (sobolevPath F hF q)).apply
                    (timeWindow b T hb hbT (projIcc 0 T hT (t.val - r)))
                    (u (projIcc 0 T hT (t.val - r)))) :=
  exists_uniform_restart_time 1 q ν hν S hS R hR (coefficients 1 hq (sobolevPath F hF q))

end NSFormalization.Section4.A01
