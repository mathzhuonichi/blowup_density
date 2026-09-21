import NSFormalization.Section4.A01.ContinuationInvariant

/-!
# A01 unit A3 — row A3-L2: the a-priori-bound / prescribed-horizon packaging

This module is the **A3-L2 packaging** on top of lane 134's
`NSFormalization.Section4.A01.forced_global_of_bound_unconditional`.  It does no new analysis:
it *names* the a-priori-bound hypothesis of that theorem and repackages the theorem's content
as "on the prescribed interval `[0,S]` itself, the full `exists_local`-shaped local theory
holds".  This is the precise content of A3-L2's slogan **`horizon := S`**: once an a-priori
bound is available, `EulerBoundedMildContinuation.exists_global_mild_of_bound` (forked to carry
angle invariance in lane 134) hands the *whole* prescribed `[0,S]`, so there is **no choice over
`Source.OrdinaryForcedLocal.exists_local`'s `∃ T`** — the horizon is the prescribed endpoint.

## What is packaged here

* `HasAprioriBound hq hν a F hF R` — the named a-priori-bound predicate: it is *definitionally*
  the `hbound` hypothesis of `forced_global_of_bound_unconditional`.  **Quantifier order (the
  operative content, same point A02 `restart` makes): `R` is fixed before every window length
  `T ≤ S` and every Duhamel solution `u` on that window** (it bounds
  `sup_{t ∈ [0,T]} ‖u t‖_{SobolevSpace 1 (q+1)}` for *every* mild solution on *every* subwindow,
  not just the constructed one).  Supplying it is A3's remaining job: rows A3-M2 (the Grönwall
  integral step, once lane 138's `highContinuationIntegral` is merged) and A3-L1·k (the order-2
  norm cap turning `exists_local`'s `‖u‖ ≤ ‖u₀‖+1` into a uniform `Kbnd`).
* `horizonOf hν a F` — the *cylinder-carrier analogue* of `LocalTheoryAPI.horizon`
  (`research/A01/Spec.lean:283`), **not** that field: its value is the prescribed **input** `S`
  (read off `F`'s type index `Icc 0 S`), fixed under `HasAprioriBound`, not a number computed
  from the datum (`horizonOf_eq`, by `rfl`).
* `localTheory_on_prescribed_horizon` — the A3-L2 theorem: `forced_global_of_bound_unconditional`
  restated with the named `HasAprioriBound` hypothesis, `T` fixed to `S` (no `∃ T`).  All seven
  `exists_local` clauses hold on `[0,S]`: the mild solution `u`, the ordinary-`L²` path
  `U : C(Icc 0 S, EulerMeanSolenoidal.L2)`, `‖u‖ ≤ R`, the two initial values, the descent
  `ordinaryLift (U t) = value 1 (u t)`, divergence-freeness, the forced Duhamel equation and
  angle invariance.
* `exists_local_shape_of_aprioriBound` — the corollary in `exists_local`'s existential shape
  (`∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S), ∃ u U, …`), satisfied with the witness `T := S`.  Its
  norm clause carries the a-priori bound `‖u‖ ≤ R` (in place of `exists_local`'s `‖u‖ ≤ ‖u₀‖+1`):
  that is what makes it usable by the A02-facing `LocalTheoryAPI.solution` modelling, which may
  then take `horizon := S`.  **Thin by design:** for `R ≥ ‖u₀‖+1` this follows from `exists_local`
  alone (reviewer probe `/tmp/rev139/strength.lean`); its only added content is the regime
  `R < ‖u₀‖+1`, and even there the fact that `T` may be taken `= S` is invisible in a bare `∃ T`
  type — consumers that need the horizon *pinned* must use `localTheory_on_prescribed_horizon`.

## Relation to `LocalTheoryAPI` (`research/A01/Spec.lean:277`) — what A3-L2 does and does not give

A3-L2 fixes the horizon at the **prescribed input `S`**, *conditional on* `HasAprioriBound` for
that `S`.  It does **not** realise the `LocalTheoryAPI` fields; it is a cylinder-carrier step
towards them.  Precisely:

* `horizon` (`Spec.lean:283`, `ℝ → SpatialField → SpaceTimeField → ℝ`) — **not** realised.
  `horizonOf` is only the cylinder-carrier analogue: `#check` gives
  `0 < ν → SmoothL2Field Space → (Icc 0 S → SmoothL2Field Space) → ℝ` (a proof `0 < ν`, a bundled
  `SmoothL2Field`, a force path on the *prescribed* interval `Icc 0 S`), and its value is the
  input `S` read off `F`'s type — it *computes nothing*.  A real `LocalTheoryAPI.horizon` must
  **produce** a number from `(ν, a, f)`, where `f` carries no `S`.
* `solution` (`Spec.lean:297`) — the *existence on `[0,S]`* content is supplied in the cylinder
  carrier by `localTheory_on_prescribed_horizon` / `exists_local_shape_of_aprioriBound`,
  **conditional on `HasAprioriBound`**.  Not yet the field.
* `regularity` (`Spec.lean:305`, `ManuscriptLocalRegularity`) — **untouched**: all-order Sobolev
  time smoothness, eq:Rpressure, eq:projected, the radial potential (A01 units A2 / T1).
* `horizon_lower_bound` (`Spec.lean:338`, the uniform `δ`) — **untouched**: needs a quantitative
  lifespan lower bound (row H1); the lead is `exists_uniform_restart_time_invariant`
  (`ContinuationInvariant.lean`), still stated with the order-`q+1` cylinder `‖u₀‖ ≤ R` rather
  than `‖a‖_{H¹}` + `‖f‖_{L¹H¹}`.  The Grönwall bound gives an *upper* bound on the norms given a
  horizon, never a *lower* bound on the horizon (`A3_SPLIT.md`, finding F9), so A3-L2 does not
  touch this field.

So an eventual `LocalTheoryAPI` witness must still supply, on top of this lane:
1. **the bound** — `HasAprioriBound` for the datum: row A3-M2 (the Grönwall integral step, via
   lane 142's `Section4/A01/GronwallInstance.lean`) + A3-L1·k (the order-2 cap) **plus** the
   mild⟹energy bridge (`hbound` quantifies over *mild* solutions, eq:Rhigh is an energy identity);
2. **a data-dependent choice `S = S(ν, a, f)`** — the largest endpoint for which that bound is
   available; a *constant* `S` is inadmissible (it would turn `solution` into a global-existence
   claim);
3. **the carrier bridge** (rows B1/B2) — `SpatialField`/`SpaceTimeField` ⟶
   `SmoothL2Field Space` / `Icc 0 S → SmoothL2Field Space` in, and the cylinder pair `(u, U)` ⟶
   `ClassicalSolutionR ν a f (horizon ν a f)` out.

No new assumptions are introduced: everything here reduces to
`forced_global_of_bound_unconditional`.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- **The a-priori-bound predicate** (A3-L2).  This is *definitionally* the `hbound` hypothesis
of `forced_global_of_bound_unconditional`: a single real `R` that bounds the `ContinuousMap`
sup-norm `sup_{t ∈ [0,T]} ‖u t‖_{SobolevSpace 1 (q+1)}` of **every** forced Duhamel (mild)
solution `u` on **every** subwindow `[0,T]`, `T ≤ S`.

Quantifier order — the operative content: `R` is fixed **before** the window length `T` and the
solution `u`, so it is a genuine *uniform* a-priori bound (the same "chosen before the datum"
discipline as A02 `restart`).  Supplying `HasAprioriBound` is A3's remaining job (rows A3-M2 and
A3-L1·k); this module only consumes it. -/
def HasAprioriBound {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
      (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))),
      (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) → ‖u‖ ≤ R

/-- **The prescribed horizon** (A3-L2's `horizon := S`).  The *cylinder-carrier analogue* of
`LocalTheoryAPI.horizon` (`research/A01/Spec.lean:283`), **not** that field: it returns the
prescribed **input** `S` (read off `F`'s type index `Icc 0 S`), it computes nothing from the
datum, and its type (`0 < ν → SmoothL2Field Space → (Icc 0 S → SmoothL2Field Space) → ℝ`) is not
the field's `ℝ → SpatialField → SpaceTimeField → ℝ`.  Under `HasAprioriBound` the local theory
holds on the *whole* `[0,S]`, so the horizon may be taken to be `S` (`horizonOf_eq`); a genuine
`LocalTheoryAPI.horizon` must instead choose `S = S(ν,a,f)` per datum (see the module header). -/
def horizonOf {ν S : ℝ} (_hν : 0 < ν) (_a : SmoothL2Field Space)
    (_F : Icc (0 : ℝ) S → SmoothL2Field Space) : ℝ := S

/-- The A3-L2 horizon is the prescribed endpoint `S`: no choice over `exists_local`'s `∃ T`. -/
@[simp] theorem horizonOf_eq {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) : horizonOf hν a F = S := rfl

/-- **A3-L2 theorem — the local theory on the prescribed horizon `[0,S]`.**  This is
`forced_global_of_bound_unconditional` with its `hbound` hypothesis replaced by the named
`HasAprioriBound` predicate: on `[0,S]` *itself* (horizon `= S`, no `∃ T`) the full
`exists_local`-shaped local theory holds — the mild solution `u`, the ordinary-`L²` path `U`,
`‖u‖ ≤ R`, `u 0 = ordinarySobolev …`, `U 0 = a.toLp`, the descent
`ordinaryLift (U t) = value 1 (u t)`, divergence-freeness, the forced Duhamel equation and angle
invariance.  (The chosen horizon is `horizonOf hν a F = S`, `horizonOf_eq`.) -/
theorem localTheory_on_prescribed_horizon {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hb : HasAprioriBound hq hν a F hF R) :
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
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t :=
  forced_global_of_bound_unconditional hq hν hS hR a ha F hF hu₀ hb

/-- **A3-L2 corollary — `exists_local`'s existential shape, satisfied with `T := S`.**  The
conclusion of `Source.OrdinaryForcedLocal.exists_local` (`∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
∃ u U, …`) is met with the witness `T := S`: under the a-priori bound the horizon can be taken
to be the whole prescribed interval.  The norm clause carries the a-priori bound `‖u‖ ≤ R` in
place of `exists_local`'s `‖u‖ ≤ ‖u₀‖ + 1`; this is the form an A02-facing
`LocalTheoryAPI.solution` model consumes to set `horizon := S`.  **Thin by design:** for
`R ≥ ‖u₀‖ + 1` this already follows from `exists_local` alone (via `hu.trans`), so its only added
content is the regime `R < ‖u₀‖ + 1`, and even there `T = S` is invisible in the bare `∃ T`
type — consumers that need the horizon *pinned* to `S` must use
`localTheory_on_prescribed_horizon`. -/
theorem exists_local_shape_of_aprioriBound {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hb : HasAprioriBound hq hν a F hF R) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2)),
        ‖u‖ ≤ R ∧
        u ⟨0, le_rfl, hT.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hT.le hTS
          (coefficients 1 hq (sobolevPath F hF q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t :=
  ⟨S, hS, le_rfl, localTheory_on_prescribed_horizon hq hν hS hR a ha F hF hu₀ hb⟩

end NSFormalization.Section4.A01
