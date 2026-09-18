# T11 — the `H¹`-ball gap after U9e (lane 338)

Lane 338 proved the **`H³`-ball** quantitative local-existence input outright
(`Section3/T11/ExistenceInputH3.lean`, `periodicQuantitativeLocalInputH3`) and
re-instantiated the whole continuation chain at that ball.  This file records
exactly what is *still* unproved, why, and what U17 must check before
registering the API.

## 1. The exact statements that remain unproved

**(G1) `PeriodicQuantitativeLocalInput'`** — `Section3/T11/LocalExistence.lean:24`,
amendment 1, verbatim:

```lean
∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
  ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
    ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
        ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

Everything downstream of it is now proved at the `H³` ball, so this is the *only*
open name on the existence line.

**(G2) `PeriodicContinuationAPI.restart` with the `H¹` ball** —
`research/T11/probes/api_on_canonical.lean:102-111`, the field with
`periodicSobolevENorm 1 a' ≤ K`.  Lane 321's `Restart.restart` derives it from
(G1) in three lines; lane 338's `restartH3` is the same statement with
`periodicSobolevENorm 3 a' ≤ K`, proved unconditionally.

**(G3) `PeriodicContinuationAPI.restartBeyond` with the `H¹` ball** —
`api_on_canonical.lean:121-135`, the field with
`∀ t ∈ Ico 0 S, periodicSobolevENorm 1 (u (t, ·)) ≤ K`.  Lane 332's
`RestartBeyond.restartBeyond` derives it from (G1) through (G2); lane 338's
`restartBeyondH3` is the `H³` version, unconditional.

No other field of `PeriodicContinuationAPI` or `PeriodicLocalTheoryAPI`
mentions a ball: `higherOrderBound` quantifies over all orders `m`,
`extendsBeyond` and `lifespanInfiniteOfLocallyFinite` carry no ball in their
statements, and `exists_maximal` / `maximal_unique` carry none either.  Hence
(G1)–(G3) is the complete `H¹` residue.

## 2. Why (G1) is out of reach in this tree

The machinery that exists is a **Picard contraction in the two-space pair
`H³ × H²`** (lanes 313/317/328/330/334).  Its self-map and contraction
certificates (`TorusPicardConstants`, `torusPicardConstants_explicit`) are
stated in terms of

* `‖A‖` = the `H³` norm of the datum, and
* the force size in the *same* space `H³`,

because the bilinear convection map is bounded only as
`H³ × H³ →L H²` (real-order version: `H^r × H^r →L H^{r-1}` for `r ≥ 3`, lane
328).  The horizon is `torusKernelTime ν (torusPicardThreshold ‖bilinear‖ b)`
with `b ≥ ‖A‖_{H³} + ∫₀¹ ‖F(s)‖_{H³} ds`, which is monotone decreasing in
`‖A‖_{H³}`.  An `H¹` bound gives **no** control of `‖A‖_{H³}`, so the horizon
cannot be made uniform over an `H¹` ball by this route, at any level of
bookkeeping.

Uniformity over an `H¹` ball is the **subcritical Fujita–Kato local theory**:
one runs the contraction in a critical or subcritical space (`Ḣ^{1/2}`, `L³`,
or `H¹` with the `‖∇u‖_{L²}`-based energy estimate `‖u‖_{H¹} ≲ ‖a‖_{H¹}` on a
time `T ∼ (ν/‖a‖_{H¹})^{…}`), using the product estimate
`‖u·∇u‖_{H^{-1}} ≲ ‖u‖_{H¹}‖u‖_{H¹}^{1/2}‖u‖_{H²}^{1/2}` and interpolation.
Nothing of that is in `vendor/HeliCorgi/Formal/`, in
`vendor/NavierStokesAndEuler/`, or in `formalization/NSFormalization/`: greps
over `Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}` and
`vendor/HeliCorgi/Formal/` return only `H^m`-type ladders with integer or real
order `≥ 3` and the `H²`-based continuation criterion.  HeliCorgi's `R³` mild
theory has an explicit lifespan, but it is again in terms of a high-regularity
norm.

This is **exactly the wall Section 4 hit**: `ManuscriptHorizonLowerBoundH1` was
kept there as a named unproved predicate and the fixed-force `H⁷` narrowing was
registered as `RestartFixedForce` (owner-approved wording pending).  Amendment 2
prescribes the same honest treatment here.

## 3. Consumer checklist for U17

U17 registers the *proved* API.  Before it does, each consumer of a ball-carrying
field must be checked for which ball it can supply.

| consumer | what it needs | ball available | verdict |
|---|---|---|---|
| **T11 internal — `extendsBeyond`** (`ExistenceInputH3.extendsBeyondH3`) | one uniform trajectory bound on `[0,S)` at *some* order, fed to `restartBeyond` | `higherOrderBound` (U12) gives a finite `M` at **every** order `m`, in particular `m = 3`; lane 337 used `m = 1` only because the `H¹` restart ball was the target | **OK at `H³`.** This is the only structural use of the ball inside T11, and it costs nothing: U12's `∃ M` already stands outside `∀ t ∈ Ico 0 S`. |
| **T11 internal — `lifespanInfiniteOfLocallyFinite`** | `extendsBeyond` | as above | **OK at `H³`.** |
| **T11 internal — `exists_maximal` / `maximal_unique`** | a positive-horizon solution for admissible data | `exists_classical_of_picard` (334) is unconditional | **OK, no ball at all** (`exists_maximal_unconditional`). |
| **T18** (`thm:insertion`, `SECTION3_PLAN.md:48`) | T11 uniqueness + `H²↪L^∞`, lifespan exactly `T` for the inserted force | the inserted datum/force are explicit smooth periodic objects built in T14–T17, so every `H^m` norm is finite and computable | **expected OK**; T18 has no draft `Spec` yet, so re-check when it is written. |
| **T19** (density package) | T18 + T11 lifespan statements | no ball | **OK.** |
| **T20** (`prop:critical`) | its own copy of `PeriodicContinuationAPI` (`research/T20/Spec.lean:387-450`) — the `restart` field at line 402 and the `restartBeyond` field at line 437 both carry `periodicSobolevENorm 1` | T20's own route (`eq:H1energy`, `Spec.lean:1051,1200`) produces bounds on `periodicSobolevENorm 2` and `periodicHomogeneousENorm`, i.e. `H²`, not `H³` | **RE-READ REQUIRED.** T20 consumes the continuation package only through `extendsBeyond` / the criterion (which carry no ball); if it turns out to consume `restartBeyond` directly with an `H¹` (or `H²`) trajectory bound, the `H³` narrowing is **not** enough and that is an **owner-level gap**, to be reported, never silently weakened. T20 also needs `higherOrderBound` at `m = 3` to upgrade its `H²` bound, which U12 supplies. |
| **T15** | no `research/T15/` directory exists in the tree (T15 is a planned rescaling node, `SECTION3_PLAN.md:74`); nothing to check yet | — | **N/A today**; re-grep when T15 lands. |

Mechanical grep used (worktree root):

```
grep -rn "periodicSobolevENorm 1" research/ --include='*.lean'
```

Outside `research/T11/` (drafts and probes of the H¹ statements themselves) the
only hits are `research/T20/Spec.lean:402,437` and its `DraftB.lean:401,436` —
both inside the copied `PeriodicContinuationAPI` structure, not in a T20 proof.

## 4. What U17 should register

1. `RestartH3` / `RestartBeyondH3`: the proved `H³`-ball fields (a V2-style
   narrowing of the manuscript's statement), as in `Section4`'s
   `RestartFixedForce`.
2. `PeriodicRestartH1 : Prop`: the `H¹`-ball field (G2) kept **verbatim** as a
   named, documented, unproved predicate — the manuscript's statement — exactly
   like `ManuscriptHorizonLowerBoundH1`.  Same for (G3) if a consumer needs it.
3. `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`, `exists_maximal`,
   `maximal_unique`: registered as proved (modulo U12's `higherOrderBound` for
   the first two).
