# ATTEMPTS — lane 139-A01-a3-l2-horizon (unit A3 row A3-L2)

Row **A3-L2** ("choose `T₀`, define `horizon`"): the a-priori-bound / prescribed-horizon
packaging.  Marked *ready, S* by the lane-134 review (`REVIEW_A2B_INV.md` §5.1) once
`forced_global_of_bound_unconditional` landed.  Deliverable module:
`formalization/NSFormalization/Section4/A01/Horizon.lean` (namespace
`NSFormalization.Section4.A01`, imports the frozen `…A01.ContinuationInvariant`, edits nothing).

## Outcome — packaging closed, first-try compile

Two defs, one `rfl` lemma, two theorems.  `lake build … Horizon` = `Build completed
successfully (3943 jobs)`; `lake env lean` on the module silent (0 bytes, no warning); every
`#print axioms` = `[propext, Classical.choice, Quot.sound]`; `make check` green.  No
`set_option` needed (all at default `200000` heartbeats): the module is a repackaging, the only
proof terms are one direct application and one anonymous-constructor witness.

* `HasAprioriBound hq hν a F hF R` (def, `Prop`) — the named a-priori-bound predicate, byte-equal
  to the `hbound` hypothesis of `forced_global_of_bound_unconditional`.  Docstring states the
  quantifier order (`R` fixed before every window length `T ≤ S` and every mild solution `u`).
* `horizonOf hν a F` (def, `:= S`) — the horizon selector, signature modelled on
  `LocalTheoryAPI.horizon` (`Spec.lean:283`).  `horizonOf_eq : horizonOf hν a F = S := rfl`.
* `localTheory_on_prescribed_horizon` (theorem) — `forced_global_of_bound_unconditional` with the
  named `HasAprioriBound` hypothesis, `T` fixed to `S` (no `∃ T`).  Proof: one application
  `forced_global_of_bound_unconditional hq hν hS hR a ha F hF hu₀ hb` (the `def` `HasAprioriBound`
  is semireducible, so `hb` unifies with the `∀`-shaped `hbound` slot by `isDefEq`; no `unfold`
  needed).  All seven `exists_local` clauses on `[0,S]`.
* `exists_local_shape_of_aprioriBound` (theorem) — the `exists_local` existential shape
  (`∃ (T:ℝ) (hT:0<T) (hTS:T≤S), ∃ u U, …`) satisfied with witness `T := S`.  Proof:
  `⟨S, hS, le_rfl, localTheory_on_prescribed_horizon …⟩`.

## Design decisions

* **`localTheory_on_prescribed_horizon` states the conclusion on literal `S`, not on
  `horizonOf hν a F`.**  Two reasons: (i) it stays character-identical to
  `forced_global_of_bound_unconditional`'s conclusion, so the one-line proof is a bare
  application with no defeq friction on the endpoint membership proofs `⟨0, le_rfl, hS.le⟩`;
  (ii) `horizonOf`/`horizonOf_eq` carry the "`horizon := S`" content separately and are what a
  `LocalTheoryAPI`-style consumer reads.  `horizonOf hν a F` is defeq `S`, so a consumer that
  wants the interval `Icc 0 (horizonOf hν a F)` gets it by `rfl`.
* **The corollary carries the a-priori bound `‖u‖ ≤ R`, not `exists_local`'s `‖u‖ ≤ ‖u₀‖+1`.**
  `exists_local` (unconditionally) already produces its own existential with *some* `T ≤ S` and
  the datum-relative bound `‖u₀‖+1`; the *new* content of A3-L2 is that under an a-priori bound
  the horizon may be pinned to the whole prescribed `S`, and the natural bound to expose is the
  uniform `R` the bound supplies.  Pinning `T = S` is not visible in a bare `∃ T` type, which is
  exactly why the primary deliverable is `localTheory_on_prescribed_horizon` (`T = S` in the
  type) and the `∃ T` corollary is a presentational wrapper for the A02-facing modelling.
* **`horizonOf`'s unused binders are `_`-prefixed** (`_hν`, `_a`) so the `unusedVariables` linter
  stays silent while the signature still mirrors `LocalTheoryAPI.horizon ν a f`; `_F` is only
  there to pin the implicit `S`.

## No failed Lean approaches

The module compiled on the first `lake build`.  There were no dead ends at the Lean level: the
content is entirely inherited from `forced_global_of_bound_unconditional` (lane 134), and the two
theorems are a direct application and an anonymous-constructor witness.  The one non-Lean snag
was the same one lane 134's audit hit — `lake env lean ../research/A01/axioms_a3_l2.lean` needs
the four `Euler.*` modules its non-vacuity example imports (`OrdinaryCauchyInterpolation`,
`OrdinaryH3Norms`, `SmoothL2Series`, `LpSmoothFieldAlgebra`) built first
(`Build completed successfully (4682 jobs)`), else it fails with `object file … .olean does not
exist`.

## The residual — supplying `HasAprioriBound`

A3-L2 *names and consumes* the a-priori bound; it does **not** produce it.  Producing
`HasAprioriBound q ν a F S R` — a single `R` bounding `sup_{t∈[0,T]} ‖u t‖_{SobolevSpace 1 (q+1)}`
for **every** forced Duhamel solution on **every** window `T ≤ S` — is the remaining A3 work:

1. **A3-M2** (`A3_SPLIT.md` row A3-M2): the Grönwall integral step
   `y t ≤ y 0 + ∫₀ᵗ(C_gron·k·y + b)` feeding `gronwall_bddAbove_Ico`
   (`Section4/A01/Propagation.lean`), whose explicit bound `(y 0 + Bbnd)·exp(C_gron·Kbnd)` is
   solution-independent — so the "`R` before `u`" quantifier order is reachable.  A3-M2 waits on
   A04's `hpr` (`energyIdentityHigh`) and, for the continuation integrand, on lane 138's
   `highContinuationIntegral` being merged.
2. **A3-L1·k** (`A3_SPLIT.md` row A3-L1·k): the order-2 norm cap
   `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖_{SobolevSpace 1 (q+1)}` turning `exists_local`'s
   `‖u‖ ≤ ‖u₀‖+1` into a uniform `Kbnd` for the Grönwall driver `k = ‖u‖²_{H²}`.  Still blocked
   by 119's C1b-m-D (the missing D01 finite-order datum constructor).

Three shape mismatches the supplier must bridge, none new (lane-134 review §5.2): (i) the norm
side — Grönwall is abstract in `y : ℕ → ℝ → ℝ`, `hbound` needs the cylinder
`‖u t‖_{SobolevSpace 1 (q+1)}`, and the *forward* comparison
`‖u t‖ ≤ c'·(finitely many sobolevNormAt m (⇑(U t)))` is **not yet a row** in `A3_SPLIT.md`;
(ii) the interval side — Grönwall lives on the half-open `Ico 0 T₀`, `hbound` needs the closed
`Icc 0 T` for every `T ≤ S` (harmless if `T₀ > S`); (iii) mild ⟹ energy — `hbound` quantifies
over mild solutions, eq:Rhigh is an energy identity, so the supplier also needs the mild→strong
bridge (A02 / T1).

## Notes for downstream

* `Horizon.lean`, like `Continuation.lean` / `ContinuationInvariant.lean`, is imported by nothing
  in `Contracts/`/`Bindings/`/`Tests/`, so it is not in `make test`'s closure until a contract
  consumes it.  Covered here by `research/A01/axioms_a3_l2.lean`.
* Which `LocalTheoryAPI` fields A3-L2 discharges vs which remain is spelled out in the module
  docstring: `horizon` modelled (`horizonOf`); `solution` supplied conditionally in the cylinder
  carrier (still needs the B1/B2 datum bridge + the supply of `HasAprioriBound`); `regularity`
  and `horizon_lower_bound` untouched (A2/T1 and H1 respectively).

## Review response (lane-139 review `research/A01/REVIEW_A3_L2.md`, ACCEPT-WITH-NOTES)

Verdict ACCEPT-WITH-NOTES; the exported statements are accepted unchanged (machine diff **0
lines** vs `exists_local[T:=S]`, `rfl`/`Iff.rfl` fidelity checks pass).  The notes are about
claims *around* the Lean, addressed doc-only:

* **F3 (module docstring overstated `LocalTheoryAPI.horizon`).**  Reworded (docstring only, no
  statement change): `horizonOf` is the *cylinder-carrier analogue* of `LocalTheoryAPI.horizon`,
  **not** that field — its type is `0<ν → SmoothL2Field Space → (Icc 0 S → SmoothL2Field Space) →
  ℝ` (not `ℝ → SpatialField → SpaceTimeField → ℝ`) and its value is the prescribed **input** `S`
  read off `F`'s type index, computing nothing.  A real `LocalTheoryAPI` witness must still
  supply (i) the bound (A3-M2 via lane 142's `Section4/A01/GronwallInstance.lean` + A3-L1·k + the
  mild⟹energy bridge), (ii) a **data-dependent** `S = S(ν,a,f)` (a *constant* `S` would assert
  global existence), (iii) the B1/B2 carrier bridge; `regularity` and `horizon_lower_bound`
  untouched.
* **F4 (`exists_local_shape_of_aprioriBound` is thin).**  Recorded in the corollary docstring and
  here: whenever `‖u₀‖ + 1 ≤ R` the corollary's full conclusion follows from
  `Source.OrdinaryForcedLocal.exists_local` **alone** — no `HasAprioriBound`, no `hu₀`, no `hR`
  (reviewer probe `/tmp/rev139/strength.lean`, exit 0).  Its only added content is the regime
  `R < ‖u₀‖ + 1`, and even there `T = S` is invisible in a bare `∃ T` type; the horizon-pinning
  deliverable is `localTheory_on_prescribed_horizon` (`T = S` in the type).
* **F5 (no instance of `HasAprioriBound` anywhere).**  Confirmed and made explicit: `HasAprioriBound`
  occurs only in `Horizon.lean` and `axioms_a3_l2.lean` and is never instantiated (its supply is
  A3's *output*, gated on `D-euler-pairing` → A3-L1·k → `Kbnd`).  So `localTheory_on_prescribed_horizon`
  inherits exactly the status of `forced_global_of_bound_unconditional`: **"A3-L2 DONE" is naming +
  fixing `T := S`, not new mathematical reach** — nothing became provable that was not provable
  before this lane.
* **F7 (filename `Horizon.lean` was pre-reserved) — merge-time, for the lead.**
  `REVIEW_A3_FORCE.md:258/:305` and `A3_SPLIT.md` §3.5 reserved `Section4/A01/Horizon.lean` for
  the Grönwall-instantiation lane; those files/sections live on `origin/erenup/integration`
  (added by PR #140/lane 137, **after** this lane's merge-base `9a68411`) and are **not present
  in this worktree**, so they cannot be edited here.  The Grönwall lane (142) has since used
  `Section4/A01/GronwallInstance.lean`, so there is **no filename clash**.  `REVIEW_A3_FORCE.md`
  is a merged historical record; its stale pointer is left as history — the lead refreshes the
  §3.5 pointers on integration at merge.
* **F8 / F9 (bookkeeping, merge-time).**  In this worktree the stale §(d) bullet
  ("A3-L2 — dissolved…") is fixed to DONE with theorem names.  The `A3_SPLIT.md` merge conflict
  the review flags is one hunk (base rows A3-L1·k / A3-L1·f / A3-L2): the lead takes
  integration's `A3-L1·k` and `A3-L1·f` (137) and this lane's `A3-L2`.  The §3.5 "ready→DONE"
  refresh is on integration, not here.
