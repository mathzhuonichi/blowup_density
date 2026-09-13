# A02 unit U7 — `exists_maximal` and `maximal_unique` (lane 064)

Module: `formalization/NSFormalization/Section4/A02/Maximal.lean`.
Conformance: `research/A02/axioms_u7.lean`.
Spec fields: `research/A02/Spec.lean:421-423` (`exists_maximal`) and `:429-434`
(`maximal_unique`), over `IsMaximalSolution` (`Spec.lean:210-214`) and
`presingularTimes` (`Spec.lean:168-169`).

Both build clean, `sorry`-free; `#print axioms` on every declaration is exactly
`propext, Classical.choice, Quot.sound`.

## What was proved

* `exists_maximal_of_localSolution (horizon) (localSolution) : … → ∃ u p, IsMaximalSolution ν a f u p`
  — the spec field, with the A01 existence clause taken as an explicit
  hypothesis (same shape as `Order.lean`'s `horizon_le_lifespan_of_localSolution`
  and `MaximalPartial`'s `horizon_le_lifespan`).
* `maximal_unique` — the spec field verbatim, with **no** A01 hypothesis (see
  "A01 dependency" below).
* Supporting: `SolExists`, `chosenSol`, `uField`, `pField` (the pointwise
  directed union) and the two coherence lemmas `uField_eq`, `pField_eq`.

## The construction and its well-definedness

`u = uField ν a f` and `p = pField ν a f` are defined **pointwise by classical
choice**.  For a spacetime point `z`, `SolExists ν a f z.1` says some classical
solution lives on a horizon `> z.1`; if so, `chosenSol` picks one (`Classical`),
and

* `uField z := (chosenSol …).velocity z`,
* `pField z := (chosenSol …).pressure z − (chosenSol …).pressure (z.1, 0)` — the
  **basepoint-normalized** pressure at the fixed basepoint `0 : Space`.

Well-definedness is *not* imposed as a hypothesis and no explicit "union" set is
built.  Instead the two coherence lemmas prove directly that the pointwise value
agrees with *every* solution on its slab:

* `uField_eq hν w ht x : uField ν a f (t,x) = w.velocity (t,x)` for any
  `w : ClassicalSolutionR ν a f S` and `t ∈ Ico 0 S`.  Proof: the chosen solution
  `w'` (horizon `> t`) and `w` are both solutions of `(ν,a,f)`, so
  `velocity_unique_core` (U2) makes them agree on `Ico 0 (min (horizon w') S)`,
  which contains `t`.
* `pField_eq hν w ht x : pField ν a f (t,x) = w.pressure (t,x) − w.pressure (t,0)`.
  Proof: `pressure_gauge_core` (U3) gives `PressureGaugeEquivOn` of `w'` and `w`
  on the common interval; `normalizePressure_gauge_invariant` collapses that gauge
  freedom — two gauge-equivalent pressures have the *same* basepoint
  normalization — so the chosen and `w`'s normalized values coincide at `t`.

This is why the reviewer-flagged **pressure obligation** (COMPARISON §1.3, I3′)
is met: `pressure_gauge` alone leaves one `c : ℝ → ℝ` per pair of horizons and
"take `p` from any longer solution" is ill-defined; normalizing at a single fixed
basepoint removes the `c` entirely.

### `exists_maximal`

* Positivity `0 < maximalLifespanR`: from `localSolution` (A01) at `(ν,a,f)`,
  `horizon_le_lifespan` and `ENNReal.ofReal_pos` on the positive horizon.
* For each `S` with `0 < S`, `ofReal S < T_max`: `exists_horizon_gt_of_lt_lifespan`
  (U6) enters the `iSup` from below to get a solution on `[0,S')`, `S' > S`;
  `ClassicalSolutionR.restrict` shrinks it to `wS` on `[0,S)`; then
  `exists_eq_fields_of_agree (wS.normalizePressure 0) u p (uField_eq …) (pField_eq …)`
  produces a solution with `velocity = u` and `pressure = p` literally.

### `maximal_unique`

For `t ∈ presingularTimes` (`0 ≤ t`, `ofReal t < T_max`), pick a horizon `S`
strictly between `t` and `T_max` (helper `common`: `exists_horizon_gt_of_lt_lifespan`
gives `S' > t`, then `S := (t+S')/2` has `t < S < S'` and
`ofReal S < ofReal S' ≤ T_max`).  Both `IsMaximalSolution` hypotheses hand over
solutions `w₁, w₂` on `[0,S)` with `wᵢ.velocity = uᵢ`, `wᵢ.pressure = pᵢ`.
`velocity_unique_core` on `[0,S)` gives `u₁ = u₂` at `t`; for the pressure, the
single global gauge `c t := p₂(t,0) − p₁(t,0)` works at every presingular `t` by
`normalizePressure_gauge_invariant` applied to `pressure_gauge_core w₁ w₂`.

## The outside-the-slab issue — how it was resolved

The task flagged the worry that `IsMaximalSolution` demands `w.velocity = u` as an
equality of *total* functions on `ℝ × Space`, while a solution's fields constrain
only the slab `Ico 0 S ×ˢ univ`.  Resolution: `Restrict.lean`'s congruence
constructor `exists_eq_fields_of_agree` already handles this.  It takes agreement
of `u,p` with a solution `w` **only on the slab** and returns a solution `w'`
whose `velocity`/`pressure` fields are the *given* `u`/`p` literally (`w'.velocity
:= u` in `ClassicalSolutionR.congr`), reproving every structure field from the
on-slab agreement (`velocity_smooth.congr`, `momentum` via
`navierStokesResidual_eq_of_eqOn` at interior times, etc.).  So the global `u,p`
need never match any `wS` off its slab; the constructor rebuilds a genuine
solution carrying the literal global fields.  The literal-fields clause is proved
in full — the germ-only fallback was **not** needed.

## A01 dependency (finding)

`exists_maximal` genuinely needs A01: without a local solution, `maximalLifespanR`
can be `0` and the predicate's positivity conjunct fails.  Taken as the explicit
hypothesis `localSolution`, per instruction.

`maximal_unique` needs **no** A01 hypothesis.  Its type carries none (Spec.lean),
and its proof draws the required solutions from the two `IsMaximalSolution`
hypotheses directly; `exists_horizon_gt_of_lt_lifespan` (U6, order-theoretic only)
supplies the intermediate horizon.  It is therefore stated as the plain spec field
— a stronger conformance than the A01-hypothesis shape.  Recorded because the U7
row of COMPARISON.md lists ⟪A01:solution⟫ as a dependency of the whole unit; that
is accurate for `exists_maximal` but conservative for `maximal_unique`.

## What failed / friction

* `dif_pos` is **deprecated** in this toolchain (v4.34.0-rc2, since 2026-07-21) in
  favour of `dite_eq_left` (a drop-in with the identical signature,
  `Init/Core.lean:1204`).  First compile emitted two deprecation warnings; switched
  both `dif_pos hex` to `dite_eq_left hex`.  Clean afterwards.
* Destructuring `ht : t ∈ presingularTimes ν a f` via `ht.1` does not resolve —
  dot-notation projection does not unfold `Set.mem`/`setOf` to reach the `And`.
  Fixed by `obtain ⟨ht0, htlt⟩ := ht` (rcases whnf-reduces through the `Set`
  membership) and threading `ht0`, `htlt` into the `common` helper explicitly
  rather than passing the packaged membership.
* Deciding `SolExists` in the `dite` needs a `Decidable` instance;
  `attribute [local instance] Classical.propDecidable` supplies it (kept the axiom
  set to the standard three).
* The `(t,x).1`-vs-`t` and `z`-vs-`(z.1,z.2)` defeq gaps were avoided by (a) stating
  the coherence lemmas over explicit `(t, x)` points and constructing
  `hex : SolExists ν a f t` (letting the `dite_eq_left`/expected-type elaboration
  bridge the condition `SolExists ν a f (t,x).1`), and (b) discharging the two
  congruence side-goals in `exists_maximal` with `show … ; exact …`, which forces
  the `wS.normalizePressure 0` field projections to reduce by defeq.  No `simp`
  gymnastics were needed.

## Commands

```
cd verification && lake build NSFormalization.Section4.A02.Maximal      # ✔ built (3.6s)
cd verification && lake env lean ../formalization/NSFormalization/Section4/A02/Maximal.lean   # no output, exit 0
cd verification && lake env lean ../research/A02/axioms_u7.lean          # 4×[propext, Classical.choice, Quot.sound], exit 0
```


## Review fixes (lead, 2026-09-13)

- Reviewer (`REVIEW_U7.md`) reproduced `ht.1`/`ht.2` on a `presingularTimes` membership: dot-projection *does* resolve through `Set.mem`/`setOf`; the `obtain` rewrite was a stylistic choice, not a necessity. The snag record above is therefore misdiagnosed; the shipped proof is unaffected.
