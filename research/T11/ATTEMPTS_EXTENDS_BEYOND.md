# ATTEMPTS — lane 337 (T11 U14 `extendsBeyond` + U16 `lifespanInfiniteOfLocallyFinite`)

Module `formalization/NSFormalization/Section3/T11/ExtendsBeyond.lean`.
Both targets closed; no `sorry`, no `axiom`, no `set_option maxHeartbeats`.
The module compiled on the first `lake build` and `lake env lean` reports zero
warnings, so this file is mostly a record of the *decisions* rather than of
failed paths. The three that were genuinely weighed are below.

## 0. Residual conditions (exact statements)

No new `def … : Prop` was introduced. Both theorems carry exactly two binders
beyond the field's own quantifiers:

1. `H : PeriodicQuantitativeLocalInput'`
   (`Section3/T11/LocalExistence.lean:24`), the single named input of the T11
   split, consumed only through lane 332's `restartBeyond`. Verbatim:

   ```
   ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
     ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
       ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
         (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
           ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
   ```

2. `hHigh`, the `higherOrderBound` field of `PeriodicContinuationAPI` copied
   token for token from `research/T11/probes/api_on_canonical.lean:112-121`:

   ```
   ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
     ∀ (f : SpaceTimeField), f ∈ forceClassT → ∀ (S : ℝ), 0 < S →
       ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
         SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
           ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
             ∀ t ∈ Ico (0 : ℝ) S, periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M
   ```

   It is an **explicit theorem binder, not a named input**: the peeling rule
   allows one name and that name is already `PeriodicQuantitativeLocalInput'`.
   It is discharged by lane 322's `higherOrderBound_of_energyInequality`
   (probe example 3 chains the two, which is what proves the binder is
   token-identical to U12's conclusion rather than a convenient restatement),
   whose own hypothesis `hRhigh` is being closed by lanes 335/336.

Lane 323's `PeriodicMaximalExistenceInput` is **not** a third condition: it is
*proved* here from `H` (`periodicMaximalExistenceInput_of_input`), so
`exists_maximal_of_input` puts U15's existence field on the same single name.

## 1. `horizon_le_lifespan` is not usable pointwise (decision, not a failure)

The split and the brief point at `Uniqueness.horizon_le_lifespan` for the final
step of U16. It cannot be applied: its signature is

```
theorem horizon_le_lifespan {horizon : ℝ → SpatialField → SpaceTimeField → ℝ}
    (solution : ∀ ν, 0 < ν → ∀ a ∈ initialClassT, ∀ f ∈ forceClassT,
      ClassicalSolutionT ν a f (horizon ν a f)) : …
```

i.e. it needs a *global family* of solutions at one global horizon function.
U16 has a single solution at a single datum, on the horizon `S + δ` produced by
the continuation. Instantiating `horizon := fun _ _ _ ↦ S + δ` would require a
solution at that horizon for every admissible `(ν, a, f)`, which is the global
existence statement itself; an `if`-dispatch on the one datum would add no
content. The pointwise fact is a one-liner off the same supremum, so the module
exports it as `lifespan_ge_of_horizon` and builds `lifespan_ge_of_extends` (the
export the brief asks for) on top of it. `horizon_le_lifespan` stays the right
lemma for the *API assembly* (U17), where the global `solution` field exists.

## 2. `set S := (maximalLifespanT ν a f).toReal` — the self-referential rewrite

First shape of the U16 contraposition used `set L := maximalLifespanT ν a f`
and then `rw [← hofS] at hle` with `hofS : ENNReal.ofReal L.toReal = L`. The
`←` direction rewrites every occurrence of `L`, including the one inside
`L.toReal`, producing
`ENNReal.ofReal ((ENNReal.ofReal L.toReal).toReal + δ) ≤ ENNReal.ofReal L.toReal`.
Fix: abbreviate the *real* `S := (maximalLifespanT ν a f).toReal` instead, so
`hofS : ENNReal.ofReal S = maximalLifespanT ν a f` has an atomic left-hand
side, and rewrite forwards inside a `have` whose statement is already the
desired `ENNReal.ofReal (S + δ) ≤ ENNReal.ofReal S` (the `S + δ` argument does
not match the pattern, so only the right-hand side moves).

## 3. `m = 1` of `hHigh` lands at `((1 : ℕ) : ℝ)`, `restartBeyond` wants `(1 : ℝ)`

`hHigh … 1` produces `periodicSobolevENorm ((1 : ℕ) : ℝ)`; `restartBeyond`'s
`H¹` ball is spelled `periodicSobolevENorm 1` with a real numeral. Closed by
`simpa only [Nat.cast_one]`. (The analogous `((2 : ℕ) : ℝ)` vs `(2 : ℝ)` in
`squaredHTwoIntegralT_ne_top_of_lt` needs nothing — `w.sobolev 2` and
`continuousOn_torusSobolevNormAt_velocity w 2` unify with the real numeral by
defeq, as they already do in `HighOrder.running_hTwo_integral_le`.)

## 4. Non-vacuity: why not `nonzero_forced_witness'`

Lanes 321/332 use `nonzero_forced_witness'` for non-vacuity, but its force `g`
is only known to be smooth, periodic and `L¹_t H^m`-bounded — **not** a member
of `forceClassT`, which additionally demands compact time support inside
`Ioi 0`. Both targets here quantify over `f ∈ forceClassT`, so that witness
cannot inhabit their hypotheses. The module therefore carries its own witness,
`constantVelocitySolutionT`: a constant divergence-free velocity with zero
force and zero pressure, a classical torus solution on *every* positive
horizon (the fieldwise proof is the one already used in
`research/T11/probes/galilean_classes_closes.lean`, generalized from the fixed
horizon `1`). It inhabits, unconditionally on `H`, all hypotheses of both
targets at once: `a ∈ initialClassT`, `0 ∈ forceClassT`, `u (0,0) ≠ 0`,
`SolvesBelowT`, `squaredHTwoIntegralT 1 u ≠ ⊤`, `IsMaximalPeriodicSolution`,
and the locally-finite criterion at every `S`.

## 5. A sharpness fact that fell out: the criterion lives at the endpoint

`squaredHTwoIntegralT_ne_top_of_lt` proves that for any classical solution on
`[0, T)` and any `S < T` the squared `H²` lintegral over `(0, S)` is finite,
with no hypothesis: the `H²` profile is continuous on `[0, T)`, hence bounded on
the compact `[0, S]`, and `volume (Ioo 0 S) < ⊤`. Probe example 6 upgrades this
to: for a maximal solution the *strict* form of U16's criterion hypothesis
(`ofReal S < maximalLifespanT` instead of `≤`) is automatic, so a `<` variant of
the field would carry a vacuous hypothesis and assert global regularity
outright. This is the machine-checked version of `RECONCILIATION.md` §2's claim
that the `≤` is load-bearing, and it is exactly why U16 applies the hypothesis
at the single point `S = L.toReal`.

## Negative / not attempted

- No attempt was made to discharge `hHigh` here; that is U12 (lanes 322 +
  335/336) and duplicating it would have produced a second, weaker copy.
- No attempt was made to weaken `restartBeyond`'s `H¹` ball. The manuscript
  `H¹` restart is kept as the split requires; if U10 ever has to narrow to a
  fixed-force `H⁷` statement the narrowing happens there, and U14/U16 inherit
  it without a change of statement here.
