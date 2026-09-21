# R45 — `cor:Rclasses` — reconciled comparison

Paper statement and proof: `paper/sections/04-whole-space.tex:194-199`.
Inherited Theorem 4.1 clauses: `:8-13`.  Binding rulings:
`research/R45/RECONCILIATION.md`.

Inputs:

- lane 238: `DraftA.lean`, `COMPARISON_A.md`, `REPORT_238.md`;
- lane 239: `DraftB.lean`, `COMPARISON_B.md`, `REPORT_239.md`.

Output: `Spec.lean`, structure
`BlowupDensity.R45.Draft.RClassesAPI`, with exactly four fields and no local
statement definition.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Draft A | Draft B | Reconciled field / shape | Ruling |
|---|---|---|---|---|
| `04-whole-space.tex:194-195`: Theorem 4.1 remains valid after replacing `F_R` by `F_c` or `F_rd` | Separate compact/rapid copies: `compactDenseBelow`, `compactZeroIff`, `compactReferenceApproximation`, `rapidDenseBelow`, `rapidZeroIff`, `rapidReferenceApproximation` | One copy parameterized by `Y`, guarded by `Y = forceClassCompact ∨ Y = forceClassRapid` | `density`, `zeroIff`, `regularReference`, each with the guarded `Y` binder first | **B**. `breakdownSetIn` and `RelativelyDense` are already class-parametric, and the disjunction prevents over-generalization to arbitrary subclasses. |
| `:8-10`, inherited by `:195`: for every fixed `a ∈ X_R`, relative density below `s_q` | `compactDenseBelow` / `rapidDenseBelow`; `q : ℕ`; local `rClassesThreshold` | `density`; `q : ℝ`; `ENNReal.ofReal q`; inline `2/q-3/2` | `density`; `q : ℝ≥0∞`; `(q = 1 ∨ q = 2)`; `s < criticalOrder q.toReal`; `RelativelyDense q s Y (breakdownSetIn Y ν a T)` | Parametric shape from B; exponent convention from neither draft, but from the binding reconciliation and shared R41/R46 convention. |
| `:8,11`, inherited by `:195`: zero-datum density iff below `s_q` | `compactZeroIff` / `rapidZeroIff` | `zeroIff` | `zeroIff`, guarded by the same class disjunction and using the same ENNReal exponent convention | **B**, with reconciled exponent. The threshold is inside the `↔`, so the critical/supercritical non-density direction remains present. |
| `:195,198`: “in particular” for every fixed `a ∈ S_σ` in the rapid-decay class | `rapidSchwartzDenseBelow` plus a separate `rapidSchwartzReferenceApproximation` | `schwartzDensity` only; zero iff supplied by the rapid instance of `zeroIff` | `schwartzDensity` only, directly assuming `a ∈ initialClassSchwartz` and concluding relative density in `forceClassRapid` | **B**. G4 proves `S_σ ⊆ X_R`; a duplicate Schwartz rider is dropped. The complete zero classification is already the rapid instance of `zeroIff`. |
| `:13`, inherited by `:195`: around every reference regular through `T`, preserve the datum and earlier history, have singularity exactly at `T`, and converge in `E_T` | `compactReferenceApproximation` / `rapidReferenceApproximation` through local `HasReferenceApproximationRider`; arbitrary cutoff `S<T`; separate force/energy radii | Inline `regularReference`; arbitrary cutoff `τ<T`; separate radii; one force and one solution witness | `regularReference`, B's inline epsilon form with five retained conjuncts: `f∈Y`, exact lifespan, force closeness, energy closeness, history equality | **B**, inline; no new local predicate requiring registration. One pair of witnesses satisfies all conclusions simultaneously. |
| `:13`, “same initial velocity” | Same index `a` on the reference and approximating `ClassicalSolutionR` | Same | Same | Agreement. The registered solution type supplies the pointwise initial condition, so no redundant conjunct is added. |
| `:36`: inserted histories agree through `T-2ε²`, giving arbitrarily long earlier history | Rider quantifies arbitrary `0≤S<T` (although its prose also discusses the insertion rate) | Quantifies arbitrary `0≤τ<T` inline | `∀ τ, 0 ≤ τ → τ < T → ...` before the two radii | **B's binder spelling**, mathematically agreed by both drafts and explicitly selected by the reconciliation; the scale-dependent cutoff is proof mechanism, not API shape. |
| `:195,198`: reference datum for the inherited theorem | General rider has `a ∈ initialClassR`; A additionally duplicates the rapid rider for `a ∈ initialClassSchwartz` | `a ∈ initialClassR ∨ a ∈ initialClassSchwartz` | `a ∈ initialClassR` only | Reconciliation decision 3. The disjunction is redundant after G4; the direct Schwartz density clause remains separate. |
| `:35`: unbounded speed for Theorem 4.2's inserted solution | Not included in the R45 rider | Last conjunct of `regularReference` | Dropped | Reconciliation decision 3. `cor:Rclasses` and Theorem 4.1's rider do not restate this conclusion; it belongs to R42. Exact lifespan at `T` is retained. |
| `:198`: compact correction preserves both selected force classes | Witness membership `f ∈ forceClassCompact` / `f ∈ forceClassRapid` | Witness membership `f ∈ Y` | `f ∈ Y`, and every density target is `breakdownSetIn Y ...` | Agreement on the mathematical consequence. Compactness of the difference is proof mechanism and is not added as a corollary field. |
| `:198`: no compactness requirement on a nonzero reference velocity or pressure | No support assumption on `v` | No support assumption on `v` | No support assumption on `v` | Agreement. Only the reference force is required to lie in the selected ambient class. |

## Exact reconciled quantifier order

The order in `Spec.lean` follows Draft B where the reconciliation selects B's
parametric shape, with only the mandated exponent and rider changes.

| Field | Quantifier order before the conclusion |
|---|---|
| `density` | `Y`; `Y=F_c ∨ Y=F_rd`; `ν`; `0<ν`; `T`; `0<T`; `q : ℝ≥0∞`; `q=1 ∨ q=2`; `s`; `a`; `a∈X_R`; `s < criticalOrder q.toReal` |
| `zeroIff` | `Y`; class disjunction; `ν`; `0<ν`; `T`; `0<T`; `q`; exponent disjunction; `s` |
| `schwartzDensity` | `ν`; `0<ν`; `T`; `0<T`; `q`; exponent disjunction; `s`; `a`; `a∈S_σ`; `s < criticalOrder q.toReal` |
| `regularReference` | `Y`; class disjunction; `ν`; `0<ν`; `T`; `0<T`; `q`; exponent disjunction; `s`; subcriticality; `a`; `a∈X_R`; `g`; `g∈Y`; `δ`; `0<δ`; `v : ClassicalSolutionR ν a g (T+δ)`; `τ`; `0≤τ`; `τ<T`; `r η : ℝ≥0∞`; `0<r`; `0<η`; then `f`, membership, and `u` |

The `regularReference` conjunct order is also fixed: exact lifespan `T`, force
distance `< r`, energy distance `< η`, then pointwise velocity history on
`[0,τ]`.  The dropped terminal-speed conjunct does not appear.

## Registered vocabulary and non-vacuity

| Field | Registered objects | Why the statement is substantive |
|---|---|---|
| `density` | `criticalOrder`, `RelativelyDense`, `breakdownSetIn` | Every target in `Y` and every positive radius require a witness both in `Y` and with lifespan at most `T`. |
| `zeroIff` | same, at `fun _ => 0` | The reverse implication asserts failure of density at and above the threshold; there is no outer subcritical hypothesis. |
| `schwartzDensity` | `initialClassSchwartz`, `forceClassRapid` | Witnesses stay in `F_rd`; the result is not weakened to density by arbitrary `F_R` forces. |
| `regularReference` | `ClassicalSolutionR`, `maximalLifespanR`, `forceSobolevENorm`, `energyENorm` | The same `f,u` have exact lifespan, both independently prescribed strict errors, and exact history. ENNReal norms are never converted with `.toReal`, so an infinite norm cannot pass a finite-radius bound. |

No field is an unspecified `Prop`, `True`, or an existential with a trivial
body.  The class disjunction is an explicit finite choice, not a free ambient
class hypothesis.

## Definitional checks requested by the reconciliation task

`Spec.lean` contains and elaborates both checks:

```lean
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl
```

Thus both registered abbreviations are definitionally, not merely
propositionally, their stated `CompletedDenseVia` specializations.  They remain
outside `RClassesAPI`, because `cor:Rclasses` concerns the relative topology on
the smooth subclasses; completed-space density begins in the following
Proposition 4.6 (`04-whole-space.tex:218-228`).

## Proof dependencies

(a),(b): Theorem 4.1's arguments with `Y` replaced: the density branch needs the inserted forces to stay in `F_c`/`F_rd` (G3 rapid-class closure, lane 234; `F_c` closure from
`forceDifference_compact`), the non-density branch is inherited from `F_R` via `Y ⊆ F_R` (G2, lane 234) and `breakdownSetIn Y ⊆ breakdownSetR`. (c): G4 + (a). (d): lane 233's record + R42 fields.

## Proof status after lane 252

`verification/Bindings/CompactClassDensity.lean` proves the following two
instances, with the binder order copied from `Spec.lean` after specializing
`Y = forceClassCompact`:

- `density_compact`: the compact instance of `density`;
- `zeroIff_compact`: both directions of the compact instance of `zeroIff`.

It also proves the two compact-class adapters used by those instances:
`memForceCompact_add_memForceCompact` and
`memForceR_of_memForceCompact`.  The latter discharges `F_c ⊆ F_R` from the
already registered D01 result, so no lane-234 supplier hypothesis is needed
for the compact class.  The rapid instances of `density` and `zeroIff`, plus
`schwartzDensity` and both instances of `regularReference`, remain outside
this lane.

## Proof status after lane 257

`verification/Bindings/RapidClassDensity.lean` now proves every rapid-class
specialization, with binder and conjunct order copied from `Spec.lean`:

- `density_rapid`, using G2 to enter `F_R` and G3 to retain the inserted force
  in `F_rd`;
- `zeroIff_rapid`, including the critical/supercritical non-density direction;
- `regularReference_rapid`, with one pair of witnesses satisfying class
  membership, exact lifespan, both strict norm bounds, and the requested
  history equality;
- `schwartzDensity`, directly from G4 and `density_rapid`.

The same module also supplies the complete guarded parametric declarations
`density` and `zeroIff` by case analysis between lane 252's compact instances
and lane 257's rapid instances.  Lane 254's `CompactClassRider.lean` is not on
this lane's base, so the corresponding parametric `regularReference`
combination is intentionally left to the registration lane as requested.

`research/R45/axioms_rapid_class.lean` reports exactly
`[propext, Classical.choice, Quot.sound]` for all six declarations and checks
the rapid density and rider at concrete parameters `ν = T = 1`, `a = g = 0`.
Thus the remaining R45 proof work on this base is only the compact-rider merge
and final four-field API registration; no rapid-class mathematical field is
open.

## Open questions for the owner

No statement-level question remains: the binding reconciliation fixes all four
field names, ambient-class shape, exponent type, threshold spelling, rider
quantifiers, and retained/dropped conjuncts.

Two bookkeeping questions do not change `Spec.lean`:

1. `RECONCILIATION.md`'s introductory sentence calls Draft A a seven-field
   record, but the copied source and `REPORT_238.md` contain eight fields (the
   six per-class fields plus two Schwartz-specialized fields).  Should that
   prose count be corrected when the lead next edits the reconciliation note?
2. Should the eventual registration/conformance lane repeat the two requested
   `CompletedDense* = CompletedDenseVia ...` `rfl` checks, or is keeping them in
   this research specification sufficient?  They are definitional checks only
   and are not fields of R45.

## Lead note (review 257, 2026-09-17)

The statements above about lane 254 being absent describe the branch **before** the integration merge `f6e879f`; after it, `Bindings/CompactClassRider.lean` (254, PR #247) is present. Only the final guarded `regularReference` assembly (`Or.elim` of 254/257) and the API registration remain — done in lane 262.
