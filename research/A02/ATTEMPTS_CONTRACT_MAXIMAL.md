# A02.maximal_partial — contract registration record (lane 061)

Registers the **already-proved part** of `MaximalSolutionAPI`
(`research/A02/Spec.lean`) beyond the registered uniqueness half
(`A02.uniqueness`).  Three new files, one registry entry, one work-item edit.

* `verification/Contracts/V1/MaximalPartial.lean` — `structure MaximalPartialAPI`.
* `verification/Bindings/MaximalPartial.lean` — binds it to the merged proofs.
* `verification/Tests/MaximalPartial.lean` — `checkedMaximalPartial` + axiom audit.

## Which fields (11 total: 1 carried record + 10 proved fields)

| field | source theorem | module |
|---|---|---|
| `uniqueness : Contracts.V1.Uniqueness.UniquenessAPI` | the registered `A02.uniqueness` binding `Bindings.uniqueness`, carried structurally | — |
| `restrict` | `exists_restrict` | Restrict.lean |
| `pressure_normalization` | `exists_pressure_normalization` | Restrict.lean |
| `horizon_le_lifespan` | `horizon_le_lifespan_of_localSolution` | Order.lean |
| `lifespan_le_iff` | `lifespan_le_iff` | Order.lean |
| `lifespan_le_iff_no_extension` | `lifespan_le_iff_no_extension` | Order.lean |
| `lifespan_ge_of_forall_shorter` | `lifespan_ge_of_forall_shorter` | Order.lean |
| `regularThrough_iff` | `regularThrough_iff` | Order.lean |
| `referenceLifespan` | `referenceLifespan` | Order.lean |
| `patch` | `patch` | Patch.lean |
| `lifespan_le_of_unbounded` | `lifespan_le_of_unbounded` | Patch.lean |

Field types are copied **verbatim** from `Spec.lean` (they are already written in
`Contracts.V1.Data` vocabulary there), with the single deliberate change that
`horizon_le_lifespan` is stated in the **Order.lean form**: the A01
`LocalTheoryAPI.solution` clause is an explicit hypothesis
`(horizon) (localSolution) → …`, not an ambient A01 field.  A docstring records
that A01 will discharge that hypothesis.  `limsupLeft` and `speedENorm`
(`⟪D01:limsupLeft⟫`, `⟪D01:normLinfty⟫`, which `Data.lean` does not define) are
restated token-for-token from `Spec.lean:135-136,148-149`; the module docstring
names every excluded field (A01 interface, `IsMaximalSolution`, `exists_maximal`,
`maximal_unique`, `restart`/`restart_datum`/`restart_force`,
`insertion_lifespan_eq`).

`MaximalPartialAPI` elaborates as a `Prop` (every field, including the carried
`UniquenessAPI`, is propositional), so the binding and `checkedMaximalPartial`
are `theorem`s, matching `A02.uniqueness`.

## Carrying the registered record

`uniqueness : Contracts.V1.Uniqueness.UniquenessAPI` is a field, discharged in the
binding by `uniqueness := uniqueness` (the registered `Bindings.uniqueness`
theorem in the same flat namespace).  This is the `InsertionFamilyAPI`-carries-
`ScalingAPI` pattern.  The bare identifier resolves to the sibling theorem, not to
the field — confirmed to compile.

## Transport: how `maximalLifespanR` / `RegularThrough` crossed the two `ClassicalSolutionR`s

`Contracts.V1.Data.ClassicalSolutionR` and `Section4/A02`'s restatement are
distinct inductive types, so no `rfl` bridge exists for the structure.  Following
`Bindings/Uniqueness.lean`, the binding moves solutions **field by field**:

* forward `uniqueness_toA02` (reused from `Bindings.Uniqueness`);
* inverse `maximalPartial_ofA02` (added here; ten bare projections) — needed
  because `restrict`, `patch` and `pressure_normalization` *produce* a solution,
  so the conclusion must be converted `A02 → Data`.

Both are plain structure literals; `(ofA02 w).velocity/pressure = w.velocity/pressure`
and the round-trip `(ofA02 (toA02 u)).velocity/pressure = u.velocity/pressure` are
`rfl` (four `example`s in §1 of the binding).  Every field type of the two copies
is definitionally equal, which is what makes the field assignments typecheck; the
predicate objects `initialClassR`, `MemForceR`, `PressureGaugeEquivOn` and the two
restated norms `limsupLeft`/`speedENorm` are token-identical and pass by
definitional unfolding (the two norms also get explicit `rfl` bridges in §0).

The 032 reviewer (`research/A02/REVIEW_U4U6.md` finding 1) verified that **only two**
objects resist `rfl` because they quantify over the solution class.  Both are
proved once and reused:

* `maximalPartial_maximalLifespanR_eq : A02.maximalLifespanR = Data.maximalLifespanR`
  — the **iSup congruence**.  `simp only [maximalLifespanR …]` unfolds the double
  `⨆` and `le_antisymm` + `iSup_le` + `le_iSup_of_le` transports each realized
  horizon by `ofA02`/`toA02` on the `Nonempty` witness.
* `maximalPartial_regularThrough_iff : A02.RegularThrough ↔ Data.RegularThrough`
  — the **one `Iff`**, `∃ δ > 0, Nonempty (solution on [0,T+δ))`, transported by
  the `Nonempty` equivalence.

Their corollaries `maximalPartial_nonempty_iff` (one line from the two
conversions) and `maximalPartial_isEmpty_iff` (`not_nonempty_iff` twice) carry the
`Nonempty`/`IsEmpty` occurrences in the order-theoretic fields.

## What used a `by` block, and why

The transport lemmas of §2 are the acknowledged unavoidable short proofs.  In §3
the field bodies are term-mode applications of the A02 theorems up to the
conversions, using `le_of_le_of_eq` / `le_of_eq_of_le` / `lt_of_lt_of_eq` to swap
`A02.maximalLifespanR` for `Data.maximalLifespanR` in `≤`/`<` conclusions.  Three
fields whose statement is an `Iff` over *both* `maximalLifespanR` and the solution
class (`lifespan_le_iff`, `lifespan_le_iff_no_extension`, `regularThrough_iff`) use
a one-line `by rw [← transport…]; exact (A02 theorem) …` — pure plumbing that
rewrites the contract goal back into A02 vocabulary, no mathematics.  `forall_congr'`
+ `imp_congr` transport the `∀ S, Nonempty/IsEmpty …` right-hand sides.

## What did not fit (out of scope, each owed by a later lane)

Not proved on this branch, hence excluded from the structure and named in the
module docstring: the restated A01 interface fields `horizon`, `localSolution`,
`horizonLowerBound`; the `IsMaximalSolution` predicate and the fields depending on
it (`exists_maximal`, `maximal_unique`); the quantitative restart (`restart`,
`restart_datum`, `restart_force`); and Theorem 4.2's packaged identification
`insertion_lifespan_eq`.  The `L^∞` embedding `‖z‖_∞ ≤ C‖z‖_{H²}` of `eq:Rproduct`
(edge `A03 → A02`) is a step of `lifespan_le_of_unbounded`'s discharging proof, not
a field.

## Gates (all green)

* `lake build Contracts.V1.MaximalPartial Bindings.MaximalPartial Tests.MaximalPartial`
  — `Build completed successfully`; `checkedMaximalPartial: checked; standard
  logical axioms only`.
* `make check` — `test_contract_policy` 13/13 OK; `check_work_queue` 30 items
  consistent; `check_contracts` closure includes `Tests.MaximalPartial`.
* `make test` — every registered contract checked, standard logical axioms only.
* `make test-mutations` — `implementation_refactor` accepted; `admitted_proof`,
  `extra_axiom`, `weakened_hypothesis` rejected as required.
* `check_contracts.py --base-ref origin/erenup/integration` — exit 0,
  `base_compatibility_checked: true` (no stable contract/spec/test changed).
* Forbidden-token scan (`sorry|admit|axiom|native_decide|maxHeartbeats`) over the
  three new files — empty.
