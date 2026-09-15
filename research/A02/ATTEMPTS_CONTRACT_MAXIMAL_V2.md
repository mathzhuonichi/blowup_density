# A02.maximal_partial_v2 — contract registration record (lane 069)

Registers **version 2** of `A02.maximal_partial`: the version-1 record
`MaximalPartialAPI` (`Contracts/V1/MaximalPartial.lean`) extended by the two
maximal-solution fields of lane 064 (unit **U7**, `Section4/A02/Maximal.lean`).
V1 stays untouched. Three new files, one registry entry, one work-item edit.

* `verification/Contracts/V2/MaximalPartial.lean` — `structure MaximalPartialV2API`
  (`extends` V1), plus the two restated defs `presingularTimes`, `IsMaximalSolution`.
* `verification/Bindings/MaximalPartialV2.lean` — binds it to lane 064's proofs,
  compatibility binding `maximalPartial_of_v2`.
* `verification/Tests/MaximalPartialV2.lean` — `checkedMaximalPartialV2` + axiom audit.

## Which fields (2 new; V1's 11 inherited verbatim via `toMaximalPartialAPI`)

| field | source theorem | shape |
|---|---|---|
| `exists_maximal` | `Section4/A02/Maximal.lean` `exists_maximal_of_localSolution` | spec `exists_maximal` (`Spec.lean:421-423`) **with the A01 `localSolution` clause as an explicit hypothesis**, same shape as V1's `horizon_le_lifespan` |
| `maximal_unique` | `Section4/A02/Maximal.lean` `maximal_unique` | spec `maximal_unique` (`Spec.lean:429-434`) **verbatim**, no A01 input |

Both field types are copied from `Spec.lean` (already written in `Contracts.V1.Data`
vocabulary), with the single deliberate change that `exists_maximal` takes
`(horizon) (localSolution) → …` explicitly, mirroring V1's `horizon_le_lifespan`
and the way lane 064's `exists_maximal_of_localSolution` is proved. A01 will
discharge that hypothesis at `LocalTheoryAPI.solution`; the clause is genuinely
used (`0 < maximalLifespanR` holds because A01 supplies a local solution).

## The two restated defs

`IsMaximalSolution` (`Spec.lean:210-214`) and `presingularTimes` (`Spec.lean:168-169`)
— `⟪D01:IsMaximalSolution⟫` and the positive-time half of `[0,T^ν_{max,R})`, which
`Contracts/V1/Data.lean` does not define and the two new fields are stated over —
are restated **token-for-token** in the V2 contract module, in `Contracts.V1.Data`
vocabulary (`maximalLifespanR`, `ClassicalSolutionR`). `Section4/A02/Maximal.lean`
carries a byte-identical copy on the A02-local solution class.

Unlike V1's `limsupLeft`/`speedENorm`, these two **do not bridge by `rfl`**: both
rest on `maximalLifespanR`, which is a double `iSup` through `Nonempty` of the
solution class and is only *propositionally* equal across the two
`ClassicalSolutionR` copies (V1's `maximalPartial_maximalLifespanR_eq`).

## Transport (the binding)

`MaximalPartialV2API extends MaximalPartialAPI`, so `{ maximalPartial with … }`
reuses the frozen V1 witness and fills only the two new fields (the DatumLemmasV2
pattern). The two objects that resist `rfl`:

* `maximalPartial_isMaximalSolution_iff : A02.IsMaximalSolution ↔ V2.IsMaximalSolution`
  — **the one `Iff`, the only non-mechanical proof.** The analogue of V1's
  `maximalPartial_regularThrough_iff`: after `rw` unfolds both predicates and applies
  `maximalPartial_maximalLifespanR_eq` (V1's `iSup` congruence, reused), the positivity
  clause and the `S`-bound match, and the inner
  `∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p` transports by
  `and_congr` / `forall_congr'` / `imp_congr` down to a two-line existential swap using
  the reused conversions `maximalPartial_ofA02` / `uniqueness_toA02`, whose
  velocity/pressure projections reduce by `rfl` (so `w.velocity = u` survives the swap).
  Kept minimal.
* `maximalPartial_presingularTimes_eq : A02.presingularTimes = V2.presingularTimes`
  — **term-mode**, a plain `congrArg (fun L => {t | 0 ≤ t ∧ ofReal t < L})` on
  `maximalPartial_maximalLifespanR_eq`. No `by` block.

Field bodies are then term-mode applications of the `Maximal.lean` theorems:

* `exists_maximal := fun horizon localSolution ν a f hν ha hf => …` — transports the
  A01 `localSolution` hypothesis by `uniqueness_toA02` (exactly as V1's
  `horizon_le_lifespan`), applies `exists_maximal_of_localSolution`, and converts the
  `A02.IsMaximalSolution` conclusion to the contract's by `(iff …).mp`.
* `maximal_unique := fun … hM₁ hM₂ => maximalPartial_presingularTimes_eq ν a f ▸
  A02.maximal_unique … ((iff …).mpr hM₁) ((iff …).mpr hM₂)` — the `▸` rewrites the
  `presingularTimes` set in the conclusion (both occurrences, one under the reused
  `rfl`-defeq `PressureGaugeEquivOn`).

Exactly one `by` block in the binding (the `Iff`); everything else term-mode.

## Compatibility binding

`maximalPartial_of_v2 : MaximalPartialAPI := maximalPartialV2.toMaximalPartialAPI`
records that V1 is recovered from V2 by the inherited projection (definitional, so
it cannot drift). `Tests.MaximalPartial` keeps running against the untouched
`Bindings.maximalPartial`; `Tests.MaximalPartialV2` is the second, stronger test.

`MaximalPartialV2API` elaborates as a `Prop` (every field, including the inherited
V1 record, is propositional), so the binding and `checkedMaximalPartialV2` are
`theorem`s, matching V1.

## Approaches tried

* **`maximalPartial_presingularTimes_eq` as `congrArg` (term-mode) — kept.** Verified
  in a scratch file (`research/A02/scratch_v2.lean`, deleted after) before writing the
  real binding: `congrArg (fun L : ℝ≥0∞ => {t | 0 ≤ t ∧ ENNReal.ofReal t < L})
  (maximalPartial_maximalLifespanR_eq ν a f)` typechecks against the stated
  `A02.presingularTimes … = V2.presingularTimes …` because each side is defeq to the
  corresponding `presingularTimes` application. No fallback `by simp only [presingularTimes,
  maximalPartial_maximalLifespanR_eq]` was needed, though it would also work.
* **`maximal_unique` field body via `▸` (term-mode) — kept.** The concern was `▸`
  motive inference plus the `A02.PressureGaugeEquivOn` vs `Data.PressureGaugeEquivOn`
  defeq in the rewritten conclusion; the scratch file confirmed the term elaborates and
  the defeq is accepted (the `▸` motive is built from the expected type, whose
  `PressureGaugeEquivOn` is the contract's). No `by rw [← …]; exact …` fallback needed.
* **`isMaximalSolution_iff` — no shorter form found.** The inner existential genuinely
  crosses the two distinct `ClassicalSolutionR` inductive types, so an explicit
  `⟨fun ⟨w,hv,hp⟩ => ⟨ofA02 w, hv, hp⟩, …⟩` is unavoidable; `simp`/`exact?` cannot
  discharge a cross-structure existential. This is the single acknowledged proof, exactly
  as V1's `REVIEW_U4U6.md` finding 1 predicted for objects quantifying over the class.

## What did not fit (out of scope, each owed by a later lane)

Excluded from the V2 structure and named in the module docstring: the restated A01
interface fields `horizon`, `localSolution`, `horizonLowerBound`; the quantitative
restart (`restart`, `restart_datum`, `restart_force`); Theorem 4.2's packaged
identification `insertion_lifespan_eq`. Nothing asserts `eq:mild`, the continuation
criterion (A04), or any smallness / common-horizon / compact-support / `p ∈ L²`
side condition.

## Gates (all green)

* `lake build Contracts.V2.MaximalPartial Bindings.MaximalPartialV2 Tests.MaximalPartialV2`
  — `Build completed successfully`; `checkedMaximalPartialV2: checked; standard logical
  axioms only`.
* `make check` — `check_formalization_plan` OK; `check_contracts` 14 contracts, the
  `A02.maximal_partial_v2` closure includes `Tests.MaximalPartialV2`; `test_contract_policy`
  13/13 OK; `check_work_queue` 30 items consistent.
* `make test` — every registered contract checked, standard logical axioms only.
* `make test-mutations` — `implementation_refactor` accepted; `admitted_proof`,
  `extra_axiom`, `weakened_hypothesis` rejected as required.
* `check_contracts.py --base-ref origin/erenup/integration` — exit 0,
  `base_compatibility_checked: true` (no stable V1 contract/spec/test changed).
* Forbidden-token scan (`sorry|admit|axiom|native_decide|maxHeartbeats`) over the three
  new files — empty. Exactly one `by` block in the binding (the `Iff`).
