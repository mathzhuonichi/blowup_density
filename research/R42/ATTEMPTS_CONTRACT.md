# R42 lane 096 — registering the two lifespan clauses as `R42.insertion_lifespan`

Deliverable: a new versioned contract (specification + binding + test + ledger)
for the two lifespan clauses of Theorem 4.2, following the lane-092 reviewer's
"Proposed V2 contract shape" (`research/R42/REVIEW_BINDING.md:242-306`) and the
precedent of lane 091 (`C01.energy_absorption_partial`) / lane 071
(`B01.bochner_partial`).  Kind: contract.  Everything compiled and every gate
passed; the command table is at the end.

## What was transcribed (and from where)

* **`verification/Contracts/V1/InsertionLifespan.lean`** — namespace
  `BlowupDensity.Contracts.V1.InsertionLifespan` (a **sub-namespace**, so the new
  `InsertionLifespanAPI` does not clash with the frozen 3-field
  `Contracts.V1.InsertionLifespanAPI`; modelled on how
  `MaximalPartial.MaximalPartialAPI` and `EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI`
  each live in their own sub-namespace).  5 fields, exactly the reviewer's shape:
  - `family : InsertionFamilyAPI ν P`
  - `memForce : Data.MemForceR family.g`
  - `regular : Data.RegularThrough ν family.a family.g (family.T + family.margin)`
  - `referenceLifespan` and `lifespan` — **token-identical** to the frozen
    `Contracts.V1.InsertionLifespanAPI`'s two fields
    (`InsertionFamily.lean:427-434`), copied verbatim.
  Plus `def insertionLifespanStatement : Prop` in the shape of
  `insertionFamilyStatement` (`InsertionFamily.lean:381-385`): two hypotheses,
  `∃ A, A.family = F`.
  **Imports: only `Contracts.V1.InsertionFamily`** (brings `InsertionFamilyAPI`,
  `PacketAPI`, `Data`).  `Data.RegularThrough` (`Data.lean:664`) and
  `Data.maximalLifespanR` (`:657`) are both in `Contracts/V1/Data.lean`, so no
  extra import (and importing `MaximalPartial` would violate the contract-import
  policy anyway).  `check_contracts.py` accepts the single import.

* **`verification/Bindings/InsertionLifespan.lean`** (lane 092, not frozen) — added
  `import Contracts.V1.InsertionLifespan`, and, inside the existing sub-namespace
  `BlowupDensity.Bindings.InsertionLifespan`, `def insertionLifespanAPI` building
  the new 5-field record and `theorem insertionLifespanAPI_family := rfl`.  The two
  clause fields **reuse 092's proofs verbatim**: `referenceLifespan F hreg` and
  `fun _ε hε => lifespan_eq F hg hε` (the same two used to build the old 3-field
  `insertionLifespan`).  `memForce := hg`, `regular := hreg` just store the two
  hypotheses.  The old `insertionLifespan` def is left in place untouched.

* **`verification/Tests/InsertionLifespan.lean`** — in the shape of
  `Tests/InsertionFamily.lean`: `theorem checkedInsertionLifespan :
  insertionLifespanStatement := fun _ν _P F hg hreg => ⟨…insertionLifespanAPI F hg
  hreg, rfl⟩`; `run_cmd TestSupport.checkAxioms ``checkedInsertionLifespan`; one
  `example` per clause writing the manuscript's two displays by hand from a record
  `A`; and the two derived-hypothesis guards `example : 0 < ν := P.viscosity_pos`
  and `example (A) : A.family.a ∈ Data.initialClassR :=
  Bindings.InsertionLifespan.initialClassR_a A.family` (lane-092 findings 1, 2).

* **`verification/contracts.json`** — appended `R42.insertion_lifespan` (parent
  `R42`, version 1) with a `scope` in the sibling style (asserted / derived /
  carried / binding-consumes / not-asserted).

* **`collaboration/work_items.json`** — added `"R42.insertion_lifespan"` to the
  R42 item's `contracts` list (exactly as lane 091 did for C01), then
  `python3 experiments/tasks.py render` regenerated `TASKS.md` and `tasks/R42.md`.

## Mismatches / deviations recorded

* **Two carried hypotheses, not four.**  The reviewer's finding is honored: `ν > 0`
  (`P.viscosity_pos`) and `a ∈ X_R` (`initialClassR_a`) are **derived**, not fields.
  Only `memForce` and `regular` are carried — and only because the manuscript states
  them (`04-whole-space.tex:32`) and a consumer (R47 needs `g ∈ F_R`) reuses them.
* **Blow-up form.**  Like `R42.insertion_family`, the displayed limsup of the spatial
  sup norm is **not** asserted; the blow-up is consumed inside the proof in the
  registered pointwise `SpeedUnboundedAt` form and re-expressed in `speedENorm`.
  Recorded in the scope.
* **`sobolev`/`pressure_gradient` for `u_eps`** are built inside `sol_on_shorter`
  (lane 087) but not exported by this contract; recorded in the scope's NOT-asserted
  list.
* The new structure's `referenceLifespan`/`lifespan` field types match the frozen
  structure's byte-for-byte (checked by eye against `InsertionFamily.lean:427-434`);
  the binding fills them with the exact 092 proofs, so no drift is possible.

## Failed / corrected approaches (negative examples)

* **`contracts.json` round-trip escaped non-ASCII in other entries.**  First attempt
  used `json.dump(data, f, indent=2)` (default `ensure_ascii=True`), which rewrote 6
  pre-existing scope strings' UTF-8 (`ν`→`ν`, `R³`→`R³`, …) into escapes —
  a semantically-identical but noisy 18-line diff touching entries I must not churn.
  `check_contracts.py` would still have passed (it compares only
  `version/specification/test_module/declaration/enabled`, not `scope`), but the
  churn is wrong.  **Fix:** `git checkout verification/contracts.json` and redo with
  `ensure_ascii=False`; the diff is then only the 11-line appended entry.  Lesson: any
  JSON round-trip of `contracts.json` MUST pass `ensure_ascii=False` (the file stores
  raw UTF-8) and `indent=2` (matches the existing formatting exactly).
* No Lean compile failures: the contract, the binding def and the Tests module each
  built on the first try.  The one thing to watch (already handled) is that the
  `lifespan := fun _ε hε => …` binder underscore-prefixes `ε` to avoid the
  `Variable name ε is not explicitly referenced` linter the 092 reviewer reproduced;
  the same underscore is used here.  The Tests `example`s use explicit binders (not a
  `variable` block) so that every bound name is referenced — `Tests` is
  `warningAsError = true`, and no existing Tests module uses `example`/`variable`, so
  a stray unused binder would have been a hard error.

## Commands and results (worktree `096-R42-lifespan-contract`;
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`; lake from `verification/`)

| command | result |
|---|---|
| `lake build Contracts.V1.InsertionLifespan` | `Build completed successfully (8822 jobs).` (only pre-existing Paper3 warnings) |
| `lake build Bindings.InsertionLifespan` | `Build completed successfully (9969 jobs).` |
| `lake build Tests.InsertionLifespan` | `Build completed successfully (9971 jobs).`; `Tests/InsertionLifespan.lean:24:0: Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only` |
| `make check` | exit 0; architecture OK; `test_contract_policy.py` 13/13; `check_work_queue.py` "30 work items … consistent" |
| `make test` | exit 0; all 17 registered contracts "checked; standard logical axioms only", including `checkedInsertionLifespan`; no `error:` |
| `make test-mutations` | `implementation_refactor: accepted`; `admitted_proof`/`extra_axiom`/`weakened_hypothesis` "rejected as required"; "Mutation suite passed." |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | `registered_contracts: 17`, `base_compatibility_checked: true`, closure for `R42.insertion_lifespan` present |
| `bash scripts/gates.sh Tests.InsertionLifespan` | ends `== gates OK` (make check + build + test + test-mutations + check_contracts all pass) |

No `sorry`, `admit`, `axiom`, `native_decide`, no placeholder `Prop` field; the
frozen `Contracts/V1/InsertionFamily.lean` (including its 3-field
`InsertionLifespanAPI`) is untouched.

## Lane-096 review (ACCEPT-WITH-NOTES, `research/R42/REVIEW_CONTRACT.md`) — corrections applied

Statements accepted byte-for-byte (the two clause field types are mechanically
identical to the frozen structure's, the axioms are the standard three, all gates
green). Three prose findings, all fixed; no Lean statement changed.

* **Finding 1 (wrong `STATEMENTS.md` line citations, mutually inconsistent across
  three places).** The correct lines are `referenceLifespan →
  research/section4/STATEMENTS.md:333` and `lifespan → :347`. I had used the
  frozen file's inherited-and-already-wrong `:245` and a `:332` (which is the
  half-open `reference` field, the most misleading one for `referenceLifespan`).
  Corrected consistently in `Contracts/V1/InsertionLifespan.lean` (module header
  bullets + the two field docstrings) and in the `contracts.json` scope. The
  `04-whole-space.tex:32,34` citations were correct and stayed. The frozen file's
  own `:245` cannot be touched and remains a known wart.
* **Finding 2 (stale Bindings docstring).** `Bindings/InsertionLifespan.lean`
  still called the target "still-unregistered … a later lane" and "the V2
  contract". Rewritten: the opening now names `R42.insertion_lifespan` (version 1
  of a new id, `Contracts.V1.InsertionLifespan.InsertionLifespanAPI`) as the
  registered contract inhabited by §8 `insertionLifespanAPI`, and §7
  `insertionLifespan` as the legacy frozen 3-field inhabitant (lane 092) whose two
  clause proofs §8 reuses verbatim; the route list gained step 8 and the "V2"
  wording is gone (heading, §7 docstring).
* **Finding 3 (name collision; frozen docstring stale).** Added a header section
  to `Contracts/V1/InsertionLifespan.lean` and one sentence to the
  `contracts.json` scope: this record supersedes the frozen 3-field
  `Contracts.V1.InsertionLifespanAPI` (whose docstring wrongly claims the clauses
  unproved and A02 unregistered — both now false); and because a bare
  `InsertionLifespanAPI` under `open Contracts.V1` resolves to the frozen one, new
  consumers must write the qualified `InsertionLifespan.InsertionLifespanAPI`.
  Per the reviewer's judgement, §7's legacy def is **kept** (only inhabitant of
  the frozen structure, proofs reused by §8, no duplicated burden).
* **Finding 4 (observation, no action):** the contract is conditional on a given
  `InsertionFamilyAPI`, as intended.

Re-ran after the edits (docstring/scope only; no statement change):

| command | result |
|---|---|
| `lake build Tests.InsertionLifespan` | `Build completed successfully (9971 jobs).`; `Contract BlowupDensity.Tests.checkedInsertionLifespan: checked; standard logical axioms only` |
| `make check` | exit 0; policy 13/13; work queue "30 work items … consistent" |
| `make test` | exit 0; all 17 contracts "checked; standard logical axioms only" |
| `check_contracts.py --base-ref origin/erenup/integration` | `registered_contracts: 17`, `base_compatibility_checked: true` |
