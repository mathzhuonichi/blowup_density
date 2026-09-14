# ATTEMPTS — lane 120 (D01 / P2 contract V3 = `D01.datum_lemmas_v3`)

Register obligation P2 (`eq:Rpressure`, `02-preliminaries.tex:89-94`), proved by
lane 117 (`Section4/D01/PressureJets.lean`), as **version 3** of
`D01.datum_lemmas`.  No new mathematics: this lane only wires the three exported
theorems into a versioned contract, following `research/D01/REVIEW_SL8_ASSEMBLY.md`
§6 and appendix C verbatim.

## Decisions

1. **V3, not a new `Contracts/V1/PressureJets.lean`** (review §6): P2 is a D01
   obligation whose sibling `solution_slice_pressureGradient_contDiff` already
   lives in `DatumLemmas`, and the V1/V2 scope sentence "no Sobolev datum or jet
   class for the pressure or its gradient is asserted" is exactly what P2 removes
   — it must be superseded *in the new version's scope*, since V1/V2 are frozen.
   `experiments/check_contracts.py:118` (`assert f'/V{version}/' in specification`)
   forces version 3 into the new dir `verification/Contracts/V3/`.

2. **Three fields, verbatim from review §6 / appendix C.**
   `solution_slice_pressureGradient_smoothJets` (P2 regularity),
   `solution_slice_temporalDerivative_smoothJets` (the `∂ₜu ∈ H^∞` corollary),
   `solution_slice_pressureGradient_exists_datum` (the existence form of the
   order-`m` datum, the `hP` slot A04 consumes).  All on interior slices
   `t ∈ Ioo 0 T`.

3. **Contract imports = `Contracts.V2.DatumLemmas` + `Contracts.V1.Packet`.**
   `extends DatumLemmasV2API` needs V2; `pressureGradient` / `temporalDerivative`
   are `Contracts.V1.Packet`'s (`Packet.lean:115,99`).  Everything else
   (`ClassicalSolutionR`, `MemForceR`, `SpatialField`, `SpaceTimeField`, `Space`,
   `IsSobolevDatum`, `SmoothSquareIntegrableJets`, `RealVectorSobolev`) is reached
   transitively through V2 → V1.DatumLemmas → V1.Data / GradientL6 and Paper3.
   Nothing new is restated in the contract; the import policy
   (`check_contracts.py`, only `Contracts.*` + canonical) is satisfied — Packet is
   `Contracts.*`.

4. **Opens = `Set`, `Contracts.V1`, `Contracts.V1.Data`, `Paper3 (RealVectorSobolev)`.**
   This is appendix C's compiled open set — **not** review §6's prose open set,
   which lists `open NavierStokes.ProblemStatement` instead of `open Contracts.V1`.
   §6's prose set does **not** compile in a V3 namespace: see negative example A.
   Opening `Contracts.V1` (Packet's operators) and *not* `NavierStokes.ProblemStatement`
   is the only conflict-free choice; the two `pressureGradient`/`temporalDerivative`
   are `rfl`-equal (bridges in the binding), so the recorded field types are the
   same either way.

5. **Binding through `uniqueness_toA02`** (`Bindings.Uniqueness`, review §6
   appendix C): `Contracts.V1.Data.ClassicalSolutionR` and
   `Section4.A02.ClassicalSolutionR` are different inductive types, so the `rfl`
   structure bridge is impossible (negative example B) — the field-by-field
   converter `uniqueness_toA02` is used, and `(uniqueness_toA02 u).pressure =
   u.pressure` / `.velocity = u.velocity` are `rfl` (`Uniqueness.lean:79,83`), which
   makes each `PressureJets` theorem's conclusion definitionally the contract
   field's.  Field 3 binds to lane 117's exported
   `exists_isSobolevDatum_pressureGradient_slice` (`PressureJets.lean:141`), which
   is precisely appendix B's recommended `∃`-form (finding 3 was implemented in
   the merged module).

6. **`work_items.json` NOT edited, `tasks.py render` NOT run.**  D01's work item is
   `kind: specification` with `contracts: []`; V1 and V2 are registered in
   `contracts.json` but were never listed in D01's work-item `contracts` array, and
   `check_work_queue.py` only asserts `set(item['contracts']) ⊆ registered` (empty
   is fine) and, for `proof`/`assembly` items, non-empty — D01 is neither.  Adding
   V3 keeps `[]` consistent; `make check` (which runs `check_work_queue.py`) passes
   unchanged (30 items consistent).  The task card / `TASKS.md` would show "none
   yet" for D01 exactly as now, so render is a no-op.

7. **Order-`m` identity `P = (I−P)ₘ Am` NOT registered as a field.**  It is proved
   and exported upstream (`PressureJets.isSobolevDatum_pressureGradient_lerayComplement`,
   `:93`).  **Correction (lane-120 review finding 1):** the momentum residual is
   *not* the obstacle — `f (t,·)`, `advection`, `spatialLaplacian` are all
   `Contracts.V1.Packet` (`:107`, `:120`), so `h = f − (u·∇)u + νΔu` writes out in
   contract terms directly.  The obstacle is the **operator** `(I−P)ₘ`
   (`D01.Leray.lerayComplement`), which has no `Contracts/V1` counterpart, so the
   identity in operator form cannot be stated in a contract.  Its operator-free
   form — the Helmholtz split `datumᵐ h = datumᵐ ∂ₜu + datumᵐ ∇p` — **is** statable
   and provable in pure contract vocabulary (reviewer's appendix E, copied to
   `research/D01/probes/v4_split_identity.lean`, standard axioms; compiled in this
   lane); with V1's registered datum uniqueness it pins `datumᵐ ∇p` from `Am` and
   `datumᵐ ∂ₜu`.  That is the **V4 candidate**, deliberately not registered in V3.
   Only the consumer-facing consequence — existence of *some* order-`m` datum,
   field 3 — is registered, which is what A04 consumes.  Reason corrected in the
   scope string and the contract docstring.

## Bridges added (binding, §1)

* `datumLemmasV3_pressureGradient_eq : @NavierStokes.ProblemStatement.pressureGradient = @Contracts.V1.pressureGradient := rfl`
* `datumLemmasV3_temporalDerivative_eq : @NavierStokes.ProblemStatement.temporalDerivative = @Contracts.V1.temporalDerivative := rfl`
* regression guard `datumLemmasV3_toDatumLemmasV2API_eq : datumLemmasV3.toDatumLemmasV2API = datumLemmasV2 := rfl`

`SmoothSquareIntegrableJets`, `MemForceR` and — relied on by field 3 —
`IsSobolevDatum` need no new bridge; they are pinned in `Bindings.DatumLemmas`
(`datumLemmas_smoothSquareIntegrableJets_eq`, `datumLemmas_memForceR_eq`, and
`datumLemmas_isSobolevDatum_eq` at `Bindings/DatumLemmas.lean:46`), imported
through `Bindings.DatumLemmasV2`.

## Negative examples (real error text)

### A — review §6's prose open set does not compile in a V3 namespace

Opening `Contracts.V1` **and** `NavierStokes.ProblemStatement` together (as §6's
prose "`open … NavierStokes.ProblemStatement`" would, alongside the `Contracts.V1`
needed for `SmoothSquareIntegrableJets`) makes `Space` (and `pressureGradient`,
`temporalDerivative`) ambiguous.  `cd verification && lake env lean` on the field
type with both opens:

```
error: Ambiguous term
  Space
Possible interpretations:
  NavierStokes.ProblemStatement.Space : Type
  BlowupDensity.Contracts.V1.Space : Type
```

Fix: open `Contracts.V1` only (appendix C's actual open set), not
`NavierStokes.ProblemStatement`.  Same `logs/LESSONS.md` (2026-09-14) "open two
namespaces → ambiguous bare name" trap.

### B — the structure `rfl` bridge to the A02 solution is impossible

```
error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  BlowupDensity.Contracts.V1.Data.ClassicalSolutionR = NSFormalization.Section4.A02.ClassicalSolutionR
```

`ClassicalSolutionR` is a `structure` defined once in `Contracts/V1/Data.lean`;
the A02 in-tree restatement is a *different* inductive type (`CLAUDE.md` structure
exception).  Hence the binding must route through `Bindings.uniqueness_toA02`, not
a `rfl` bridge.

## Commands run (worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `cd verification && lake build Tests.DatumLemmasV3` | `Build completed successfully (10015 jobs).`; `Contract …checkedDatumLemmasV3: checked; standard logical axioms only` |
| `cd verification && lake env lean ../research/D01/axioms_contract_v3.lean` | exit 0, no errors; 4 × `#print axioms` = `[propext, Classical.choice, Quot.sound]`; all `rfl` bridges + 3 field examples elaborate |
| `make check` | exit 0 (`test_contract_policy` 13 OK; `check_work_queue` 30 items consistent) |
| `make test` | exit 0; all 22 contracts "checked; standard logical axioms only" |
| `make test-mutations` | exit 0; `implementation_refactor: accepted`, `admitted_proof`/`extra_axiom`/`weakened_hypothesis: rejected as required` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | `registered_contracts: 22`, `base_compatibility_checked: true` |

## Review follow-ups (lane-120 review, `REVIEW_CONTRACT_V3.md`, ACCEPT-WITH-NOTES)

* **Finding 0 (citation, medium) — fixed.**  eq:Rpressure is
  `paper/sections/02-preliminaries.tex:89-94` (`:89` "On R³ we require", `:90-92`
  the equation, `:93-94` "For smooth H^∞ data, G is smooth …"); `:76-81` is the
  Leray-projection paragraph + `eq:projected`.  The wrong `:76-81` was inherited
  from `REVIEW_SL8_ASSEMBLY.md` §2(b) and copied forward.  Replaced everywhere in
  this lane's files, `contracts.json`, and `REVIEW_SL8_ASSEMBLY.md` (3×).
  `P2_SPLIT.md` / `SL8_SPLIT.md` / `ATTEMPTS_SL8_ASSEMBLY.md` had no occurrence
  (grep).  **`Section4/D01/PressureJets.lean`** (merged module, NOT edited) still
  cites `:76-81` in its docstring — flag for the next D01 SIMP / docstring pass.
* **Finding 1 (reason, medium) — fixed.**  See decision 7 above: reason corrected
  (operator `(I−P)ₘ`, not the residual), V4 candidate named, probe
  `research/D01/probes/v4_split_identity.lean` added and compiled (standard axioms).
* **Finding 2 (HeliCorgi closure, info) — recorded.**  V3 is the first registered
  contract whose `make test` audited closure reaches vendored HeliCorgi: **28**
  `Formal.*` modules (`R3Leray*`, `R3Stokes*`, `FlowMap*`, `PDEBridgeAdapter`, …),
  entering through `Section4/D01/LeraySymbol.lean` and `LerayMultiplier.lean`; **no
  `FormalPatched.*`**.  No rule broken — `Tests/DatumLemmasV3.lean` imports only
  `Contracts.V3.DatumLemmas`, `Bindings.DatumLemmasV3`, `TestSupport.Axioms`, so
  `warningAsError` is not tripped and `checkAxioms` is standard-only.  But the
  audited surface now spans HeliCorgi, so a vendor/toolchain bump can break a
  *registered contract* rather than only a research module — **lead: worth a line
  in `PLAN.md` / `NEXT_SESSION.md`.**
* **Finding 3 (wording, low) — fixed.**  Field 1's "strengthens the V1 field" is a
  stronger conclusion on a *narrower* domain (V1 `Ico 0 T`, V3 `Ioo 0 T`); contract
  docstring reworded.
* **Finding 4 (wording, low) — fixed.**  The supersede sentence (contract docstring
  + registry scope) narrowed to the **gradient** only; the scalar `p` half stays
  out of scope.
* **Finding 5 (info) — made explicit.**  Only V1's *registry-scope* sentence is
  superseded, not V1's *docstring* claim that the jet class does not follow "from
  the class as specified" — that stays true (`MemForceR` is not a
  `ClassicalSolutionR` field; `Pressure.lean:62-66` is the no-force
  counterexample).  Stated in the contract docstring "Why a new version".
* **Finding 6 / 7 (info) — no action.**  The V3 witness-level regression guard is
  intentionally stronger than V2's (reviewer approved); `work_items.json` skip is
  correct and matches V1/V2 precedent.
* **LESSONS-worthy (flag for lead).**  `ring` / `module` (and
  `linear_combination (norm := module)`) treat `Contracts.V1.temporalDerivative`
  and `NavierStokes.ProblemStatement.temporalDerivative` as *different atoms*
  although they are `rfl`-equal (`ring failed … ⊢ 1 = 0`); the fix is an explicit
  `show` into one vocabulary before the algebra tactic.  Recorded in the V4 probe
  header.

## Post-review commands (re-run after the fixes)

| command | result |
|---|---|
| `cd verification && lake env lean ../research/D01/probes/v4_split_identity.lean` | exit 0; `'Rev120V4.splitIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `cd verification && lake build Tests.DatumLemmasV3` | `Build completed successfully`; `checkedDatumLemmasV3: checked; standard logical axioms only` |
| `make check` | exit 0 |
| `make test` | exit 0; 22 contracts standard-only |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | `registered_contracts: 22`, `base_compatibility_checked: true` |
