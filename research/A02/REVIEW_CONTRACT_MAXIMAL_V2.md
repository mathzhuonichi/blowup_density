# Review — lane 069, contract `A02.maximal_partial_v2`

**Verdict: ACCEPT.**

Scope of this review: contract `A02.maximal_partial_v2` = V1 (`MaximalPartialAPI`,
unchanged, `extends`) + `exists_maximal` (conditional on A01's local-existence
clause) + `maximal_unique`. Files reviewed:

* `verification/Contracts/V2/MaximalPartial.lean` (new, 161 lines)
* `verification/Bindings/MaximalPartialV2.lean` (new, 127 lines)
* `verification/Tests/MaximalPartialV2.lean` (new, 26 lines)
* `verification/contracts.json` (one new entry)

The lane's own change set (`git diff --name-status $(git merge-base HEAD
origin/erenup/integration) HEAD`) is exactly eight files: the four above plus
`research/A02/ATTEMPTS_CONTRACT_MAXIMAL_V2.md`, `collaboration/TASKS.md`,
`collaboration/tasks/A02.md`, `collaboration/work_items.json`. No V1 file, no
`formalization/` file, no other lane's file is touched.

---

## 1. Gates

All run inside the worktree `/data_8T/ping/blowup_density/.claude/worktrees/069-A02-maximal-partial-v2`
after `bash scripts/lean-install.sh`, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
no `-j`, one `lake` at a time from `verification/`.

### 1.1 `lake build Contracts.V2.MaximalPartial Bindings.MaximalPartialV2 Tests.MaximalPartialV2`

```
$ cd WT/verification && lake build Contracts.V2.MaximalPartial Bindings.MaximalPartialV2 Tests.MaximalPartialV2
...
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
Build completed successfully (9954 jobs).
```

PASS. The only warnings in the run are pre-existing linter warnings from
`NSFormalization.Source.*` / `NSFormalization.Paper3.*` replay, none from the three
new modules. `Tests` is built with `warningAsError = true` (`verification/lakefile.toml`),
so the new test module is warning-clean.

### 1.2 `make check`

```
$ cd WT && make check
python3 experiments/check_formalization_plan.py --check     -> ok
python3 experiments/check_contracts.py                      -> ok (Tests.MaximalPartialV2 in the closure)
python3 experiments/test_contract_policy.py                 -> Ran 13 tests ... OK
python3 experiments/check_work_queue.py                     -> 30 work items: ownership, contract registration and task cards consistent.
exit 0
```

PASS.

### 1.3 `make test`

```
$ cd WT && make test        # lake -d verification test
info: Tests/Thresholds.lean:13:0:            checkedThresholds:            checked; standard logical axioms only
info: Tests/Scaling.lean:18:0:               checkedScaling:               checked; standard logical axioms only
info: Tests/Packet.lean:14:0:                checkedPacket:                checked; standard logical axioms only
info: Tests/DatumLemmasV2.lean:23:0:         checkedDatumLemmasV2:         checked; standard logical axioms only
info: Tests/InsertionFamily.lean:19:0:       checkedInsertionFamily:       checked; standard logical axioms only
info: Tests/DatumLemmas.lean:14:0:           checkedDatumLemmas:           checked; standard logical axioms only
info: Tests/BoundedRepresentative.lean:14:0: checkedBoundedRepresentative: checked; standard logical axioms only
info: Tests/CorrectionV2.lean:28:0:          checkedCorrectionV2:          checked; standard logical axioms only
info: Tests/GradientL6.lean:13:0:            checkedGradientL6:            checked; standard logical axioms only
info: Tests/Correction.lean:19:0:            checkedCorrection:            checked; standard logical axioms only
info: Tests/MaximalPartial.lean:16:0:        checkedMaximalPartial:        checked; standard logical axioms only
info: Tests/Uniqueness.lean:16:0:            checkedUniqueness:            checked; standard logical axioms only
info: Tests/TameProduct.lean:14:0:           checkedTameProduct:           checked; standard logical axioms only
info: Tests/MaximalPartialV2.lean:24:0:      checkedMaximalPartialV2:      checked; standard logical axioms only
```

PASS — all 14 registered contracts, including the untouched V1
`checkedMaximalPartial`, still check.

### 1.4 `make test-mutations`

```
$ cd WT && make test-mutations
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
exit 0
```

PASS.

### 1.5 `check_contracts.py --base-ref origin/erenup/integration`

```
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
exit 0
registered_contracts: 14
base_compatibility_checked: true
closures: ... "A02.maximal_partial": 1187 modules, "A02.maximal_partial_v2": 1190 modules
```

PASS. The V2 closure is V1's plus exactly three modules
(`Contracts.V2.MaximalPartial`, `Bindings.MaximalPartialV2`, `Tests.MaximalPartialV2`);
no new `formalization/` dependency is pulled in.

### 1.6 Axiom audit (direct, beyond `TestSupport.checkAxioms`)

```
$ lake env lean  # scratch, since deleted
'BlowupDensity.Tests.checkedMaximalPartialV2'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartialV2'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_of_v2'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_isMaximalSolution_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_presingularTimes_eq'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

PASS — standard logical axioms only, no `sorryAx`.

### 1.7 V1 byte-unchanged

```
$ git diff origin/erenup/integration -- verification/Contracts/V1 verification/Tests/MaximalPartial.lean verification/Bindings/MaximalPartial.lean
(empty)
```

PASS.

### 1.8 Contract imports / forbidden tokens

```
$ grep -n '^import' verification/Contracts/V2/MaximalPartial.lean
1:import Contracts.V1.MaximalPartial

$ grep -rn 'maxHeartbeats\|sorry\|axiom ' verification/Contracts/V2/MaximalPartial.lean verification/Bindings/MaximalPartialV2.lean verification/Tests/MaximalPartialV2.lean
(none)
```

PASS. The contract imports one `Contracts.*` module and nothing else; it declares
two `def`s and one `structure` and proves nothing. (`Contracts/V1/Data.lean` imports
`NSFormalization.*` for the ambient vocabulary — that is the frozen V1 baseline,
outside this lane.)

---

## 2. Statement fidelity

All four comparisons below were made with `diff` on the exact line ranges; each is
byte-identical except where noted.

| object | source | contract | result |
|---|---|---|---|
| `presingularTimes` | `research/A02/Spec.lean:168-169` | `Contracts/V2/MaximalPartial.lean:96-97` | **identical** |
| `IsMaximalSolution` | `research/A02/Spec.lean:210-214` | `Contracts/V2/MaximalPartial.lean:106-110` | **identical** |
| `maximal_unique` | `research/A02/Spec.lean:429-434` | `Contracts/V2/MaximalPartial.lean:154-159` | **identical** |
| `exists_maximal` hypothesis prefix | `Contracts/V1/MaximalPartial.lean:155-160` (`horizon_le_lifespan`) | `Contracts/V2/MaximalPartial.lean:139-144` | **identical** modulo the field name |
| `exists_maximal` conclusion | `research/A02/Spec.lean:423` | `Contracts/V2/MaximalPartial.lean:145` | identical modulo two spaces of indentation |

Notes.

* Both restated objects are in `Contracts.V1.Data` vocabulary (`maximalLifespanR`,
  `ClassicalSolutionR`, `PressureGaugeEquivOn`, `initialClassR`, `MemForceR`);
  `Contracts/V1/Data.lean` indeed defines neither of them, so restating is required.
* The A02-side copies in `formalization/NSFormalization/Section4/A02/Maximal.lean:78-79`
  and `:85-89` are byte-identical to the contract's, on the A02 solution class —
  confirmed by `diff`. So the two `def`s the binding transports differ only in which
  `ClassicalSolutionR` / `maximalLifespanR` they mention, exactly as documented.
* `maximal_unique` carries **no** A01 input, as the contract claims.
* `exists_maximal` carries the A01 clause `⟪A01:LocalTheoryAPI.solution⟫`
  (`research/A02/Spec.lean:317-321`, verified: docstring 317-318, field 319-321) as an
  explicit hypothesis. Its shape is *character-for-character* V1's
  `horizon_le_lifespan` prefix, so A01 will discharge the two fields by the same
  instantiation at `LocalTheoryAPI.solution`. Requirement met.
* The conditionality is disclosed in three places — the field docstring
  (`:131-138`), the module docstring (`:33-37`) and the `contracts.json` scope string —
  and the clause is genuinely load-bearing: `Maximal.lean:169-171` uses
  `localSolution` to get `0 < maximalLifespanR`, which is clause one of
  `IsMaximalSolution`, so the field is not provable without it.
* `Section4/A02/Maximal.lean` `exists_maximal_of_localSolution` (`:157-165`) and
  `maximal_unique` (`:192-201`) have exactly the statements the two fields need; no
  hypothesis is added or dropped in transit.
* Field coverage of `MaximalSolutionAPI` (20 fields) is now complete apart from the
  seven declared exclusions: V1 holds 10 + the carried `uniqueness`, V2 adds
  `exists_maximal` and `maximal_unique`, and the declared out-of-scope set is
  `{horizon, localSolution, horizonLowerBound, restart, restart_datum, restart_force,
  insertion_lifespan_eq}`. 10 + 1 + 2 + 7 = 20. The scope string is arithmetically
  honest.

---

## 3. Binding honesty

Every `by` block in `verification/Bindings/MaximalPartialV2.lean` (module docstring
occurrences of the English word "by" excluded):

| line | declaration | kind | verdict |
|---|---|---|---|
| 84 | `maximalPartial_isMaximalSolution_iff` | `:= by rw […]; refine and_congr Iff.rfl (forall_congr' …); exact ⟨…ofA02…, …toA02…⟩` | **the one allowed `Iff` transport** |

That is the complete list — **exactly one** tactic block in the file.

* `maximalPartial_presingularTimes_eq` (`:67-72`) is term-mode: a single
  `congrArg (fun L => {t | 0 ≤ t ∧ ENNReal.ofReal t < L}) (maximalPartial_maximalLifespanR_eq ν a f)`.
  No `by`. As claimed.
* The one `by` block contains no mathematics: it rewrites the two `def`s and the
  reused V1 congruence `maximalPartial_maximalLifespanR_eq`, then closes with
  `and_congr Iff.rfl (forall_congr' … imp_congr Iff.rfl (imp_congr Iff.rfl …))` and a
  pair of anonymous constructors applying `maximalPartial_ofA02` / `uniqueness_toA02`.
  Structurally the analogue of V1's `maximalPartial_regularThrough_iff`.
* The transport is faithful. `Contracts.V1.Data.ClassicalSolutionR` and
  `NSFormalization.Section4.A02.ClassicalSolutionR`
  (`formalization/NSFormalization/Section4/A02/SolutionClass.lean`) have the same ten
  fields with the same statements (`velocity`, `pressure`, `horizon_pos`,
  `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`, `momentum`,
  `sobolev`, `pressure_gradient`), and the two conversions (frozen V1 code,
  `Bindings/Uniqueness.lean:63-73`, `Bindings/MaximalPartial.lean:73-83`) are total
  field-by-field maps in both directions whose `velocity`/`pressure` projections
  reduce by `rfl`. So the inner `∃ w, w.velocity = u ∧ w.pressure = p` really is the
  same existential on both sides; nothing is weakened.
* Both new fields (`:104-114`) are **term-mode** applications of the lane-064
  theorems: `exists_maximal` applies
  `NSFormalization.Section4.A02.exists_maximal_of_localSolution`, mapping its
  `localSolution` argument by `uniqueness_toA02` (the same move V1's
  `horizon_le_lifespan` makes) and its conclusion by `.mp` of the `Iff`;
  `maximal_unique` applies `NSFormalization.Section4.A02.maximal_unique`, moving its
  two hypotheses by `.mpr` of the `Iff` and its conclusion by `▸` on the set equality.
  Both `Iff` directions are used the right way round.
* `maximalPartialV2` reuses the frozen V1 witness by `{ maximalPartial with … }`, so
  no V1 field is restated.
* `maximalPartial_of_v2` (`:124-125`) is exactly the inherited projection
  `maximalPartialV2.toMaximalPartialAPI` — no proof, and I confirmed
  `maximalPartial_of_v2 = maximalPartialV2.toMaximalPartialAPI` holds by `rfl`.

No REJECT-level content: nothing in the binding proves mathematics.

---

## 4. Round trip

Scratch file compiled with `lake env lean` from `WT/verification`, then deleted.
It stated the conclusions in pure contract vocabulary and required them to typecheck,
and separately printed the inferred types with `set_option pp.fullNames true`.

```lean
-- both `example`s typechecked
example : ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
    Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p :=
  Bindings.maximalPartialV2.exists_maximal horizon hloc ν a f hν ha hf

example :
    (∀ t ∈ Contracts.V2.MaximalPartial.presingularTimes ν a f,
        ∀ x : Space, u₁ (t, x) = u₂ (t, x)) ∧
      PressureGaugeEquivOn (Contracts.V2.MaximalPartial.presingularTimes ν a f) p₁ p₂ :=
  Bindings.maximalPartialV2.maximal_unique ν a f hν ha hf u₁ u₂ p₁ p₂ h₁ h₂
```

Inferred types, fully qualified:

```
BlowupDensity.Bindings.maximalPartialV2.exists_maximal horizon hloc ν a f hν ha hf
  : ∃ u p, BlowupDensity.Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p

BlowupDensity.Bindings.maximalPartialV2.maximal_unique ν a f hν ha hf u₁ u₂ p₁ p₂ h₁ h₂
  : (∀ t ∈ BlowupDensity.Contracts.V2.MaximalPartial.presingularTimes ν a f,
      ∀ (x : NavierStokes.ProblemStatement.Space), u₁ (t, x) = u₂ (t, x)) ∧
    BlowupDensity.Contracts.V1.Data.PressureGaugeEquivOn
      (BlowupDensity.Contracts.V2.MaximalPartial.presingularTimes ν a f) p₁ p₂
```

PASS. The inputs accepted are contract-typed (`Contracts.V1.Data.ClassicalSolutionR`,
`Contracts.V2.MaximalPartial.IsMaximalSolution`) and the public conclusions mention
only `BlowupDensity.Contracts.*` and `NavierStokes.ProblemStatement.*` structures.
No `NSFormalization.Section4.A02` name, and no `toA02` / `ofA02`, leaks into a public
type. Scratch deleted.

---

## 5. Scope string

`verification/contracts.json`, entry `A02.maximal_partial_v2`. Checked clause by clause:

* "extending A02.maximal_partial version 1 unchanged (extends MaximalPartialAPI)" — true (§1.7, §3).
* "restated token-for-token … (maximalLifespanR, ClassicalSolutionR)" — true (§2).
* "`exists_maximal` … stated with the A01 LocalTheoryAPI.solution clause as an explicit
  hypothesis, exactly as version 1's horizon_le_lifespan … so A01 will discharge that
  hypothesis; the clause is genuinely used" — true, and the "exactly as version 1"
  claim is literal, not approximate (§2).
* "`maximal_unique` … stated verbatim, needing no A01 hypothesis" — true.
* "transports IsMaximalSolution … by one Iff … and the only non-mechanical proof" — true;
  it is the file's only tactic block (§3).
* "maximalPartial_of_v2 recovers version 1 by the inherited projection
  toMaximalPartialAPI, and Tests.MaximalPartial keeps running against the untouched
  Bindings.maximalPartial" — both verified (§1.3, §3).
* Remaining exclusions listed: A01 interface fields (`horizon`, `localSolution`,
  `horizonLowerBound`); `restart`, `restart_datum`, `restart_force`;
  `insertion_lifespan_eq`. This is exactly the residue of `MaximalSolutionAPI` (§2);
  no field is silently omitted.
* The negative disclaimer ("Nothing here asserts eq:mild, the continuation criterion
  eq:criterion (A04), or any smallness, common-horizon, compact-support or p in L^2
  side condition") is true of both new fields.

PASS — honest.

---

## 6. Findings

No blocking finding. Two informational notes.

**N1 — informational, process, no code change.** The lane branch is 18 commits behind
`origin/erenup/integration` (merge-base `c1e19fe`); `git diff origin/erenup/integration`
therefore also shows unrelated deletions (`Section4/B01/Temporal.lean`,
`Section4/D01/OrderZeroDatum.lean`, `research/B01/*`, `research/D01/*`, rows of
`logs/AGENT_RUNS.csv` and `logs/LESSONS.md`) that the lane did not make — they are files
added on integration after the lane branched. The lane's own change set (vs merge-base)
is the eight files listed at the top. All gates above were run on the lane tree; they
should be re-run after the rebase, and `verification/contracts.json` will need the
registry three-way merge. *Fix:* nothing in the lane; standard rebase at merge time.

**N2 — cosmetic, `Contracts/V2/MaximalPartial.lean:83-86`, no change requested.** The
`open Set MeasureTheory` / `open scoped ENNReal` header is copied verbatim from
`Contracts/V1/MaximalPartial.lean:83-86`, but the V2 body uses neither `MeasureTheory`
nor the `ℝ≥0∞` notation (it writes `Set ℝ` and `ENNReal.ofReal` in full). Harmless,
consistent with house style across `Contracts/V1` and `Contracts/V2`, and no linter
flags it. *Fix:* none needed; only drop the unused opens if the house style ever changes.

---

## 7. Commands, in order

```
cd WT && bash scripts/lean-install.sh                                                    # == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification && lake build Contracts.V2.MaximalPartial Bindings.MaximalPartialV2 Tests.MaximalPartialV2
                                                                                         # Build completed successfully (9954 jobs)
cd WT && make check                                                                      # exit 0
cd WT && make test                                                                       # 14/14 contracts checked
cd WT && make test-mutations                                                             # Mutation suite passed
cd WT && python3 experiments/check_contracts.py --base-ref origin/erenup/integration     # exit 0, base_compatibility_checked: true
cd WT && git diff origin/erenup/integration -- verification/Contracts/V1 \
         verification/Tests/MaximalPartial.lean verification/Bindings/MaximalPartial.lean # empty
cd WT/verification && lake env lean /tmp/rev069_scratch.lean                             # round trip, exit 0, then deleted
cd WT/verification && lake env lean /tmp/rev069_ax.lean                                  # axioms, exit 0, then deleted
```

Reviewer: lane-069 reviewer (opus). Read/build only; no repository file other than this
one was written, and no git write command was run.
