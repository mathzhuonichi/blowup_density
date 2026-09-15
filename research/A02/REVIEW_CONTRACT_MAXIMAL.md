# Review — lane 061, contract `A02.maximal_partial`

Reviewer: opus (lane-review). Worktree
`.claude/worktrees/061-A02-maximal-partial-contract`, HEAD `3f221f4`,
merge-base with `origin/erenup/integration` = `c411feb`.

## Verdict: **ACCEPT**

Ten field statements are the spec's, nine of them token-for-token and the tenth
(`horizon_le_lifespan`) in the documented Order.lean form; the carried
`uniqueness` field is the registered `Bindings.uniqueness` record, confirmed by
printing the elaborated term. The binding contains **no mathematics**: every
`by` block is one of the two acknowledged transport lemmas, a corollary of them,
or a one-line rewrite in an `Iff`-valued field. All gates green, axioms standard.

---

## 1. Gates

Environment: `bash scripts/lean-install.sh`, `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`; every `lake` invocation from `verification/`, one
at a time.

### 1.1 `lake build Contracts.V1.MaximalPartial Bindings.MaximalPartial Tests.MaximalPartial`

```
info: Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial: checked; standard logical axioms only
Build completed successfully (9951 jobs).
```

Explicit axiom print (scratch module, since deleted):

```
'BlowupDensity.Tests.checkedMaximalPartial' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no lane-local axiom.

### 1.2 `make check`

`exit=0`. `check_formalization_plan --check` OK; `check_contracts` closure lists
`Tests.MaximalPartial`; `test_contract_policy` `Ran 13 tests … OK`;
`check_work_queue` `30 work items: ownership, contract registration and task
cards consistent.`

### 1.3 `make test`

`exit=0`. Every registered contract replays with `checked; standard logical
axioms only`, including
`Tests/MaximalPartial.lean:16:0: Contract BlowupDensity.Tests.checkedMaximalPartial`.

### 1.4 `make test-mutations`

`exit=0`.

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed.
```

### 1.5 `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`

`exit=0`; `"registered_contracts": 13`, `"base_compatibility_checked": true`.
No stable contract, test or binding was altered.

### 1.6 Frozen files

```
$ git diff origin/erenup/integration --stat -- verification/Contracts/V1 verification/Tests verification/Bindings
 verification/Bindings/MaximalPartial.lean     | 213 ++++++
 verification/Contracts/V1/MaximalPartial.lean | 231 ++++++
 verification/Tests/MaximalPartial.lean        |  18 ++
 3 files changed, 462 insertions(+)
```

Only the three new files. The whole lane commit (`c411feb..HEAD`) touches exactly
`collaboration/{TASKS.md,tasks/A02.md,work_items.json}`,
`research/A02/ATTEMPTS_CONTRACT_MAXIMAL.md`, the three Lean files and
`verification/contracts.json` — no formalization file, no other lane's record.

### 1.7 Contract self-containment and forbidden tokens

Transitive local import closure of `Contracts.V1.MaximalPartial`, computed from
the import graph: `Contracts.V1.Data`, `Contracts.V1.Uniqueness` and itself —
**no non-`Contracts.*` module**.

`grep -n 'maxHeartbeats\|sorry\|^axiom\|set_option\|native_decide'` over the three
new files: empty.

---

## 2. Statement fidelity

Fields were compared mechanically (parse both structures, strip docstrings,
normalize whitespace, compare) against `research/A02/Spec.lean`'s
`MaximalSolutionAPI`:

| field | result |
|---|---|
| `restrict` (Spec:345) | identical |
| `patch` (Spec:357) | identical |
| `pressure_normalization` (Spec:399) | identical |
| `lifespan_le_iff` (Spec:443) | identical |
| `lifespan_le_iff_no_extension` (Spec:451) | identical |
| `lifespan_ge_of_forall_shorter` (Spec:463) | identical |
| `regularThrough_iff` (Spec:476) | identical |
| `referenceLifespan` (Spec:500) | identical |
| `lifespan_le_of_unbounded` (Spec:576) | identical |
| `horizon_le_lifespan` (Spec:372) | differs only by the documented hypothesis prefix — see below |

`limsupLeft` (`Contracts/V1/MaximalPartial.lean:101-102`) and `speedENorm`
(`:106-107`) are byte-identical to `research/A02/Spec.lean:135-136,148-149` and
to the `Section4/A02/Patch.lean:55-56,60-61` copies; the binding states both
`rfl` bridges (`:57-62`).

### `horizon_le_lifespan` — the one deliberate change, checked in all three places

Contract (`:155-161`):

```lean
horizon_le_lifespan : ∀ (horizon : ℝ → SpatialField → SpaceTimeField → ℝ),
  (∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ClassicalSolutionR ν a f (horizon ν a f)) →
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f
```

* The **conclusion** after the hypothesis is token-for-token the spec field
  (`Spec.lean:372-375`).
* The `horizon` binder type is token-for-token `MaximalSolutionAPI.horizon`
  (`Spec.lean:317`).
* The hypothesis is token-for-token `MaximalSolutionAPI.localSolution`
  (`Spec.lean:322-325`), which is itself ⟪A01:LocalTheoryAPI.solution⟫ and is
  token-for-token A01's own field `research/A01/Spec.lean:297-299`. So A01 can
  discharge it by `exact api.solution`.
* It matches `Section4/A02/Order.lean:56-64`
  `horizon_le_lifespan_of_localSolution` exactly (the only difference is that
  `horizon` is explicit here, implicit there — the binding supplies it by named
  argument).
* `research/A01/Spec.lean:370-372` independently assigns this inequality to A02
  ("A02 owns the inequality `ENNReal.ofReal (api.horizon ν a f) ≤
  maximalLifespanR ν a f`"), so the ownership split is consistent in both
  directions.

The change is disclosed in the field docstring (`:144-154`), the module docstring
(`:25-28`) and the `contracts.json` scope string. See finding N1.

---

## 3. Binding honesty

`verification/Bindings/MaximalPartial.lean`, complete inventory of `by` blocks
(six; everything else is term mode):

| line | declaration | tactic content | verdict |
|---|---|---|---|
| 124-125 | `maximalPartial_isEmpty_iff` | `rw [← not_nonempty_iff, ← not_nonempty_iff, maximalPartial_nonempty_iff]` | allowed — `Nonempty`/`IsEmpty` corollary, pure logic |
| 132-138 | `maximalPartial_maximalLifespanR_eq` | `simp only [both defs]; le_antisymm` + `iSup_le` / `le_iSup_of_le` moving the `Nonempty` witness by `ofA02`/`toA02` | allowed — this is *the* iSup congruence |
| 144-147 | `maximalPartial_regularThrough_iff` | `refine ⟨fun ⟨δ,hδ,h⟩ => ⟨δ,hδ,?_⟩, …⟩` + the two conversions | allowed — this is *the* one `Iff` |
| 182-185 | field `lifespan_le_iff` | `rw [← maximalPartial_maximalLifespanR_eq]; exact (A02 thm).trans (forall_congr' fun S => imp_congr … Iff.rfl)` | allowed — one-line rewrite |
| 186-189 | field `lifespan_le_iff_no_extension` | same shape with `imp_congr Iff.rfl (isEmpty_iff …)` | allowed — one-line rewrite |
| 195-197 | field `regularThrough_iff` | `rw [← regularThrough_iff, ← maximalLifespanR_eq]; exact (A02 thm)` | allowed — one-line rewrite |

`maximalPartial_nonempty_iff` (`:114-118`) is a term, not a tactic proof.
**Nothing in the file proves an inequality about solutions, an energy fact, or
any analytic statement.** The remaining fields are term-mode applications of the
`Section4/A02` theorems composed with `le_of_le_of_eq` / `le_of_eq_of_le` /
`lt_of_lt_of_eq` and `let ⟨…⟩ := …` destructure-rebuild — pure plumbing.

Two structural checks behind the two transport lemmas:

* `Section4/A02/SolutionClass.lean:142-143,146-147` restates `maximalLifespanR`
  and `RegularThrough` **token-identically** to `Contracts/V1/Data.lean:657-658,
  664-665`. The transport proofs are therefore genuine congruences across two
  copies of one definition, not a reconciliation of two different definitions.
* `Section4/A02/SolutionClass.lean:116-137` and `Contracts/V1/Data.lean`'s
  `ClassicalSolutionR` have the same ten fields in the same order with the same
  types.

`maximalPartial_ofA02` (`:73-85`) is exactly ten bare projections
(`velocity, pressure, horizon_pos, velocity_smooth, pressure_smooth, initial,
divergence, momentum, sobolev, pressure_gradient`) — one per structure field, no
tactic, no side condition. The four `rfl` round-trip `example`s exist at
`:88-105` (`ofA02` preserves velocity/pressure; `ofA02 ∘ toA02` preserves
velocity/pressure).

`uniqueness := uniqueness` (`:160`) resolves to the registered record. Because
`UniquenessAPI` is a `Prop`, a `rfl` check is vacuous (proof irrelevance), so this
was confirmed by printing the elaborated term instead:

```
$ #print BlowupDensity.Bindings.maximalPartial   (pp.fullNames)
theorem BlowupDensity.Bindings.maximalPartial : …MaximalPartialAPI :=
{ uniqueness := BlowupDensity.Bindings.uniqueness,
  restrict := …
```

`BlowupDensity.Bindings.uniqueness` is exactly the theorem
`verification/Bindings/Uniqueness.lean:93` that `Tests/Uniqueness.lean:14`
registers as `A02.uniqueness`. It is not a re-proof; it is the same declaration,
and it is the only declaration by that name in scope.

---

## 4. Round trip

A scratch module (`verification/Tests/ScratchReview061.lean`, built then
**deleted**; `git status` clean afterwards) applied the binding's fields to
contract-typed inputs with the conclusion spelled out in contract vocabulary
only. Both `example`s typechecked:

* `Bindings.maximalPartial.patch ν a f hν ha hf T₁ T₂ u₁ u₂` against a goal whose
  every symbol is `Contracts.V1.Data.{ClassicalSolutionR, PressureGaugeEquivOn}`
  and `Set.Ico`;
* `Bindings.maximalPartial.lifespan_le_of_unbounded …` against
  `maximalLifespanR ν a f ≤ ENNReal.ofReal T` with the blow-up hypothesis written
  with `Contracts.V1.MaximalPartial.{limsupLeft, speedENorm}`.

Printed types with `set_option pp.fullNames true`:

```
BlowupDensity.Bindings.maximalPartial.restrict : ∀ (ν : ℝ)
  (a : BlowupDensity.Contracts.V1.Data.SpatialField)
  (f : BlowupDensity.Contracts.V1.Data.SpaceTimeField) (T : ℝ)
  (u : BlowupDensity.Contracts.V1.Data.ClassicalSolutionR ν a f T) (S : ℝ), …

BlowupDensity.Bindings.maximalPartial.regularThrough_iff : … →
  (BlowupDensity.Contracts.V1.Data.RegularThrough ν a f T ↔
    ENNReal.ofReal T < BlowupDensity.Contracts.V1.Data.maximalLifespanR ν a f)
```

No `toA02`, no `ofA02`, no `NSFormalization.Section4.A02` name appears in any
public conclusion. The bridge is fully internal to the binding.

---

## 5. Scope string

`verification/contracts.json`, `A02.maximal_partial`. `MaximalSolutionAPI` has 20
fields; this record carries 11 (the 10 proved + `uniqueness`). The scope string
names all 9 exclusions explicitly:

* A01 interface `horizon`, `localSolution`, `horizonLowerBound` — named;
* `IsMaximalSolution` predicate, `exists_maximal`, `maximal_unique` — named;
* `restart`, `restart_datum`, `restart_force` — named;
* `insertion_lifespan_eq` — named.

It also states the `horizon_le_lifespan` weakening, the `MemForceR` ⊂ `prop:local`
force-class narrowing, that `limsupLeft`/`speedENorm` are restated because
`Data.lean` does not define them, that the binding's bridge is the two
conversions plus one `iSup` congruence and one `Iff`, and that the
`‖z‖_∞ ≤ C‖z‖_{H²}` step (`A03 → A02`) is a proof step and not a field. It
asserts nothing about `eq:mild`, the continuation criterion, or any smallness /
common-horizon / compact-support / `p ∈ L²` side condition. Honest.

---

## 6. Findings

**N1 — NOTE, `horizon_le_lifespan`, informational, no fix required now.** As
registered this field is *conditional*: it is an implication whose hypothesis is
A01's `solution` clause, so `A02.maximal_partial` alone does not assert
`ofReal (horizon ν a f) ≤ maximalLifespanR ν a f` for any particular `horizon`.
That is correct ownership — A01 owes the local solution — and it is disclosed in
the field docstring, the module docstring and the scope string, so nothing is
overclaimed. *Action for a later lane, not this one:* when A01's `LocalTheoryAPI`
is registered, add the one-line instantiation (a derived lemma next to the A01
binding, or a V2 field here) so that the unconditional spec field is actually
recorded somewhere; otherwise a reader counting "10 of 20 `MaximalSolutionAPI`
fields proved" is off by the difference between the conditional and unconditional
form of this one.

**N2 — NOTE, merge mechanics, for the merger.** The branch is behind
`origin/erenup/integration` (merge-base `c411feb`, tip `7be5fa7`), so
`git diff origin/erenup/integration` also shows integration's later 055/062
records as apparent deletions. The lane commit itself touches none of them
(verified with `git diff c411feb HEAD`). Rebase before squashing and use the
registry three-way merge for `contracts.json` / `work_items.json` / `TASKS.md`
as usual. `logs/AGENT_RUNS.csv` has no row for lane 061 on either branch — that
is the lead's record-at-merge step, not a lane-branch defect.

No REJECT-level and no ACCEPT-WITH-NOTES-level finding.

---

## 7. Commands run, verbatim

```
cd WT && bash scripts/lean-install.sh                                   # == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6

cd WT/verification && lake build Contracts.V1.MaximalPartial \
    Bindings.MaximalPartial Tests.MaximalPartial                        # Build completed successfully (9951 jobs)
                                                                        # checkedMaximalPartial: checked; standard logical axioms only
cd WT && make check                                                     # exit=0
cd WT && make test                                                      # exit=0
cd WT && make test-mutations                                            # exit=0, 4/4 mutations as required
cd WT && python3 experiments/check_contracts.py \
    --base-ref origin/erenup/integration                                # exit=0, base_compatibility_checked: true, 13 contracts

git diff origin/erenup/integration --stat -- \
    verification/Contracts/V1 verification/Tests verification/Bindings  # only the 3 new files
git diff c411feb HEAD --stat                                            # 8 files, none frozen

# scratch (created, built, deleted — git status clean)
cd WT/verification && lake build Tests.ScratchReview061                 # exit=0, both round-trip examples typecheck
cd WT/verification && lake build Tests.ScratchReview061b                # exit=0, #print shows uniqueness := Bindings.uniqueness
```
