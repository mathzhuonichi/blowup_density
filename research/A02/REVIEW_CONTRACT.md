# A02 — review of lane 057, contract `A02.uniqueness`

Reviewer pass over `verification/Contracts/V1/Uniqueness.lean`,
`verification/Bindings/Uniqueness.lean`, `verification/Tests/Uniqueness.lean` and
the `A02.uniqueness` entry of `verification/contracts.json` (commit `73c1b98`).
Light and strict: gates re-run from scratch in the worktree, statement compared
byte-for-byte against the accepted draft, binding read for hidden proof content,
scope string compared against the full `MaximalSolutionAPI` field list, and a
round-trip application type-checked in a scratch file (since deleted).

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct and the contract is honest. All four gates pass,
`checkedUniqueness` is on standard logical axioms only, the two fields are
**byte-identical** (md5-equal) to `research/A02/Spec.lean:263-281` including their
docstrings, the contract imports only `Contracts.V1.Data`, the binding contains
no proof content whatsoever, and the scope string is the exact complement of the
one registered field. Both notes below are record/ledger hygiene outside the
three Lean files; **nothing in the specification, binding or test needs to
change.**

---

## Findings

### 1. `A02.uniqueness` was not added to the ledger, so A02's task card still says "none yet" — severity **minor**, file `collaboration/work_items.json`

`verification/contracts.json` registers `A02.uniqueness`, but the A02 item of
`collaboration/work_items.json` still has `"contracts": []`:

```
A02 | state: in-progress | kind: specification | owner: erenup | contracts: []
```

`experiments/tasks.py:34` renders the card line from that list, so
`collaboration/tasks/A02.md:26` still reads `Registered component contracts: none
yet.` Every other registering lane updated it — `R42.md:25`, `I01.md:24`,
`I02.md:26`, `A05.md:25`, `A03.md:26`, `I03.md:27`, `R41.md:23` all name their
contracts. (`D01.md:29` has the same gap; that is a pre-existing precedent, not a
justification.)

`make check` does not catch this: `experiments/check_work_queue.py:21` asserts
only `set(item['contracts']) <= registered`, a subset, so an empty list always
passes. It will bite later — line 22-23 of the same file requires
`item['contracts']` to be non-empty once A02's item turns into `proof` or
`assembly` kind.

**Fix** (one line plus a render, no Lean):

```
add "A02.uniqueness" to the A02 item's "contracts" in collaboration/work_items.json
python3 experiments/tasks.py render
```

Per `CLAUDE.md:26-27` these are the known merge-conflict generated files, so the
lead may prefer to do it at merge time together with the post-rebase
`tasks.py render`. Either way it should not be forgotten.

### 2. `ATTEMPTS_CONTRACT.md` §2 misstates why `Order.lean`/`Restrict.lean` are unregistered — severity **minor**, file `research/A02/ATTEMPTS_CONTRACT.md`

§2 says:

> the `Order.lean` and `Restrict.lean` modules exist but their public deliverables
> are not yet the `MaximalSolutionAPI` fields

That is not so. Eight already-merged, `sorry`-free theorems in those two modules
carry docstrings of the form "**Spec field `MaximalSolutionAPI.X`** …, verbatim":

| declaration | spec field |
|---|---|
| `Order.lean:48` `horizon_le_lifespan` | `horizon_le_lifespan` |
| `Order.lean:70` `lifespan_le_iff` | `lifespan_le_iff` |
| `Order.lean:83` `lifespan_le_iff_no_extension` | `lifespan_le_iff_no_extension` |
| `Order.lean:99` `lifespan_ge_of_forall_shorter` | `lifespan_ge_of_forall_shorter` |
| `Order.lean:135` `regularThrough_iff` | `regularThrough_iff` |
| `Order.lean:152` `referenceLifespan` | `referenceLifespan` |
| `Restrict.lean:88` `exists_restrict` | `restrict` (`Spec.lean:345-348`) |
| `Restrict.lean:269` `exists_pressure_normalization` | `pressure_normalization` (`Spec.lean:399-403`) |

This does **not** contaminate the contract: `Contracts/V1/Uniqueness.lean:37-55`
and the `contracts.json` scope say these are "not included … each owed by a later
lane", which is a statement about *registration*, not about proof, and is
therefore true. It is the lane's own record that is wrong, and wrong in a way
that could mislead the next A02 lane into re-proving merged material.

**Fix**: reword §2 to "proved in `Order.lean`/`Restrict.lean` but not registered
here; the brief scopes this lane to `A02.uniqueness`." Worth flagging to the lead
as an opportunity: a follow-on registration lane can bundle roughly eight more
`MaximalSolutionAPI` fields at near-zero proof cost.

### 3. `appendix-a-local-theory.tex:119-124` overshoots by one sentence — severity **informational, do not change**

The `velocity_unique` docstring cites `:119-124`. Lines 119-120 are the display
`½(‖z‖₂²)' + ν‖∇z‖₂² ≤ ‖∇u₂‖_∞‖z‖₂²`, `:122-123` are "The coefficient is bounded
on compact common intervals, since `u₂ ∈ C_tH³`. Grönwall gives uniqueness", and
`:123-124` is "Patching these local solutions defines the maximal lifespan" —
patching being explicitly out of this contract's scope. The uniqueness claim is
fully supported by `:119-123`. **Leave it alone**: the docstring is copied
verbatim from the accepted `Spec.lean:264-266`, and byte-identity with the spec
is worth more than one line of citation range.

---

## Positive findings (recorded, per rule 4)

* **The spec review's H2 was carried forward, not silently dropped.**
  `research/A02/REVIEW.md:27-33` (H2) objected that `MemForceR` is a *strictly
  narrower* force class than `prop:local`'s "smooth into every `H^m`", so the
  draft's "Nothing else is assumed" was false. The contract does not repeat that
  claim; it adds a dedicated section, `Uniqueness.lean:57-65` "The narrowing to
  `F_R`, recorded deliberately", stating the inclusion `F_c ⊆ F_rd ⊆ F_R` and
  warning that "a consumer needing the wider hypothesis must widen these fields".
  The `contracts.json` scope repeats it. This is exactly right.
* `REVIEW.md:71-76` had already spot-checked these two fields and found "no
  defects beyond the above" — confirmed independently here.
* The out-of-scope list is **exhaustive**, not a sample: `MaximalSolutionAPI`
  has 20 fields, the scope names all 19 that are not `uniqueness`, plus the
  auxiliary `def IsMaximalSolution`.
* Every "token-identical"/"byte-identical" claim in the binding docstring was
  verified by `diff`, not taken on trust (see command log).

---

## Command log

All from the worktree `.claude/worktrees/057-A02-uniqueness-contract`, after
`bash scripts/lean-install.sh`, with `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, lake only from `verification/`.

### Gates

| command | result |
|---|---|
| `cd verification && lake build Contracts.V1.Uniqueness Bindings.Uniqueness Tests.Uniqueness` | **exit 0** — `Build completed successfully (9947 jobs)`; `info: Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only` |
| `make check` | **exit 0** — `test_contract_policy` `Ran 13 tests … OK`; `check_work_queue` `30 work items: ownership, contract registration and task cards consistent.` |
| `make test` | **exit 0** — every `checked…` line reports "standard logical axioms only", including `checkedUniqueness` |
| `make test-mutations` | **exit 0** — `implementation_refactor: accepted`, `admitted_proof: rejected as required`, `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed.` |
| `python3 experiments/check_contracts.py --base-ref HEAD` | **exit 0** — `registered_contracts: 11`, `base_compatibility_checked: true`, `A02.uniqueness` closure 1183 modules incl. `Tests.Uniqueness` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | **raises** `AssertionError: Removed stable specification: verification/Contracts/V2/DatumLemmas.lean` — **base drift, confirmed not this lane's** |

Base-drift confirmation (the point of running it twice):

```
git merge-base HEAD origin/erenup/integration  ->  185089b "Record lane 053 PR"
git diff --name-status origin/erenup/integration HEAD -- verification/{Contracts,Bindings,Tests}/
  A  verification/Contracts/V1/Uniqueness.lean      <- this lane
  A  verification/Bindings/Uniqueness.lean          <- this lane
  A  verification/Tests/Uniqueness.lean             <- this lane
  D  verification/Contracts/V2/DatumLemmas.lean     <- base drift (D01.datum_lemmas_v2)
  D  verification/Bindings/DatumLemmasV2.lean       <- base drift
  D  verification/Tests/DatumLemmasV2.lean          <- base drift
contracts.json ids  BASE: [… D01.datum_lemmas, D01.datum_lemmas_v2]
                    HEAD: [… D01.datum_lemmas, A02.uniqueness]
```

No existing specification is modified or removed by the lane; the three `D`
entries are exactly the `D01.datum_lemmas_v2` trio that landed on integration
after the fork point. The assertion message names only `Contracts/V2/DatumLemmas.lean`
because `check_compatibility` iterates base `Contracts/*.lean` files and stops at
the first missing one. Resolved by the lead's merge-time rebase.

Hygiene: `grep -n "maxHeartbeats\|sorry\|axiom \|native_decide\|set_option"` over
the three lane files returns **nothing**. `grep -rn "sorry\|^axiom \|maxHeartbeats"`
over `formalization/NSFormalization/Section4/A02/` returns **nothing**.
`Contracts/V1/Uniqueness.lean` has exactly one import: `Contracts.V1.Data`.

### Statement fidelity

```
awk 'NR>=263 && NR<=281' research/A02/Spec.lean               > /tmp/spec_uniq.txt
awk 'NR>=85  && NR<=103' verification/Contracts/V1/Uniqueness.lean > /tmp/contract_uniq.txt
diff /tmp/spec_uniq.txt /tmp/contract_uniq.txt    ->  no output
md5sum  ->  4123a8a6f727b9c3e1bed7ce819b187d  (both files)
```

Byte-identical, docstrings included. So binder names (`ν a f T₁ T₂ u₁ u₂ t x`),
`(0 : ℝ)`, `Ico 0 (min T₁ T₂)` and the hypotheses `0 < ν`, `a ∈ initialClassR`,
`MemForceR f` all match by construction. Confirmed in the elaborated type as
well, with `pp.fullNames`:

```
UniquenessAPI.velocity_unique : UniquenessAPI →
  ∀ (ν : ℝ) (a : …Contracts.V1.Data.SpatialField) (f : …Contracts.V1.Data.SpaceTimeField),
    0 < ν → a ∈ …Contracts.V1.Data.initialClassR → …Contracts.V1.Data.MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : …Contracts.V1.Data.ClassicalSolutionR ν a f T₁) (u₂ : … T₂),
        ∀ t ∈ Set.Ico 0 (Min.min T₁ T₂), ∀ (x : NavierStokes.ProblemStatement.Space),
          u₁.velocity (t, x) = u₂.velocity (t, x)
```

Every name resolves inside `BlowupDensity.Contracts.V1.Data`. No `NSFormalization`
name appears in either field type.

Paper citations, each re-opened:

| cited | text found | verdict |
|---|---|---|
| `appendix-a-local-theory.tex:119-120` | the display `\tfrac12(\norm{z}_2^2)'+\nu\norm{\nabla z}_2^2 \le\norm{\nabla u_2}_\infty\norm{z}_2^2` | correct |
| `appendix-a-local-theory.tex:122-123` | "The coefficient is bounded on compact common intervals, since $u_2\in C_tH^3$. Gr\"onwall gives uniqueness." | correct |
| `appendix-a-local-theory.tex:119-124` (field docstring) | as above, plus one sentence of patching at `:123-124` | correct, one sentence wide — finding 3 |
| `02-preliminaries.tex:31` | "the scalar pressure is determined up to / a function of time" (wraps to `:32`) | correct |
| `02-preliminaries.tex:105` | `\begin{proposition}[Local existence, uniqueness, and continuation]`, labels `prop:local`/`lem:Rlocal` on `:106` | correct |
| `02-preliminaries.tex:107-109` | "each force smooth into / every $H^m$ on compact time intervals" | correct |
| `02-preliminaries.tex:12` | `\mathcal X_{\R}=H^\infty(\R^3;\R^3)\cap L^2_\sigma(\R^3)` = `initialClassR` (`Data.lean:509`) | correct |
| `04-whole-space.tex:53` | "Proposition~\ref{prop:local} identifies the solution with the unique maximal solution." | correct |
| `04-whole-space.tex:183-192` | `\mathcal F_c` and `\mathcal F_{\mathrm{rd}}` defined as "subclasses of $\mathcal F_{\R}$" | correct |
| `Data.lean:544` / `:589` / `:624-648` | `MemForceR` / `PressureGaugeEquivOn` / `ClassicalSolutionR` | correct |
| `DEPENDENCY_GRAPH.md` `A02 ← A01`, `A02 → A04`, `A02 → C01`, `A02 → R42` | `:186` A02 deps A01; `:207` A04 deps A02,A03; `:277` C01 deps A02,A05; `:259` R42 deps I03,A02 | correct |

Docstring honesty about scope: `Uniqueness.lean:3` "Stable specification for the
**uniqueness** half of A02's local theory", `:9-10` "A01 owns existence and A04
the continuation criterion, and A02 owns the middle third", `:76` "**The
uniqueness half of `prop:local` on `R³`**", and the dedicated `:37-55` "Out of
scope" section. Honest throughout; no field is stated more strongly than the
manuscript.

### Binding honesty

`uniqueness_toA02` (`Bindings/Uniqueness.lean:63-75`) is exactly ten bare
projections and nothing else — `velocity, pressure, horizon_pos,
velocity_smooth, pressure_smooth, initial, divergence, momentum, sobolev,
pressure_gradient`, each `:= w.<same name>`. No tactic block, no lemma applied.

The binding `theorem uniqueness` (`:93-99`) has two fields, each a lambda over
the ten binders followed by a single application:

```
velocity_unique := fun ν a f hν ha hf T₁ T₂ u₁ u₂ =>
  NSFormalization.Section4.A02.velocity_unique ν a f hν ha hf T₁ T₂
    (uniqueness_toA02 u₁) (uniqueness_toA02 u₂)
```

No `by`, no `show`, no `exact` anywhere in the file. Note that `ha`/`hf` are
passed **straight through** where the A02 theorem expects its own
`initialClassR`/`MemForceR` — nothing is converted, so no proof content can hide
in a conversion. The lane's claim that definitional unfolding suffices is
therefore confirmed by reading, and independently by the file compiling.

The three `rfl` bridges pair the right definitions — verified by `diff`, not by
reading:

| bridge | contract side | A02 side | `diff` |
|---|---|---|---|
| `uniqueness_initialClassR_eq` | `Data.lean:509` | `SolutionClass.lean:97` | identical |
| `uniqueness_memForceR_eq` | `Data.lean:544-550` | `SolutionClass.lean:100-106` | identical |
| `uniqueness_pressureGaugeEquivOn_eq` | `Data.lean:589-590` | `SolutionClass.lean:109-110` | identical |

The binding docstring's further claim that `SolutionClass.lean:114` is
byte-identical to `Data.lean:624-648` also holds:
`diff <(awk 'NR>=624&&NR<=648' Data.lean) <(awk 'NR>=114&&NR<=138' SolutionClass.lean)`
produces no output.

`theorem` rather than `def`: correct and necessary. Both `UniquenessAPI` fields
are `Prop`, so the structure lands in `Prop`, and `Tests` is built with
`warningAsError = true` where `linter.defProp` rejects a `def`. `TestSupport.checkAxioms`
handles it fine — it ran and printed the "checked" line — and `#print axioms`
names the theorem explicitly:

```
'BlowupDensity.Tests.checkedUniqueness'      depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.uniqueness'          depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.uniqueness_toA02'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard logical axioms only, no `sorryAx`, no project axiom.

### Scope string in `contracts.json`

`MaximalSolutionAPI` (`Spec.lean:312`) has 20 fields. The scope excludes 19 of
them by name — `horizon`, `localSolution`, `horizonLowerBound`, `restrict`,
`patch`, `horizon_le_lifespan`, `pressure_normalization`, `exists_maximal`,
`maximal_unique`, `lifespan_le_iff`, `lifespan_le_iff_no_extension`,
`lifespan_ge_of_forall_shorter`, `regularThrough_iff`, `referenceLifespan`,
`restart_datum`, `restart_force`, `restart`, `lifespan_le_of_unbounded`,
`insertion_lifespan_eq` — plus the auxiliary `def IsMaximalSolution`
(`Spec.lean:210`). The one field not excluded is `uniqueness`, which is what is
registered. The complement is exact: nothing registered is omitted from the
scope, and nothing excluded is actually delivered.

No overclaim elsewhere in the string: it states the narrowing to `MemForceR`
("strictly smaller than prop:local's smooth-into-every-H^m class") rather than
hiding it, names the discharging theorems and lanes, explains the field-by-field
conversion and why a `rfl` bridge is impossible for the structure, and disclaims
`eq:mild`, `eq:criterion`, smallness / common-horizon / compact-support /
`p ∈ L²` side conditions, and the Grönwall coefficient's finiteness.

### Round trip (scratch file, since deleted)

Applied the *bound* field to solutions of the **contract** structure and asked
Lean to accept a goal written purely in contract vocabulary:

```lean
example (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (hν : 0 < ν)
    (ha : a ∈ initialClassR) (hf : MemForceR f) (T₁ T₂ : ℝ)
    (u₁ : ClassicalSolutionR ν a f T₁) (u₂ : ClassicalSolutionR ν a f T₂)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (min T₁ T₂)) (x : Space) :
    u₁.velocity (t, x) = u₂.velocity (t, x) :=
  BlowupDensity.Bindings.uniqueness.velocity_unique ν a f hν ha hf T₁ T₂ u₁ u₂ t ht x
```

plus the analogous `pressure_gauge` example landing on
`PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure`.
Both accepted, `exit 0`. Printing the applied term with `pp.explicit true` gives
a conclusion

```
@Eq Space (@ClassicalSolutionR.velocity ν a f T₁ u₁ (@Prod.mk Real Space t x))
          (@ClassicalSolutionR.velocity ν a f T₂ u₂ (@Prod.mk Real Space t x))
```

with `ClassicalSolutionR` resolving to `BlowupDensity.Contracts.V1.Data.ClassicalSolutionR`
(shown by the `pp.fullNames` print above). **No `uniqueness_toA02` and no
`NSFormalization.Section4.A02` name appears anywhere in the public type.** The
adapter is fully absorbed; a consumer never sees it. Scratch file deleted; the
worktree is clean (`git status --short` empty apart from this review file).
