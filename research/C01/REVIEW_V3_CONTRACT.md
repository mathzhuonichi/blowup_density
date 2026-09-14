# REVIEW — lane 156-C01-v3-contract (C01 V3: `energyDifferentialBound` + `l2Bound` = eq:RL2)

Reviewer: opus, read-only, worktree `.claude/worktrees/156-C01-v3-contract`, branch
`erenup/156-C01-v3-contract`, HEAD `0de4416`.  Probes written:
`research/C01/probes/rev156_{mutation,nonvacuity,resolution}.lean` (new files only; no tracked
file touched, no git state changed — `git status --short` shows exactly those three `??` lines).

## Verdict: **ACCEPT-WITH-NOTES**

The Lean statements are byte-identical to `Spec.lean`, the mathematics is the manuscript's, the
binding assumes nothing extra, all gates are green, three contract-statement mutations are
rejected and both fields are non-vacuously instantiated through the registered witness.  The
notes are **docstring / registry-scope paper line references that are off by one**; they are
listed only because `Contracts/V3/*` and the registry scope are frozen by CI the moment they
merge (this is exactly the failure mode `logs/LESSONS.md` records for 117 → 120, nine frozen
copies), so five one-line `sed` fixes are cheaper now than never.  None touches a Lean statement.

---

## 1. What the contract claims

`verification/Contracts/V3/EnergyAbsorptionPartial.lean:121` registers

```
structure EnergyAbsorptionPartialV3API extends
    BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API
```

with exactly **two** new fields and **two** new spec-local `def`s.

* `energyDifferentialBound` (`:136-142`): for `0 < ν`, `a ∈ initialClassR`, `MemForceR f`, a
  classical whole-space solution `w : ClassicalSolutionR ν a f T`, every **interior**
  `t ∈ Ioo 0 T` and **every real `E'`** with
  `HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t`:
  `E' + 2*ν*gradientSq (slice w.velocity t) ≤ 2 * l2Norm (slice f t) * l2Norm (slice w.velocity t)`.
  This is the **doubled Cauchy–Schwarz form** of the §2 energy identity
  `½(‖U(t)‖₂²)' + ν‖∇U(t)‖₂² = ⟨F(t),U(t)⟩` (`paper/sections/02-preliminaries.tex:137-140`,
  with the "Dropping dissipation gives `½(‖U‖₂²)' ≤ ‖F‖₂‖U‖₂`" step at `:141-142` — the cited
  range `:136-142` is **correct** and well chosen).
* `l2Bound` (`:156-160`) = **eq:RL2**: same hypotheses, every **presingular** `t ∈ Ico 0 T`,
  `l2Norm (slice w.velocity t) ≤ energyBudget a f t`.  The manuscript display is
  `paper/sections/04-whole-space.tex:119`
  (`\norm{u(t)}_2\le\norm{a}_2+\int_0^t\norm{f(s)}_2\dd s=:K(t)`, label at `:118`) — **no
  smallness hypothesis, no absorption, no spectral gap**, exactly as the contract's scope
  disclosure 4 says.
* `forcePrimitive` (`:94-95`) `= ∫ s in (0:ℝ)..t, l2Norm (slice f s)` and `energyBudget`
  (`:101-102`) `= l2Norm a + forcePrimitive f t`, i.e. `K(t)`.

Slack, disclosed in the two field docstrings, in scope items 1–2 and in the registry scope:
`0 < ν` is unused by `energyDifferentialBound` and is consumed by `l2Bound` **only through
`0 ≤ ν`**; `a ∈ initialClassR` is unused by both.  I checked this against the lane-154 theorems:
`Section4/C01/EnergyBounds.lean:133` `energyDifferentialBound` takes **no** `ν`-positivity and
**no** `initialClassR`, and `:239` `l2Bound` takes `hν : 0 < ν` whose **only** occurrence in the
proof body is `hν.le` at `EnergyBounds.lean:295` (`mul_nonneg (mul_nonneg (by norm_num) hν.le) (gradientSq_nonneg _)`,
the dissipation-discarding step).  Direction is the safe one: the contract asserts **less** than
the theorem proves.

## 2. What is in Lean

### 2.1 Statement fidelity — byte-identical to `Spec.lean` (finding: none)

Mechanical diff (not by eye), both raw and whitespace-normalised:

| contract | `Spec.lean` | result |
|---|---|---|
| `Contracts/V3/EnergyAbsorptionPartial.lean:136-142` | `research/C01/Spec.lean:364-370` | **byte-identical** |
| `:156-160` | `:383-387` | **byte-identical** |
| `:94-95` (`forcePrimitive`) | `:218-219` | **byte-identical** |
| `:101-102` (`energyBudget`) | `:224-225` | **byte-identical** |

`gradientSq`/`slice`/`l2Sq`/`l2Norm` are **not** re-declared: `Contracts/V3/…:85-86` opens them
from V1/V2.  `research/C01/probes/rev156_resolution.lean` prints the elaborated field types with
`pp.fullNames`, confirming the constants the fields actually mention:

* `…Contracts.V2.EnergyAbsorptionPartial.gradientSq`, itself
  `fun z => ∫ x, ‖BlowupDensity.Contracts.V1.gradientTensor z x‖ ^ 2` — the **registered
  `gradientTensor` Frobenius form**, not the tree's same-named raw-integral `gradientSq`;
* `…Contracts.V1.EnergyAbsorptionPartial.{slice,l2Sq,l2Norm}`;
* `…Contracts.V3.EnergyAbsorptionPartial.energyBudget` = `l2Norm a + forcePrimitive f t`;
* `Set.Ico 0 T` in `l2Bound`, `Set.Ioo 0 T` in `energyDifferentialBound`.

Quantifier order is the safe one everywhere: `ν`, `a`, `f`, `T`, `w`, `t`, `E'` are all
universally quantified **inside** the record, the constant `C₁` stays the single inherited data
field quantified **outside**, and `E'` is quantified before the `HasDerivAt` hypothesis, so no
constant is chosen after the datum.

### 2.2 Structure / policy (finding: none)

* `extends EnergyAbsorptionPartialV2API` (`:121-122`) — structural inheritance, so no V1/V2
  field can be silently dropped or weakened.
* `git diff origin/erenup/integration -- verification/Contracts/V1 verification/Contracts/V2
  verification/Tests/EnergyAbsorptionPartial.lean verification/Tests/EnergyAbsorptionPartialV2.lean`
  → **0 lines**.  `git diff --stat origin/erenup/integration -- verification/` → 4 files,
  **339 insertions, 0 deletions**.
* Imports: the contract has exactly one, `import Contracts.V2.EnergyAbsorptionPartial`
  (`:1`) — inside `check_contracts.py`'s `contract_import_allowed`.
* `experiments/check_contracts.py:118` asserts `f'/V{version}/' in specification`; the path is
  `verification/Contracts/V3/EnergyAbsorptionPartial.lean` with `version: 3` → accepted (the
  run below is exit 0).
* No `sorry` / `admit` / `axiom` / `native_decide` in any of the four new Lean files.

### 2.3 Bindings (finding: none)

`verification/Bindings/EnergyAbsorptionPartialV3.lean:77-86`:

```
def energyAbsorptionPartialV3 : …EnergyAbsorptionPartialV3API :=
  { energyAbsorptionPartialV2 with
    energyDifferentialBound := fun _ _ _ _ _ hf _ w _ ht E' hderiv => by
      rw [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.energyDifferentialBound (uniqueness_toA02 w) hf ht E' hderiv
    l2Bound := fun _ hν _ _ _ hf _ w _ ht =>
      NSFormalization.Section4.C01.l2Bound (uniqueness_toA02 w) hf hν ht }
```

* **`l2Bound` is bridge-free** — closed by the tree theorem directly.
* **`energyDifferentialBound` goes through exactly one `rw`**, the already-existing V2 bridge
  `energyAbsorptionPartialV2_gradientSq_eq` (`Bindings/EnergyAbsorptionPartialV2.lean:70-75`,
  the cited lines are correct).  **Direction confirmed empirically**, not from the docstring: in
  mutation C below, the goal after the `rw` is printed as
  `E' + 2*ν*∫ x, ∑ i, ‖fderiv ℝ (slice w.velocity t) x (coordinateVector i)‖^2 ≤ …`, i.e. the
  rewrite goes **contract `gradientSq` → raw Frobenius integrand**, matching the lane's theorem.
  No second rewrite, no `simp`, no extra lemma.
* **Nothing else is assumed.**  Binder counts match the field types exactly (12 binders for
  `energyDifferentialBound`, 10 for `l2Bound`); the anonymous `_`s are precisely `ν`, `hν`, `a`,
  `ha`, `f`, `T`, `t` (and `hν` only in `energyDifferentialBound`), so the binding consumes no
  hypothesis the contract does not offer, and offers none it does not use.
* `energyAbsorptionPartialV3_forcePrimitive_eq` / `_energyBudget_eq` (`:54-59`, `:62-66`) are `rfl`
  bridges to `NSFormalization.Section4.C01.forcePrimitive` / `energyBudget` — one per rewritten
  definition, as CLAUDE.md requires.
* `energyAbsorptionPartialV2_of_v3 : energyAbsorptionPartialV3.toEnergyAbsorptionPartialV2API
  = energyAbsorptionPartialV2 := rfl` (`:93-96`) — the V2 projection **is** the frozen V2
  witness, so nothing V1/V2 guarantees is lost.

### 2.4 Tests / registry (finding: none)

* `Tests/EnergyAbsorptionPartialV3.lean:37` `def checkedEnergyAbsorptionPartialV3`, `:41`
  `run_cmd TestSupport.checkAxioms`, plus one conformance `example` per new field (`:50-59`,
  `:61-67`), each discharged by the corresponding field of the checked witness.
* Tests imports are `Contracts.V3.EnergyAbsorptionPartial`, `Bindings.EnergyAbsorptionPartialV3`,
  `TestSupport.Axioms` only — **no `Formal.*`** (the single textual hit is the word inside the
  module docstring), so `warningAsError = true` is respected; `make test` is clean.
* `verification/contracts.json`: one entry appended, `id: C01.energy_absorption_partial_v3`,
  `version: 3`, `parent_task: C01`, `specification: verification/Contracts/V3/EnergyAbsorptionPartial.lean`,
  `binding_module: Bindings.EnergyAbsorptionPartialV3`, `test_module: Tests.EnergyAbsorptionPartialV3`,
  `declaration: BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3` — all four resolve to real
  files/declarations.  `git diff` on the file is **+11 / −0**; `grep -c '\u0' ` → **0** (no
  `\uXXXX` escapes, i.e. `ensure_ascii=False` was used).
* Scope string: honest.  Both "INCLUDED FIELD" paragraphs transcribe the Lean statements
  correctly; the five disclosures match what I verified independently (slack hypotheses,
  Frobenius reading, `E'`-not-`deriv`, `Ico` load-bearing); the "NOT INCLUDED" list matches V1/V2's.
* `collaboration/work_items.json` / `TASKS.md` / `tasks/C01.md`: the C01 item's `contracts` list
  gains exactly `C01.energy_absorption_partial_v3`, cards regenerated by `tasks.py render`
  (no hand-written text in the generated cards).  `check_work_queue.py` → consistent.
* `research/C01/ENERGY_SPLIT.md`: the two row updates are additive and accurate.

### 2.5 Honesty of `ATTEMPTS_V3_CONTRACT.md` (finding: none)

Every cited declaration opened at its cited line and matched:
`Bindings/EnergyAbsorptionPartialV2.lean:70-75` (`energyAbsorptionPartialV2_gradientSq_eq`),
`Contracts/V2/EnergyAbsorptionPartial.lean:58-61` (the "left to a future version" disclosure that
motivates V3), `DEPENDENCY_GRAPH.md:277` (`Dependencies: A02, A05`) and `:285`/`:292`
(R43/R44, `Dependencies: A04, A05, C01`), `probes/rev154_v3_binding_dryrun.lean` (the dry run
really does state both fields in the contract vocabulary and discharge them with exactly the
bridge count claimed), `probes/rev154_icc_false.lean` (really proves `l2Bound_Icc_false`, not
merely "unprovable"), `probes/rev154_t0_nonvacuous.lean`.  The ATTEMPTS' command log matches
what I reproduced.

## 3. Gaps — the notes

All five are **paper line references inside frozen text**; none changes a Lean statement, a
binding or a test.  Verified at HEAD with `grep -n` on `paper/sections/04-whole-space.tex`
(per `logs/LESSONS.md`, not copied from an earlier review):

* line **117** = `This controls the gradient … It does not control low frequencies by itself.
  The separate ordinary energy identity, with regularized norm division, supplies`
* line **118** = `\begin{equation}\label{eq:RL2}`, line **119** = the display, **120** = `\end{equation}`
* line **132** = `Proposition~\ref{prop:local} … The low frequencies have been controlled
  directly by the ordinary energy estimate.`
* line **104** = `Choosing $c<1/(4C_0)$ … including times at which $y=0$.` (line 103 is `\]`)

| # | severity | where | now | should be |
|---|---|---|---|---|
| 1 | note | `Contracts/V3/…:66` (scope item 4) | `04-whole-space.tex:116` "It does not control low frequencies by itself", `:131` "The low frequencies have been controlled…" | `:117` and `:132` |
| 2 | note | `Contracts/V3/…:150-151` (`l2Bound` docstring) | same two quotes at `:116` / `:131` | `:117` and `:132` |
| 3 | note | `Contracts/V3/…:134` (`energyDifferentialBound` docstring) | `‖u(t)‖₂ = 0` at `(\`:103\`)` | `(\`:104\`)` |
| 4 | note | `Contracts/V3/…:124` and `:143` | `04-whole-space.tex:116-121` | `:117-121` (or `:118-121`, which is what `Spec.lean` and `Section4/C01/EnergyBounds.lean:10` use for eq:RL2) |
| 5 | note | `contracts.json`, the V3 scope | `manuscript source 04-whole-space.tex:116-121` | same fix as #4 |

Notes 1–3 are inherited verbatim from `research/C01/Spec.lean:379-380` and `:363`, so `Spec.lean`
carries the same off-by-one; fixing it there too would stop the next version inheriting it.
Note that the already-frozen `Contracts/V2/EnergyAbsorptionPartial.lean:111` cites the **correct**
`:117` for the same sentence, so V3 is currently inconsistent with its own parent.

Non-blocking, for the record (no action): the V3 contract does not `open
NavierStokes.ProblemStatement` (V2 does); it does not need to, and it compiles.

## 4. Commands and results

All from the worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from `verification/`.

**`bash scripts/gates.sh` → exit 0.**

```
== make check
… check_formalization_plan.py --check: OK
… check_contracts.py: {"registered_contracts": 26, …}
… test_contract_policy.py: OK
… check_work_queue.py: 30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/EnergyAbsorptionPartial.lean:15:0:   Contract …checkedEnergyAbsorptionPartial:   checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV2.lean:32:0: Contract …checkedEnergyAbsorptionPartialV2: checked; standard logical axioms only
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract …checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
(26 Contract lines in total, all "checked; standard logical axioms only"; no error, no sorry)
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
```

**`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` → exit 0**,
`{'registered_contracts': 26, 'base_compatibility_checked': True}`.

**`cd verification && lake env lean ../research/C01/axioms_v3_contract.lean` → exit 0**:

```
'BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.energyDifferentialBound'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Bound'                   depends on axioms: [propext, Classical.choice, Quot.sound]
```

(the three `rfl`-bridge `example`s in that file emit nothing, i.e. they typecheck.)

**Negative check — three mutations of the contract statement**,
`research/C01/probes/rev156_mutation.lean` (scratch structures extending
`EnergyAbsorptionPartialV2API`, each fed the **verbatim** binding proof term).
`lake env lean …/rev156_mutation.lean` → **exit 1, all three rejected**:

* **A. `Ico 0 T` → `Icc 0 T` in `l2Bound`** (`:33:70`):
  `Application type mismatch: the argument ht has type x✝ ∈ Icc 0 x✝¹ but is expected to have
  type x✝ ∈ Ico 0 x✝¹`.  (And `probes/rev154_icc_false.lean` shows the widening is not merely
  unprovable but **false**.)
* **B. the `∫₀ᵗ‖f‖₂` term dropped from `energyBudget`** (`:50:6`): `Type mismatch … has type
  … ≤ NSFormalization.Section4.C01.energyBudget x✝⁴ x✝² x✝ but is expected to have type
  l2Norm (slice w.velocity x✝) ≤ energyBudgetB x✝⁴ x✝² x✝`.
* **C. `2 * l2Norm … * l2Norm …` → `l2Norm … * l2Norm …`** (`:68:6`): `Type mismatch …
  ≤ 2 * …l2Norm … * …l2Norm … but is expected to have type … ≤ l2Norm (slice x✝² x✝) *
  l2Norm (slice w.velocity x✝)`.  This error also **prints the post-`rw` goal**, which is how
  the `gradientSq` rewrite direction was confirmed (see §2.3).

**Non-vacuity** — `research/C01/probes/rev156_nonvacuity.lean` → **exit 0**.  The whole
hypothesis block is satisfiable: `W : ClassicalSolutionR 1 0 0 2 :=
maximalPartial_ofA02 (A04.zeroSol 1 2 one_pos …)`, with `A04.zero_mem_initialClassR` and
`A04.memForceR_zero`.  Through the **registered witness** `Bindings.energyAbsorptionPartialV3`:

* `rev156_l2Bound_zero : l2Norm (slice W.velocity 0) ≤ energyBudget 0 0 0` (the left endpoint
  `t = 0` of `Ico 0 2`, the load-bearing one);
* `rev156_l2Bound_one : l2Norm (slice W.velocity 1) ≤ energyBudget 0 0 1`;
* `rev156_edb`: the differential bound at `t = 1 ∈ Ioo 0 2`, fed the derivative produced by the
  **inherited V2 `energyIdentity`** (the consumer route the contract docstring advertises), so
  the two fields compose as claimed.

All three `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

**Constant resolution** — `research/C01/probes/rev156_resolution.lean` → exit 0, output quoted
in §2.1.
