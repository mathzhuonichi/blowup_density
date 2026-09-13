# Review — lane 054, `D01.datum_lemmas_v2`

Reviewer: independent opus reviewer (lane 054 review pass).
Worktree: `.claude/worktrees/054-D01-datum-lemmas-v2`, head `27dc193`.
Base: `origin/erenup/integration`.

## Verdict: **ACCEPT-WITH-NOTES**

The contract states exactly the three theorems lane 042 proved, with the same
hypotheses and no strengthening; the binding is pure theorem application with
zero `by` blocks; V1 is byte-unchanged; every gate is green; the JSON `scope`
is honest about the homogeneous half of G3 and the G2 path-level comparison.
Two findings, both **nit** severity and both in doc comments only — neither
changes a statement, a proof, or the trust boundary. Merge is not blocked.

---

## 1. Gates

All run from the worktree with `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
no `-j`; every `lake` invocation from `verification/`, one at a time.

### 1.1 Targeted build

```
cd verification && lake build Contracts.V2.DatumLemmas Bindings.DatumLemmasV2 Tests.DatumLemmasV2
```
```
info: Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
Build completed successfully (9898 jobs).
```

### 1.2 `make check`

```
python3 experiments/check_formalization_plan.py --check
python3 experiments/check_contracts.py
python3 experiments/test_contract_policy.py   → Ran 13 tests ... OK
python3 experiments/check_work_queue.py       → 30 work items: ownership, contract registration and task cards consistent.
```
All four ran to completion (make chains them; no abort).

### 1.3 `make test`

```
lake -d verification test
```
```
Tests/DatumLemmasV2.lean:23:0: Contract BlowupDensity.Tests.checkedDatumLemmasV2: checked; standard logical axioms only
Tests/DatumLemmas.lean:14:0:   Contract BlowupDensity.Tests.checkedDatumLemmas:   checked; standard logical axioms only
(+ Thresholds, Packet, Scaling, Correction, CorrectionV2, InsertionFamily,
   BoundedRepresentative, GradientL6, TameProduct — all "standard logical axioms only")
```
`checkedDatumLemmasV2` reports **standard logical axioms only**. ✅

### 1.4 `make test-mutations`

```
implementation_refactor: accepted
admitted_proof:          rejected as required
extra_axiom:             rejected as required
weakened_hypothesis:     rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### 1.5 Base-compatibility contract check

```
python3 experiments/check_contracts.py --base-ref origin/erenup/integration
  → EXIT=0,  "base_compatibility_checked": true
  → registered_contracts = 11
  → D01.datum_lemmas_v2 closure = 1134 modules,
    includes NSFormalization.Section4.D01.HalfOrder  (True)
```
Lane 042's `HalfOrder.lean` is now inside a *tested* closure — the stated point
of the lane, confirmed independently.

### 1.6 V1 frozen

```
git diff origin/erenup/integration -- verification/Contracts/V1 \
    verification/Tests/DatumLemmas.lean verification/Bindings/DatumLemmas.lean
  → (empty)          status: UNCHANGED
```
Full diff vs base touches only: `NEXT_SESSION.md`, `PLAN.md`, `logs/LESSONS.md`,
`research/D01/ATTEMPTS_CONTRACT_V2.md`, `verification/Bindings/DatumLemmasV2.lean`
(new), `verification/Contracts/V2/DatumLemmas.lean` (new),
`verification/Tests/DatumLemmasV2.lean` (new), `verification/contracts.json`.

### 1.7 Hygiene

```
grep -n "^import" verification/Contracts/V2/DatumLemmas.lean
  1:import Contracts.V1.DatumLemmas          ← the only import, a Contracts.* module
grep -n "maxHeartbeats" <the three new files>   → (none)
```
`Contracts/V1/DatumLemmas.lean` itself imports only `Contracts.V1.Data`,
`Contracts.V1.GradientL6`, `Contracts.V1.BoundedRepresentative` — so the V2
contract's transitive import set is contracts only, as its "Self-containedness"
paragraph claims. No implementation module reachable from the spec. ✅

---

## 2. Binding honesty — `Bindings/DatumLemmasV2.lean`

**Zero `by` blocks.** `grep -n "\bby\b"` hits lines 9, 15, 17, 66, 78 — every one
inside a doc comment (prose "…by three fields", "no `by` block", "by the
inherited projection", "is by definition", "by the inherited projection").
No term-level `by` anywhere. ✅

**Every new field is `:= HalfOrder.theorem`, argument permutation only:**

| field | value |
|---|---|
| `forceSobolevENorm_ne_top` | `fun _ hf _ _ hsm _ hq => …D01.forceSobolevENorm_ne_top hf hsm hq` |
| `forceSobolevENormL1_half_ne_top` | `fun _ hf => …D01.forceSobolevENormL1_half_ne_top hf` |
| `forceSobolevENormL2_half_ne_top` | `fun _ hf => …D01.forceSobolevENormL2_half_ne_top hf` |

The `fun _ … =>` prefixes only re-bind the implicit/explicit binders that
`HalfOrder` leaves implicit (`{f}`, `{s}`, `{m}`, `{q}`) and that the contract
makes explicit. No transport, no `Or.elim`, no rewriting. ✅

**The two `rfl` bridges — pairs confirmed:**

| bridge (`Bindings/DatumLemmasV2.lean`) | left | right |
|---|---|---|
| `datumLemmasV2_forceSobolevENorm_eq` :46 | `NSFormalization.Section4.D01.forceSobolevENorm q s f` (`HalfOrder.lean:141`, `def`) | `Contracts.V1.Data.forceSobolevENorm q s f` (`Data.lean:225`) |
| `datumLemmasV2_forceSobolevENormL1_eq` :52 | `NSFormalization.Section4.D01.forceSobolevENormL1 s f` (`HalfOrder.lean:148`, `abbrev`) | `Contracts.V1.Data.forceSobolevENormL1 s f` (`Data.lean:231`) |

Both `:= rfl`, both compile. Read side by side, the two definitions are
character-for-character the same infimum (`⨅ G : {G // IsSobolevPath s f G ∧
AEStronglyMeasurable G forceTimeMeasure}, bochnerDatumENorm q s G.1`), so the
bridges do what they claim: CI breaks if either side drifts.

The docstring's two "no bridge needed" claims check out:
* `MemForceR`: `Bindings/DatumLemmas.lean:118` `datumLemmas_memForceR_eq :
  NSFormalization.Section4.D01.MemForceR f = Contracts.V1.Data.MemForceR f := rfl`
  exists in the imported V1 binding, not repeated. ✅
* `forceSobolevENormL2`: `HalfOrder.lean` has no local copy — line 184 writes
  `forceSobolevENorm 2 (1 / 2) f` directly, and `Data.lean:235` is
  `abbrev forceSobolevENormL2 (s) (f) := forceSobolevENorm 2 s f`. So the L²
  field is the L^q bridge at `q = 2`; nothing extra to pin. ✅
* Type names: `Contracts/V1/Data.lean:104` is `abbrev SpaceTimeField :=
  VelocityField`, so `HalfOrder`'s `{f : VelocityField}` and the contract's
  `(f : SpaceTimeField)` are the same type, not a coincidence of elaboration.

**`datumLemmas_of_v2` is the plain projection.** `:= datumLemmasV2.toDatumLemmasAPI`,
the `extends`-generated parent projection, nothing else. I checked (scratch,
deleted) that it is definitionally the *frozen* V1 witness, not a rebuilt one:

```lean
example : Bindings.datumLemmas_of_v2 = Bindings.datumLemmas := rfl   -- ✅ compiles
```

so no V1 field was silently re-derived or re-proved while passing through V2.

---

## 3. Statement fidelity — the three new fields vs `HalfOrder.lean`

| | `HalfOrder.lean` | `Contracts/V2/DatumLemmas.lean` |
|---|---|---|
| general | `:156` `forceSobolevENorm_ne_top {f} (hf : MemForceR f) {s : ℝ} {m : ℕ} (hsm : s ≤ (m:ℝ)) {q : ℝ≥0∞} (hq : q = 1 ∨ q = 2) : forceSobolevENorm q s f ≠ ⊤` | `:120` `∀ (f : SpaceTimeField), MemForceR f → ∀ (s : ℝ) (m : ℕ), s ≤ (m:ℝ) → ∀ q : ℝ≥0∞, q = 1 ∨ q = 2 → forceSobolevENorm q s f ≠ ⊤` |
| L¹ instance | `:178` `forceSobolevENormL1_half_ne_top {f} (hf) : forceSobolevENormL1 (1/2) f ≠ ⊤` | `:133` `∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤` |
| L² instance | `:183` `forceSobolevENormL2_half_ne_top {f} (hf) : forceSobolevENorm 2 (1/2) f ≠ ⊤` | `:140` `∀ f, MemForceR f → forceSobolevENormL2 (1/2) f ≠ ⊤` |

Identical up to binder explicitness and the two bridged names. In particular the
hypotheses are **exactly** `s ≤ (m : ℝ)` with `m : ℕ`, `q = 1 ∨ q = 2`, and
`MemForceR f` — nothing stronger (no `HasCompactSupport`, no `0 ≤ s`, no
Schwartz component, no measurability side condition), and nothing weaker.
`(1 / 2)` is one fixed spelling on both sides, so no transport is hidden.

**Line citations in the field doc comments are right:** `:156` is the `theorem`
keyword of `forceSobolevENorm_ne_top`, `:178` of `forceSobolevENormL1_half_ne_top`,
`:183` of `forceSobolevENormL2_half_ne_top`. (The briefing's `157,177,183` are
off by one on the first two; the contract's numbers are the correct ones.)

**Paper citations verified against `paper/sections/04-whole-space.tex`:**
* `:82-89` = `\begin{proposition}[Global regularity for small critical data and
  $L^1$ force]\label{prop:Rcritical1}` … `\end{proposition}`. ✅
* `:88` = "In particular, for $a=0$, the ball $\norm{f}_{L^1_tH^{1/2}_x}<c\nu$
  consists of globally regular inputs." — the *inhomogeneous* ball, exactly what
  `forceSobolevENormL1 (1/2)` is. ✅
* `:136-144` = `\begin{proposition}[Regularity on a prescribed finite interval]
  \label{prop:Rcritical2}`, with `:140` `\norm{f}_{L^2(0,\infty;H^{-1/2})}<r_{\nu,S}`. ✅
* `:132` (G2, cited in the out-of-scope paragraph) = "Finally
  $\norm{f}_{\dot H^{1/2}}\le\norm{f}_{H^{1/2}}$ proves the stated inhomogeneous
  consequence." — the path-level comparison. ✅
* Numbering: section 4's numbered environments in order are `thm:Rmain`,
  `thm:Rinsert`, `prop:Rcritical1`, `prop:Rcritical2`, so "Propositions 4.3 and
  4.4" is right.
* **Improvement over lane 042:** `HalfOrder.lean:12` still cites the two
  propositions as `04-whole-space.tex:97,150`, which are now stale (`:97` is
  `\label{eq:Rcritical1}`, `:150` is a display line inside the 4.4 proof). The
  V2 contract silently corrects them.

**Consumer citations verified:**
* `research/R43/COMPARISON.md` §4 ("What upstream must add", heading at `:99`),
  row **G3** at `:109`: "`∀ f, MemForceR f → forceSobolevENormL1 (1/2) f ≠ ⊤`
  and `forceHomogeneousENorm 1 (1/2) f ≠ ⊤`". The V2 field is the first clause
  verbatim; the second is correctly declared out of scope. ✅
* `research/R44/COMPARISON.md` §4 ("Gap table", heading at `:135`), **S1** at
  `:145` ("proved, lane 042 `HalfOrder.lean:156`, at `m=0, s=-1/2, q=2`") and
  **G6** at `:171` ("register lane-042 `forceSobolevENorm_ne_top` into
  `DatumLemmas` V2 (+ a Bindings import of HalfOrder)"). Both served. ✅

### 3.1 The R44 instance really is derivable — scratch `example`, typechecked and deleted

Written to `verification/Tests/Scratch054Review.lean`, built, then removed
(worktree confirmed clean afterwards, `git status --short` empty):

```lean
import Contracts.V2.DatumLemmas
import Bindings.DatumLemmasV2
open BlowupDensity BlowupDensity.Contracts.V1.Data
open scoped ENNReal

example (A : Contracts.V2.DatumLemmas.DatumLemmasV2API)
    (f : SpaceTimeField) (hf : MemForceR f) :
    forceSobolevENormL2 (-1 / 2) f ≠ ⊤ :=
  A.forceSobolevENorm_ne_top f hf (-1 / 2) 0 (by norm_num) 2 (Or.inr rfl)

example (f : SpaceTimeField) (hf : MemForceR f) :
    forceSobolevENormL2 (-(1 / 2)) f ≠ ⊤ :=
  Bindings.datumLemmasV2.forceSobolevENorm_ne_top f hf (-(1 / 2)) 0 (by norm_num) 2 (Or.inr rfl)
```
```
✔ [9897/9897] Built Tests.Scratch054Review (2.4s)
Build completed successfully (9897 jobs).
```

Both compile. This settles two things at once: (a) R44's `m = 0`, `s = -1/2`,
`q = 2` ball is a genuine consequence of the *general* field, so R44 G6 needs no
fourth named field; (b) the `-1 / 2` vs `-(1 / 2)` spelling hazard that
`research/R44/COMPARISON.md:74,187` flags (`(-1/2 : ℝ) = -(1/2)` is **not** `rfl`)
costs nothing here, because the field quantifies over all real `s` and the side
condition `s ≤ ((0:ℕ):ℝ)` closes by `norm_num` in either spelling.

---

## 4. Scope string in `contracts.json`

New entry `D01.datum_lemmas_v2`, `version: 2`, spec
`verification/Contracts/V2/DatumLemmas.lean`, binding `Bindings.DatumLemmasV2`,
test `Tests.DatumLemmasV2`, declaration `BlowupDensity.Tests.checkedDatumLemmasV2`,
`enabled: true`. Every path and name resolves; `check_contracts.py` agrees.

The `scope` string is honest on both counts the briefing asks about:

* **homogeneous twin** — "Not asserted: the homogeneous half of G3
  (`forceHomogeneousENorm 1 (1/2) f` finite …), which needs a homogeneous datum
  for a general `H^∞` slice and is proved nowhere in the tree". Matches reality:
  `Homogeneous.exists_isHomogeneousSliceDatum` and
  `isHomogeneousSliceDatum_compact` are the only in-tree producers and both
  require Schwartz components or compact support.
* **G2 path-level comparison** — "… and its path-level domination by
  `forceSobolevENormL1 (1/2) f`", i.e. G2, explicitly excluded.
* **inherited V1 exclusions** — "and everything version 1 already lists as out of
  scope", which is accurate because `extends` inherits the V1 fields unchanged
  and adds no clause touching a V1 out-of-scope item.

It also states the positive content precisely (general `s ≤ m`, `q ∈ {1,2}`; the
two `1/2` instances; R44's ball as the `m = 0` case). No overclaim found.

---

## 5. Findings

### F1 — nit — module docstring, `Contracts/V2/DatumLemmas.lean:12-16`

**What is wrong.** The text says: "`Contracts.V1.DatumLemmas` … **Its module
docstring** records that `smoothJets_sobolevENorm_ne_top` is the **spatial**
slice finiteness only, and lists no clause bounding the *time-integrated*
Sobolev norm". The V1 *module* docstring
(`Contracts/V1/DatumLemmas.lean:5-90`) never mentions
`smoothJets_sobolevENorm_ne_top`; it is the *field* docstring at
`Contracts/V1/DatumLemmas.lean:163-168` that describes it as
`‖z‖_{H^s(R³)}` on a `SpatialField`. The V1 module docstring's out-of-scope list
(`:54-90`) likewise says nothing about the time-integrated norm — it covers norm
equivalence, time regularity, pressure data, `forceHomogeneousENorm`, the `L¹∩L²`
class, `F_rd`, and the Lemma A.1/B.1 estimates.

The *substance* is correct — `smoothJets_sobolevENorm_ne_top` is spatial-only and
V1 has no clause bounding `forceSobolevENorm` — only the attribution is off.

**Fix.** One word: "Its **field** docstring (`Contracts/V1/DatumLemmas.lean:163`)
records that …, and its module docstring's out-of-scope list names no clause
bounding the time-integrated Sobolev norm."

### F2 — nit — field docstring, `Contracts/V2/DatumLemmas.lean:111-113`

**What is wrong.** The `forceSobolevENorm_ne_top` doc comment cites
"`A03.lowerDatum` (`01-introduction.tex:105`, the inhomogeneous weight
monotonicity `(1+|ξ|²)^{s/2} ≤ (1+|ξ|²)^{m/2}` for `s ≤ m`)". Line 105 of
`paper/sections/01-introduction.tex` is the *homogeneous*-norm sentence ("The
homogeneous norm $\dot H^s$ replaces the weights above by $(2\pi|k|)^{2s}$ or
$|\xi|^{2s}$"); the inhomogeneous weight $(1+|\xi|^2)^{s/2}$ this field actually
relies on is defined at `01-introduction.tex:94-95`.

This citation is inherited from `HalfOrder.lean:22-23`, which cites the same
line but carries the caveat — *"the homogeneous norm replaces the weights", read
for the inhomogeneous weights* — that makes the pointer honest. V2 drops the
caveat while keeping the line number, so as it stands the parenthesis asserts
that `:105` states the inhomogeneous monotonicity, which it does not.

**Fix.** Cite `01-introduction.tex:94-95` (where $H^s(\R^3)$ and its weight are
defined), or restore lane 042's caveat.

### Non-findings, checked and clear

* `Data.lean:546` is cited for "finite `L¹_t` and `L²_t` Bochner norms"; the two
  `MemLp` conjuncts are at `:549-550` and `:546` is the `∀ m : ℕ, ∃ G` line that
  opens the datum-path clause. Same pointer `HalfOrder.lean:19` uses; reads as
  "the clause", not "the line". Not worth changing.
* `Data.lean:225 / 231 / 235 / 544` all land exactly on
  `forceSobolevENorm` / `forceSobolevENormL1` / `forceSobolevENormL2` /
  `MemForceR`. ✅
* `HalfOrder.lean:141 / 148` in the binding land exactly on the local
  `def forceSobolevENorm` / `abbrev forceSobolevENormL1`. ✅
* No V1 field removed, renamed, weakened or restated — `extends` plus the
  compiled `datumLemmas_of_v2 = datumLemmas := rfl` check make that structural.
* The three new fields are not placeholders: none is `True`, `∃ x, True`, or a
  hypothesis about an unnamed proposition, as the structure docstring promises.

---

## 6. Commands, verbatim

```
cd WT && bash scripts/lean-install.sh                                   → == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd WT/verification && lake build Contracts.V2.DatumLemmas Bindings.DatumLemmasV2 Tests.DatumLemmasV2
    → Build completed successfully (9898 jobs)
    → checkedDatumLemmasV2: checked; standard logical axioms only
cd WT && make check
    → check_formalization_plan --check ok; check_contracts ok;
      test_contract_policy: Ran 13 tests ... OK; check_work_queue: 30 work items ... consistent
cd WT && make test
    → 11 contracts, every one "checked; standard logical axioms only"
cd WT && make test-mutations
    → implementation_refactor accepted; admitted_proof / extra_axiom /
      weakened_hypothesis rejected as required; Mutation suite passed.
cd WT && python3 experiments/check_contracts.py --base-ref origin/erenup/integration
    → EXIT=0; "base_compatibility_checked": true; registered_contracts = 11
    → D01.datum_lemmas_v2 closure = 1134 modules, contains
      NSFormalization.Section4.D01.HalfOrder
cd WT && git diff origin/erenup/integration -- verification/Contracts/V1 \
          verification/Tests/DatumLemmas.lean verification/Bindings/DatumLemmas.lean
    → (empty)  — V1 byte-unchanged
grep -n "^import" verification/Contracts/V2/DatumLemmas.lean
    → 1:import Contracts.V1.DatumLemmas   (only import; Contracts.* only)
grep -n "maxHeartbeats" verification/Contracts/V2/DatumLemmas.lean \
       verification/Bindings/DatumLemmasV2.lean verification/Tests/DatumLemmasV2.lean
    → (none)
scratch: verification/Tests/Scratch054Review.lean
    → ✔ Built Tests.Scratch054Review — R44 (m=0, s=-1/2, q=2) instance derivable,
      both -1/2 spellings; V1-from-V2 projection defeq to the frozen witness
    → file and olean deleted; git status --short empty
```

No code was modified by this review. The only file written is this one.
