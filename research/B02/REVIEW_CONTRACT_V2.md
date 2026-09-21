# Review — lane 116 `B02.homogeneous_partial_v2` (`Contracts/V2/HomogeneousPartial.lean`)

Reviewer: opus reviewer, 2026-09-13.  Worktree
`.claude/worktrees/116-B02-homogeneous-v2`, branch `erenup/116-B02-homogeneous-v2`
at `9ce435b`, base `origin/erenup/integration` = `94bec50`.
Probes in `/tmp/rev116/`.  No file in the worktree was modified except this report.

## Verdict: **ACCEPT-WITH-NOTES**

The contract compiles, the axiom audit is the standard three, both new fields are
token-for-token the spec modulo the one intended, thrice-disclosed `-3/2 < s`
narrowing and pure namespace qualification of three definitionally identical
objects, the binding is lane 103's and lane 110's theorems *on the nose* (`rfl`
against the tree constants), the V1 half is the frozen V1 witness itself, the
statement is non-vacuous, and both recorded failures reproduce verbatim.

The notes are two documentation defects (F5, F6), neither mathematical, neither
blocking.  F5 (stale `Spec.lean` line citations, off by 11, inherited from the
frozen V1 file) is worth a one-line fix before merge because the V2 file freezes
too; F6 is cosmetic.

---

## 1. Compiles / policy — PASS

| command (from the worktree, after `. scripts/lean-env.sh`; lake from `verification/`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `lake build Tests.HomogeneousPartialV2` | EXIT=0, 9902 jobs |
| `make check` | EXIT=0 |
| `make test` | EXIT=0, **21/21** contracts |
| `make test-mutations` | EXIT=0, all four mutation outcomes as required |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | EXIT=0, 21 registered, `base_compatibility_checked: true` |

Tail evidence:

```
ℹ [9902/9902] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
Build completed successfully (9902 jobs).
```

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

`make test` prints `checked; standard logical axioms only` on exactly 21 lines
(`/tmp/rev116/make_test_full.log`), i.e. all registered contracts including the
new one and the untouched `Tests.HomogeneousPartial`.

`check_contracts.py --base-ref` output ends:

```
  "registered_contracts": 21,
  ...
  "base_compatibility_checked": true,
```

**Diff shape.**  `git diff origin/erenup/integration --stat` — 11 files, 656
insertions, 3 deletions.  No `Contracts/V1/*` file, no existing `Tests/*` file and
no existing `Bindings/*` file is touched; the only `Bindings/`+`Tests/` entries in
the diff are the two brand-new `*V2.lean` files:

```
$ git diff origin/erenup/integration --name-only | grep -E "Contracts/V1|Tests/|Bindings/"
verification/Bindings/HomogeneousPartialV2.lean
verification/Tests/HomogeneousPartialV2.lean
```

`verification/contracts.json` is **purely additive**: the diff is a single
appended object `B02.homogeneous_partial_v2` (11 `+` lines, 0 `-` lines).
`collaboration/` changes are the three expected generated ledger lines (one JSON
entry, one `TASKS.md` row, one `B02.md` line), all consistent with
`check_work_queue.py` ("30 work items: ownership, contract registration and task
cards consistent").

**Hygiene grep.**  `grep -nE '\bsorry\b|\badmit\b|\baxiom\b|native_decide|set_option|maxHeartbeats'`
over all six new files (`Contracts/V2/HomogeneousPartial.lean`,
`Bindings/HomogeneousPartialV2.lean`, `Tests/HomogeneousPartialV2.lean`,
`research/B02/axioms_contract_v2.lean`, `research/B02/probes/{v2_check,v2_test_examples}.lean`):
**zero hits in every file.**

**Warnings.**  Grepping every build log for the three new `verification/` paths
returns only the one expected `checkAxioms` `info:` line — the new files emit no
warning, which matters because `verification/Tests` is `warningAsError = true`.

## 2. Statement fidelity

### 2(a) Machine token-diff against `research/B02/Spec.lean` — PASS, one intended difference

`research/B02/Spec.lean` is byte-identical to base (`git diff origin/erenup/integration -- research/B02/Spec.lean` is empty), last touched by lane 110's `3e1f815`.

Method: field text extracted by line range, whitespace-normalized to one token per
line, `diff`'d.  Not by eye.

**`separatedAssembly`** — spec field body at `Spec.lean:593-601`, contract at
`Contracts/V2/HomogeneousPartial.lean:156-166`.  Complete diff (`<` spec, `>` V2),
101 tokens compared:

```
6c6,13
< ℝ)
---
> ℝ),
> -3
> /
> 2
> <
> s
> →
> ∀
80c87,93c96,101 (four occurrences)
< (separatedField                  > (BlowupDensity.Contracts.V1.BochnerPartial.separatedField
< (separatedPath                   > (BlowupDensity.Contracts.V1.BochnerPartial.separatedPath
```

That is the **whole** difference: (i) the intended insertion of `-3 / 2 < s →`
splitting `∀ (s : ℝ) (J : ℕ)` into `∀ (s : ℝ), -3 / 2 < s → ∀ (J : ℕ)`; (ii) the
two spec-local names `separatedField` / `separatedPath` written under their
`Contracts.V1.BochnerPartial` qualification.  Nothing else — the hypothesis list,
its order, the `(J : ℕ)` explicitness, `SpatialField`, `RealVectorSobolev s`,
`ContDiff ℝ ∞`, `HasCompactSupport`, `tsupport ⊆ Ioi 0`,
`IsHomogeneousSliceDatum`, `MemForceCompact`, `IsHomogeneousPath`,
`AEStronglyMeasurable … forceTimeMeasure` — is token-identical.

**`approxCompactHomogeneous`** — spec at `Spec.lean:618-619`, contract at
`:190-192`.  Complete diff:

```
19c19
< SplitRange
---
> BlowupDensity.Contracts.V1.HomogeneousPartial.SplitRange
```

One token, a namespace qualification.  `1 ≤ q`, `q ≠ ⊤`, `∀ s : ℝ`,
`CompletedDenseHomogeneous q s forceClassCompact` are identical.

**The qualification is not a substitution.**  The three qualified names are the
*same definitions*, checked two ways.  Source text:

| object | `Spec.lean` | contract's source |
|---|---|---|
| `separatedField` | `:211` `fun z => ∑ j, φ j z.1 • h j z.2` | `Contracts/V1/BochnerPartial.lean:79-81`, identical body |
| `separatedPath` | `:219` `fun t => ∑ j, φ j t • A j` | `Contracts/V1/BochnerPartial.lean:85-87`, identical body |
| `SplitRange` | `:237` `-3 / 2 < s ∧ s ≤ 0` | `Contracts/V1/HomogeneousPartial.lean:197`, identical body |

and kernel (`/tmp/rev116/probe.lean`, all three `rfl`s accepted):

```lean
example {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    Contracts.V1.BochnerPartial.separatedField φ h
      = NSFormalization.Section4.B01.separatedField φ h := rfl
example {J s} (φ) (A) :
    Contracts.V1.BochnerPartial.separatedPath φ A
      = NSFormalization.Section4.B01.separatedPath φ A := rfl
example (s : ℝ) : Contracts.V1.HomogeneousPartial.SplitRange s
      = NSFormalization.Section4.B02.SplitRange s := rfl
```

### 2(b) Against the manuscript — PASS, two deviations, both disclosed

Read-only; `paper/` untouched.  Verified line numbers:

* `04-whole-space.tex:218` `\begin{proposition}[…]\label{prop:Renergy}`
* `:219` "Fix $a\in\mathcal X_\R$ and $\nu,T>0$. Smooth compact forces **with $T^\nu_{\max,\R}(a,f)\le T$** are dense in each full Bochner space $L^q(0,\infty;H^s(\R^3))$ for $q\in\{1,2\}$ and $s<s_q$. **They are also dense in $L^2(0,\infty;\dot H^{-1}(\R^3))$.**"
* `:228` "The homogeneous norm here is a norm of the compact difference; the background itself need not belong to that homogeneous force space."
* `:251` "We next make the time and spatial compactness simultaneous. Write $X$ for any of the preceding separable Hilbert spaces **and $1\le q<\infty$**."
* `:260` "Thus the finite sum $\sum_j\varphi_j(t)h_j(x)$ approximates $b$ and is jointly smooth with compact support strictly inside $\R^3\times(0,\infty)$."

**Is `approxCompactHomogeneous` exactly the homogeneous density statement of
Prop 4.6?**  It is that statement with two deviations, both stated in the module
docstring and in the `contracts.json` scope:

1. **Weaker in one respect, disclosed**: the manuscript's homogeneous clause says
   smooth compact forces *with $T^\nu_{\max,\R}(a,f)\le T$*.  The field drops the
   breakdown condition, asserting density of `forceClassCompact` plain.  This is
   the deliberate B02/R46 split — the contract docstring (`:170-172`) and the scope
   string both say so ("stripped of the breakdown condition … which `R46` supplies
   from `R41D` by the two-radius argument of `04-whole-space.tex:262`"), it is what
   `research/section4/STATEMENTS.md:831-836` asks B02 for, and V1 already framed
   B02 this way.  The scope string closes with "Nothing here asserts the
   singular-force threshold `s < s_q`, the breakdown condition
   `T^nu_max,R(a,f) <= T`, or any PDE norm estimate."  Honest.
2. **Stronger in two respects**: the manuscript's homogeneous clause is the single
   case $q=2$, $s=-1$; the field is `∀ q ∈ [1,∞), ∀ s ∈ SplitRange`.  A
   generalization of a *conclusion* cannot lose the paper's claim, and the paper's
   case is recovered: `SplitRange (-1)` holds and `Tests/HomogeneousPartialV2.lean:44-51`
   instantiates the field at `q = 2`, `s = -1` and gets the manuscript shape.

**Is the `q ≠ ⊤` / `SplitRange` restriction the paper's?**

* `1 ≤ q`, `q ≠ ⊤` — **yes, verbatim the paper's**: `:251` says "$1\le q<\infty$"
  for exactly this Bochner step.
* `SplitRange s = -3/2 < s ∧ s ≤ 0` — **not literally in the paper**, but a
  faithful reading of the paper's own homogeneous argument, and it is *inherited
  frozen from V1* (`Contracts/V1/HomogeneousPartial.lean:194-197`, whose docstring
  already cites `04-whole-space.tex:241,246,249`), not invented by this lane.  The
  two halves are exactly the two places the manuscript's low/high split
  eq:Rnegative-cutoff (`:242-248`) constrains the order: `-3/2 < s` is finiteness
  of $\int_{|\xi|<1}|\xi|^{2s}\dd\xi$ in dimension three (the paper writes "The
  integral at the origin is finite in dimension three" for its $s=-1$), and
  $s\le0$ is the high-frequency bound $\int_{|\xi|\ge1}|\xi|^{2s}|\hat k|^2\le\|k\|_2^2$.
  The manuscript's only case, $s=-1$, lies strictly inside.  No objection.

**Is `-3/2 < s` for `separatedAssembly` weaker than what the paper's
separated-sum step needs?**  **No.**  The paper's separated-sum step (`:251-260`)
is realization-independent — "Write $X$ for any of the preceding separable Hilbert
spaces" — so relative to the paper's *generality* `-3/2 < s` is a real narrowing,
and relative to the spec's `∀ (s : ℝ)` it is a real weakening.  But relative to
what the paper *needs* it costs nothing: the homogeneous application is $s=-1$
only, and $-3/2<-1$.  The lane's claim that the sole in-repo consumer feeds it
exactly `SplitRange.1` is **verified in the tree**, not just asserted —
`formalization/NSFormalization/Section4/B02/ApproxCompact.lean:204`:

```lean
  have hasm := separatedAssembly s hs.1 φ h H hφs hφc hφpos hhs hhc hHdatum
```

with `hs : SplitRange s` at `:143`.  So `SplitRange.1 = -3/2 < s` is literally the
only thing supplied, and the narrowing is invisible downstream.

The narrowing is disclosed in four independent places, each with the reason
(D01's `homogeneousVectorDatum` is finite only at $s>-3/2$) and the pointer to
lane 110's finding 5-A: the module docstring `:52-60`, the field docstring
`:146-155`, the `contracts.json` scope ("CAVEAT: registered with the honest
hypothesis -3/2 < s, NOT the spec's stated forall (s : R) and NOT the narrower
SplitRange s"), and `ATTEMPTS_CONTRACT_V2.md` decision 1.  `research/B02/Spec.lean:583-592`
itself already recommends precisely this.  This is the fidelity rule working as
intended: a weaker hypothesis loudly labelled rather than a false `∀ s`.

### 2(c) Non-vacuity — PASS

All checks in `/tmp/rev116/probe.lean` and `/tmp/rev116/probe2.lean`, accepted by
the kernel, in contract vocabulary.

**The V2 API is a closed value, no hypotheses.**

```
$ lake env lean /tmp/rev116/probe.lean
Bindings.homogeneousPartialV2 : Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API
Bindings.homogeneousPartial_of_v2 : Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI
```

`#check @…` prints no argument telescope at all: unlike `InsertionLifespanV2`
(which is conditional on an `InsertionFamilyAPI`), this contract is inhabited
unconditionally.

**`SplitRange` is inhabited** (so the outer `∀ s, SplitRange s → …` is not vacuous):

```lean
example : Contracts.V1.HomogeneousPartial.SplitRange (-1 : ℝ) := ⟨by norm_num, by norm_num⟩   -- ✓
```

**`forceClassCompact` is nonempty** (so `∃ f ∈ S, …` is not an unsatisfiable demand):

```lean
example : (0 : SpaceTimeField) ∈ forceClassCompact :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩                                 -- ✓
example : forceClassCompact.Nonempty := ⟨0, contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩  -- ✓
```

**The antecedent `MemBochnerDatum` is inhabited** — the check that actually rules
out vacuous truth here, since `CompletedDenseVia` (`Contracts/V1/Data.lean:732-742`)
opens with `∀ b, MemBochnerDatum q s b → …`, and an empty target class would make
the whole field trivially true:

```lean
example : MemBochnerDatum 2 (-1 : ℝ) 0 := MemLp.zero                                           -- ✓
```

So the field is a genuine `∀`/`∃` statement over a nonempty domain with a nonempty
witness class.  (Lane 110's reviewer checked the analogous points in the tree; this
re-does them in the `Contracts.V1.Data` vocabulary the contract actually uses.)

Additionally, no field of either new clause is `True`, `∃ x, True`, or a hypothesis
about an unspecified `Prop` — inspected directly; both are concrete.

### 2(d) The bound fields really are lanes 103's and 110's theorems — PASS

`#print`-level identity, not just type-compatibility.  All four `rfl`s accepted
(`/tmp/rev116/probe.lean`):

```lean
example : Bindings.homogeneousPartialV2.approxCompactHomogeneous
    = fun q hq1 hqt s hs =>
        NSFormalization.Section4.B02.approxCompactHomogeneous q hq1 hqt s hs := rfl      -- ✓
example : @Bindings.homogeneousPartialV2.separatedAssembly
    = fun s hs _J φ h A hφs hφc hφpos hhs hhc hA =>
        NSFormalization.Section4.B02.separatedAssembly s hs φ h A hφs hφc hφpos hhs hhc hA := rfl  -- ✓
example : Bindings.homogeneousPartial_of_v2 = Bindings.homogeneousPartial := rfl          -- ✓
example : Bindings.homogeneousPartialV2.toHomogeneousApproxPartialAPI
    = Bindings.homogeneousPartial := rfl                                                   -- ✓
```

The last two are the important ones for "no V1 field re-proved or weakened": the
V1 projection of the V2 witness is not merely *a* `HomogeneousApproxPartialAPI`,
it is **definitionally the frozen `Bindings.homogeneousPartial` itself**.  The
`{ homogeneousPartial with … }` in `Bindings/HomogeneousPartialV2.lean:96` is
therefore a genuine extension, not a rebuild.

Transitive axioms of the new binding, both the record and the projection:

```
'BlowupDensity.Bindings.homogeneousPartialV2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.homogeneousPartial_of_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the two tree theorems themselves, re-audited (`research/B02/axioms_contract_v2.lean`, EXIT=0):

```
'NSFormalization.Section4.B02.separatedAssembly' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.approxCompactHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lane 110's defeq check still holds on this base — `lake env lean
../research/B02/axioms_approx_compact.lean`, EXIT=0, five declarations all
`[propext, Classical.choice, Quot.sound]`.

The tree theorem's `{J : ℕ}` is implicit while the contract field's `(J : ℕ)` is
explicit; the binding's `_J` absorbs it and the `rfl` above proves the absorption
is defeq, not a reshuffle.  Likewise the tree's `h : Fin J → Space → Space` vs the
contract's `h : Fin J → SpatialField`.

## 3. Consistency — PASS

**Import policy.**  `Contracts/V2/HomogeneousPartial.lean` has exactly one import:

```
imports of verification/Contracts/V2/HomogeneousPartial.lean = ['Contracts.V1.HomogeneousPartial']
policy violations: none
```

Within `Mathlib` / `Lean` / `Init` / `Contracts.*`, no upstream import, no
whitelist widening, no policy change.  `experiments/test_contract_policy.py`: 13
tests OK.  (The `open NavierStokes.ProblemStatement (Space)` /
`open NSFormalization.Paper3 (RealVectorSobolev)` lines resolve through
`Contracts.V1.Data`'s already-sanctioned imports, exactly as V1 does.)

**No restated definition without a bridge.**  The lane's claim that the file
restates nothing is **correct**: every identifier in the two new field types comes
from `Contracts.V1.Data` (`SpatialField`, `IsHomogeneousSliceDatum`,
`IsHomogeneousPath`, `MemForceCompact`, `forceTimeMeasure`, `forceClassCompact`,
`CompletedDenseHomogeneous`), `Contracts.V1.BochnerPartial`
(`separatedField`, `separatedPath`) or `Contracts.V1.HomogeneousPartial`
(`SplitRange`).  No `def`, `abbrev` or `structure` is declared in the file — only
the one `structure HomogeneousApproxPartialV2API`, which is the contract itself.
So no new `rfl` bridge is owed.

**The three bridges are duplicates — and the lane says so.**  All three re-recorded
bridges already exist:

| re-recorded in `Bindings/HomogeneousPartialV2.lean` | original |
|---|---|
| `homogeneousPartialV2_separatedField_eq` (`:74`) | `bochnerPartial_separatedField_eq`, `Bindings/BochnerPartial.lean:47-49` |
| `homogeneousPartialV2_separatedPath_eq` (`:80`) | `bochnerPartial_separatedPath_eq`, `Bindings/BochnerPartial.lean:52-54` |
| `homogeneousPartialV2_splitRange_eq` (`:86`) | `homogeneousPartial_splitRange_eq`, `Bindings/HomogeneousPartial.lean:97-99` |

This is fine (harmless, self-documenting), and it **is** stated, in three places:
the contract module docstring `:99-104`, the binding module docstring `:26-30` and
`:37-43,:49-50` (each citing the original by file and line), and
`ATTEMPTS_CONTRACT_V2.md` decision 4 ("The relevant `rfl` bridges already live in
`Bindings/BochnerPartial.lean:47-54` and `Bindings/HomogeneousPartial.lean:97-99`;
I re-recorded three of them … for self-documentation").  Requirement met.

**Conventions vs `Contracts/V2/{MaximalPartial,InsertionLifespan}.lean`.**  Match:
single `import Contracts.V1.X` (plus `Contracts.V2.MaximalPartial` where
`InsertionLifespan` needs it), `noncomputable section`,
`namespace BlowupDensity.Contracts.V2.X`, `structure XV2API extends …`, the shared
sentence "No version-one field is removed, weakened, renamed or restated; `extends`
makes that structural", the `…_of_v2` V1-recovery declaration in the binding, and
`Tests/XV2.lean` = `import Contracts.V2.X` + `import Bindings.XV2` +
`import TestSupport.Axioms`, `checkedXV2`, `run_cmd TestSupport.checkAxioms`.
The one divergence is correct and explained: `homogeneousPartialV2` /
`checkedHomogeneousPartialV2` are `def`s where `maximalPartialV2` is a `theorem`,
because `HomogeneousApproxPartialV2API` inherits the data field `χ` and so lives in
`Type`, not `Prop` — matching V1's own `def homogeneousPartial`
(`Bindings/HomogeneousPartial.lean:105`) and `def checkedHomogeneousPartial`
(`Tests/HomogeneousPartial.lean:11`).  `ATTEMPTS` decision 6 records this.
Also correct: unlike `MaximalPartialV2`, this binding needs **no** `Iff` transport,
because nothing here is a re-declared `structure` (decision 5) — confirmed by the
direct-assignment `rfl`s in §2(d).

**The `scope` string.**  It states what is asserted and what is not, and it is
accurate on every point I checked:

* the `-3/2 < s` restriction — present, flagged `CAVEAT:`, with the reason, the
  "NOT the spec's stated forall (s : R) and NOT the narrower SplitRange s"
  disambiguation, and the no-consumer-weakened justification;
* `SplitRange` — spelled out inline as `(-3/2 < s and s <= 0)`, with `q=2, s=-1`
  named as R46's instance;
* the excluded `annularPathApprox` — present, with all four reasons (no proof
  exists, off the manuscript's chain, feeds nothing, not routed through), matching
  the module docstring `:80-91`;
* comparison with the V1 exclusion list (`Contracts/V1/HomogeneousPartial.lean:75-100`):
  V1 excluded three obligations — `separatedAssembly`, `annularPathApprox`,
  `approxCompactHomogeneous`.  V2 registers the first and third, keeps the second
  excluded with V1's own wording, and **carries forward** V1's other two
  exclusions verbatim ("as in version 1, forceClassCompact subset forceClassR and
  the datum-path/Bochner-space identification stay with B01").  Nothing V1 excluded
  is silently picked up, nothing V1 asserted is dropped.

## 4. Honesty of `ATTEMPTS_CONTRACT_V2.md` — PASS (both failures reproduce verbatim)

**N1 — `ENNReal.two_ne_top`.**  Reconstructed by reverting `by simp` to
`ENNReal.two_ne_top` at the two sites (`/tmp/rev116/N1_two_ne_top.lean`):

```
$ lake env lean /tmp/rev116/N1_two_ne_top.lean
/tmp/rev116/N1_two_ne_top.lean:17:28: error(lean.unknownIdentifier): Unknown constant `ENNReal.two_ne_top`
/tmp/rev116/N1_two_ne_top.lean:27:68: error(lean.unknownIdentifier): Unknown constant `ENNReal.two_ne_top`
```

Character-for-character the text pasted in `ATTEMPTS_CONTRACT_V2.md`, including
both line:column pairs `17:28` and `27:68`.  The recorded fix (`by simp`) is what
the committed file uses and it is green.

**N2 — missing `open BlowupDensity`.**  Reconstructed by deleting the
`open BlowupDensity` line from the conformance file (`/tmp/rev116/N2_no_open.lean`):

```
$ lake env lean /tmp/rev116/N2_no_open.lean
/tmp/rev116/N2_no_open.lean:38:10: error(lean.unknownIdentifier): Unknown identifier `Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API`
/tmp/rev116/N2_no_open.lean:42:10: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI`
/tmp/rev116/N2_no_open.lean:53:21: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.BochnerPartial.separatedField`
/tmp/rev116/N2_no_open.lean:54:27: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.BochnerPartial.separatedField`
/tmp/rev116/N2_no_open.lean:55:9: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.BochnerPartial.separatedPath`
/tmp/rev116/N2_no_open.lean:57:9: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.BochnerPartial.separatedPath`
/tmp/rev116/N2_no_open.lean:63:4: error(lean.unknownIdentifier): Unknown identifier `Contracts.V1.HomogeneousPartial.SplitRange`
```

The three lines quoted in `ATTEMPTS` — `38:10`, `53:21`, `63:4` — reproduce
exactly, same identifiers, same columns.  See F6 for the nit.

The committed files are green as recorded: `axioms_contract_v2.lean` EXIT=0 with
all four `#print axioms` standard; `probes/v2_check.lean` and
`probes/v2_test_examples.lean` both EXIT=0 with the expected output.

**Git history — confirmed clean, the `--ff-only` created no merge commit.**

```
$ git log --oneline origin/erenup/integration..HEAD
9ce435b [116-B02] HomogeneousPartial V2 contract: …
$ git rev-list --count origin/erenup/integration..HEAD
1
$ git log --merges --oneline origin/erenup/integration..HEAD
(empty)
$ git rev-parse HEAD~1 origin/erenup/integration
94bec50c74dd25e3870166bba304b90ca3459c96
94bec50c74dd25e3870166bba304b90ca3459c96
```

Exactly one commit, no merge commit anywhere in the range, and `HEAD~1` is
bit-identical to `origin/erenup/integration`.  The `git merge --ff-only` was a true
fast-forward, as the ATTEMPTS "Environment note" describes; the base-compatibility
gate consequently reports `base_compatibility_checked: true` against the current
base, which was the point of the sync.

---

## Findings

| # | Severity | Finding |
|---|---|---|
| F1 | — | **Gates all green.**  `lake build Tests.HomogeneousPartialV2` EXIT=0 "checked; standard logical axioms only"; `make check` EXIT=0; `make test` EXIT=0 with 21/21 contracts; `make test-mutations` EXIT=0 with all four outcomes as required; `check_contracts.py --base-ref origin/erenup/integration` EXIT=0, 21 registered, `base_compatibility_checked: true`.  No `sorry`/`admit`/`axiom`/`native_decide`/`set_option`/`maxHeartbeats` in any of the six new files.  No V1 contract, test or binding touched; `contracts.json` purely additive.  No warnings on the new files. |
| F2 | — | **Statement fidelity holds.**  Machine token-diff against `Spec.lean:593-601` and `:618-619` shows exactly the one intended difference (`-3 / 2 < s →`) plus namespace qualification of three objects whose definitions are textually identical *and* `rfl`-equal.  The manuscript comparison holds: `1 ≤ q < ∞` is the paper's own (`:251`); `SplitRange` is V1's frozen, well-cited reading of eq:Rnegative-cutoff containing the paper's $s=-1$; the only weakening (dropping `T^ν_{max,R}(a,f) ≤ T`) is the deliberate B02/R46 split, disclosed in the docstring and the scope. |
| F3 | — | **Binding is the tree's theorems on the nose, V1 half untouched.**  Four `rfl`s accepted, including `homogeneousPartial_of_v2 = Bindings.homogeneousPartial` and `homogeneousPartialV2.toHomogeneousApproxPartialAPI = Bindings.homogeneousPartial` — the V1 projection is definitionally the *frozen witness itself*, so no V1 field was re-proved or weakened.  Transitive axioms standard for all four relevant declarations.  Non-vacuity confirmed in contract vocabulary: the API is a closed value with no hypotheses; `SplitRange (-1)`, `forceClassCompact.Nonempty` and `MemBochnerDatum 2 (-1) 0` are all inhabited. |
| F4 | — | **ATTEMPTS is honest.**  Both recorded failures reproduce character-for-character at the recorded line:column.  Git history confirms one commit on top of `origin/erenup/integration`, no merge commit. |
| **F5** | **low (documentation)** | **Stale `Spec.lean` line citations, off by 11.**  The contract cites `separatedAssembly` at `research/B02/Spec.lean:582` and `approxCompactHomogeneous` at `:607`; the fields are actually at `:593` and `:618`.  Line 582 is a blank line inside a docstring and 607 is the prose "`R41D` by the two-radius argument of `04-whole-space.tex:262`".  Cause: lane 110's own commit `3e1f815` inserted the 11-line ⚠ paragraph at `Spec.lean:582-592`, shifting everything below.  The numbers were inherited unchanged from V1's frozen exclusion list (`Contracts/V1/HomogeneousPartial.lean:82,100`), so this lane propagated rather than introduced the drift — but it now appears **25 times** across the lane's files (counted by grep): 11 in `Contracts/V2/HomogeneousPartial.lean`, 5 in the `contracts.json` scope string, 3 in `axioms_contract_v2.lean`, 6 in `ATTEMPTS_CONTRACT_V2.md`.  Mathematically harmless — every one is accompanied by the field *name*, and §2(a) confirms the intended fields — but the V2 file freezes on merge, so the cheapest moment to fix is now.  Suggested (lead's call, docstring-only, no Lean change, does not invalidate any gate): `582` → `593` and `607` → `618` in `Contracts/V2/HomogeneousPartial.lean`, `contracts.json` and `axioms_contract_v2.lean`.  Alternatively leave them for consistency with the frozen V1 file and log the drift in `logs/LESSONS.md` (line-number citations into a file that is still being edited go stale). |
| **F6** | **trivial (cosmetic)** | **N2's pasted error block is a 3-of-7 excerpt, presented without an ellipsis.**  Removing `open BlowupDensity` produces seven `unknownIdentifier` errors; `ATTEMPTS_CONTRACT_V2.md` quotes three (`38:10`, `53:21`, `63:4`) with no "…" marking the elision.  The three quoted are verbatim correct and the diagnosis is right, so nothing is misleading about the *conclusion*; strictly, "pasted error text" should be the whole output or marked as trimmed. |

## Recommendation

**Merge.**  F5 is worth the two-minute docstring fix before merge since the V2
contract freezes; F6 needs nothing.  Neither affects the Lean, the gates, the
axiom audit, or the mathematics.

## Commands run

```
. scripts/lean-env.sh              # every shell; lake from verification/, LEAN_NUM_THREADS=6
lake build Tests.HomogeneousPartialV2                                   # EXIT=0, 9902 jobs
make check                                                              # EXIT=0
make test                                                               # EXIT=0, 21/21 "standard logical axioms only"
make test-mutations                                                     # EXIT=0, 4/4 outcomes as required
python3 experiments/check_contracts.py --base-ref origin/erenup/integration  # EXIT=0, 21, base_compatibility_checked: true
python3 experiments/test_contract_policy.py                             # 13 tests OK
git diff origin/erenup/integration --stat / --name-only / -- verification/contracts.json / -- collaboration/
git log --oneline / --merges / rev-list --count / rev-parse   origin/erenup/integration..HEAD
lake env lean ../research/B02/axioms_contract_v2.lean                   # EXIT=0, 4 decls standard
lake env lean ../research/B02/axioms_approx_compact.lean                # EXIT=0, lane 110 defeq still holds
lake env lean ../research/B02/probes/v2_check.lean                      # EXIT=0
lake env lean ../research/B02/probes/v2_test_examples.lean              # EXIT=0
lake env lean /tmp/rev116/probe.lean                                    # #check closed value; 7 rfl/vacuity examples; #print axioms
lake env lean /tmp/rev116/probe2.lean                                   # forceClassCompact nonempty, 3 examples, EXIT=0
lake env lean /tmp/rev116/N1_two_ne_top.lean                            # N1 reproduced verbatim
lake env lean /tmp/rev116/N2_no_open.lean                               # N2 reproduced verbatim
# token diffs: field text normalized one-token-per-line, diff'd (not by eye)
```
