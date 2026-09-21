# Review — lane 110-B02-approx-compact (`approxCompactHomogeneous`)

Reviewer: opus, 2026-09-13.  Worktree `.claude/worktrees/110-B02-approx-compact`,
branch `erenup/110-B02-approx-compact`, HEAD `925bade`, working tree clean.
Diff vs base: 4 files, +433/-1 — `formalization/NSFormalization/Section4/B02/ApproxCompact.lean` (new, 224 ln),
`research/B02/{ATTEMPTS_APPROX_COMPACT.md, axioms_approx_compact.lean}` (new),
`research/B02/REMAINING_SPLIT.md` (row 8 → DONE).  Probes in `/tmp/rev110/`.

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics and the Lean are correct, clean, non-vacuous and faithful to the
manuscript; every gate is green.  All notes are documentation / claim-accuracy
issues plus two pre-existing ledger items the lead must settle before a V2
contract.  Nothing blocks the merge.

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh && cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.B02.ApproxCompact
Build completed successfully (9892 jobs).              # EXIT=0
   (the only warnings replayed are pre-existing, from Paper3/*; none from the new module)

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/B02/ApproxCompact.lean
                                                        # EXIT=0, 0 bytes of output — silent

$ LEAN_NUM_THREADS=6 lake env lean ../research/B02/axioms_approx_compact.lean   # EXIT=0
'NSFormalization.Section4.B02.eLpNorm_smul_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.bochnerDatumENorm_separatedPath_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.SeparatedCompactHomogeneousDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.separatedCompactHomogeneousDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.B02.approxCompactHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both conformance `example`s in `axioms_approx_compact.lean` typecheck (no error
emitted for either).  All 5 public declarations are exactly the three standard axioms.

```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/B02/ApproxCompact.lean
50:`research/B02/axioms_approx_compact.lean` discharges the spec field type through
```
Single hit, a docstring word.  No `sorry`/`admit`/`axiom`/`native_decide`, **no
`set_option` and no `maxHeartbeats` bump** — notable given finding 4.1 below.

```
$ make check      # EXIT=0 ... 13 tests OK; "30 work items: ownership, contract
                  #            registration and task cards consistent."
$ make test       # EXIT=0 ... every registered contract "checked; standard logical axioms only"
```
(`make test` does not touch the new module — it is not yet in a registered
contract closure — but it confirms the lane broke nothing.)

---

## 2. Statement fidelity — PASS, with two documentation notes

### 2.1 `#check` of every export (probe `/tmp/rev110/fidelity.lean`)

```
NSFormalization.Section4.B02.approxCompactHomogeneous : ∀ (q : ℝ≥0∞),
  1 ≤ q → q ≠ ∞ → ∀ (s : ℝ), NSFormalization.Section4.B02.SplitRange s →
    NSFormalization.Section4.B01.CompletedDenseVia q s
      (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s)
      NSFormalization.Section4.B01.forceClassCompact

@NSFormalization.Section4.B02.bochnerDatumENorm_separatedPath_sub_le : ∀ {q : ℝ≥0∞},
  1 ≤ q → ∀ {s : ℝ} {J : ℕ} (φ : Fin J → ℝ → ℝ) (A A' : Fin J → RealVectorSobolev s),
    (∀ (j : Fin J), AEStronglyMeasurable (φ j) NSFormalization.Section4.D01.forceTimeMeasure) →
      NSFormalization.Section4.B01.bochnerDatumENorm q s
          (…separatedPath φ A - …separatedPath φ A') ≤
        ∑ j, eLpNorm (φ j) q …forceTimeMeasure * ‖A j - A' j‖ₑ

@NSFormalization.Section4.B02.eLpNorm_smul_const : ∀ {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → ℝ) (v : E) {q : ℝ≥0∞} {μ : Measure ℝ},
  eLpNorm (fun t => f t • v) q μ = eLpNorm f q μ * ‖v‖ₑ

NSFormalization.Section4.B02.SeparatedCompactHomogeneousDense : ℝ≥0∞ → ℝ → Prop
NSFormalization.Section4.B02.separatedCompactHomogeneousDense : ∀ (q : ℝ≥0∞),
  1 ≤ q → q ≠ ∞ → ∀ (s : ℝ), …SplitRange s → …SeparatedCompactHomogeneousDense q s
```

`eLpNorm_smul_const` is indeed quantified over **every** `q : ℝ≥0∞`, `⊤` included,
and over an arbitrary real normed space `E` — as claimed.

### 2.2 Token-identity with `Spec.lean:607` — **not literal**, but defeq at `rfl`

Machine diff of the two pretty-printed type strings (not by eye):

```
$ diff <(tr ' ' '\n' < spec_type.txt) <(tr ' ' '\n' < lane_type.txt)
17c17
< SplitRange                              > NSFormalization.Section4.B02.SplitRange
20c20
< CompletedDenseHomogeneous               > NSFormalization.Section4.B01.CompletedDenseVia
23c23,25
< forceClassCompact                       > (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s)
                                          > NSFormalization.Section4.B01.forceClassCompact
```

Three token differences.  They are all benign — `CompletedDenseHomogeneous` is an
`abbrev` for `CompletedDenseVia q s (IsHomogeneousPath s)` (`Data.lean:752`), and
`SplitRange` / `forceClassCompact` are the sanctioned `formalization/`
restatements — and definitional equality is confirmed **by the kernel**, which is
stronger than the elaboration-unification the conformance file relies on:

```lean
-- /tmp/rev110/fidelity.lean, accepted (EXIT: no error on this line)
example : specApproxCompactHomogeneous = laneApproxCompactHomogeneous := rfl
```

> **Finding 2-A (severity: low, documentation).**  `REMAINING_SPLIT.md` row 8 and
> `ATTEMPTS_APPROX_COMPACT.md` say the theorem is "**token-identical** to
> `Spec.lean:607`".  It is not, literally: see the diff above.  The correct claim is
> "defeq to `Spec.lean:607`, `rfl`-checked, modulo the `CompletedDenseHomogeneous`
> `abbrev` and the two documented restatements".  Contrast lane 097's
> `temporalApprox`, which really *is* character-for-character identical to
> `Contracts/V1/BochnerPartial.lean:132-138`; using the same phrase for both blurs a
> distinction the repo relies on.  Fix the two words, not the Lean.

### 2.3 Hypotheses of the gluing estimate — nothing hidden, but not "only `1 ≤ q`"

The `#check` above is the full type: the hypotheses are `1 ≤ q` **and**
`∀ j, AEStronglyMeasurable (φ j) forceTimeMeasure`.  There is no `q ≠ ⊤`, no
`MemBochnerDatum`, no homogeneity, no `SplitRange`, no side condition on `A`/`A'`
— so the lemma is genuinely realization-independent, as the docstring says.

> **Finding 2-B (severity: informational).**  The lane's one-line summary (and the
> review brief) say the estimate holds "under only `1 ≤ q`".  The measurability
> hypothesis on each `φ j` is real (it is what `eLpNorm_sum_le` consumes); it is
> free at the call site (`(hφs j).continuous.aestronglyMeasurable`, line 173).
> `ATTEMPTS_APPROX_COMPACT.md` states it correctly; only the summary is loose.

### 2.4 Against the manuscript — the paper's inequality, stated more generally

The Lean estimate is

  `‖Σ_j φ_j·(A_j − A'_j)‖_{L^q(0,∞;X)} ≤ Σ_j ‖φ_j‖_{L^q} · ‖A_j − A'_j‖_X`

(triangle inequality over `j`, plus the **equality** `eLpNorm_smul_const` on each
term — so no slack is introduced beyond the triangle step the paper itself takes).

Read-only comparison with `paper/sections/04-whole-space.tex` (no edit):

* line **254**: `\sum_{j=1}^J |E_j|^{1/q}\norm{b_j-h_j}_X` — fixed time factors
  `1_{E_j}`, differing spatial vectors.  Since `‖1_{E_j}‖_{L^q} = |E_j|^{1/q}`,
  **this is exactly the Lean shape** with `φ_j := 1_{E_j}`, and it is exactly how
  the Lean lemma is used at `ApproxCompact.lean:171-181` (replace `A'_j` by `H_j`).
* line **258**: `\sum_{j=1}^J\norm{\mathbf1_{E_j}-\varphi_j}_{L^q}\norm{h_j}_X` —
  *differing* time factors, fixed spatial vectors.  A different shape; it belongs
  to the temporal stage, which is already inside `temporalApprox` (lane 097).

So the Lean inequality is **the paper's, neither weaker nor stronger** — and
strictly more general in that `A`, `A'` are arbitrary rather than the one pair the
proof uses.

> **Finding 2-C (severity: low, documentation).**  The citation
> `04-whole-space.tex:257` (module docstring lines 28, 69, 85; repeated in
> `ATTEMPTS_APPROX_COMPACT.md` and `REMAINING_SPLIT.md` row 8 / the lane-103
> follow-up note) points at the wrong display.  `:257` is the `\[` that opens the
> display whose content is line **258**, the `‖1_E − φ‖·‖h‖` estimate.  The correct
> pointer for this lemma is `04-whole-space.tex:253-255` (content on line **254**).
> The error is inherited from the lane-103 recipe at the bottom of
> `REMAINING_SPLIT.md`, so it is not this lane's invention, but it is now in a
> merged Lean docstring and should be corrected there.

### 2.5 `q ≠ ⊤` exclusion — matches spec and paper

`04-whole-space.tex:251` runs the Bochner argument for "`1\le q<\infty`", and the
homogeneous clause of `:219` is asserted at `q = 2`.  The Lean `1 ≤ q ∧ q ≠ ⊤` is
literally `1 ≤ q < ∞`, and covers `q = 2`.  Matches `Spec.lean:607` word for word.
Likewise `SplitRange s = -3/2 < s ∧ s ≤ 0` covers the manuscript's only case
`s = -1`.  Both are generalizations of what the paper claims, not restrictions.

### 2.6 Non-vacuity — PASS, four independent checks

All machine-checked (`/tmp/rev110/fidelity{,2,3}.lean`, EXIT=0):

```lean
example : SplitRangeSpec (-1) := by constructor <;> norm_num          -- ✓ SplitRange satisfiable
example : NSFormalization.Section4.B02.SplitRange (-1) := …           -- ✓ same for the local one

example : forceTimeMeasure ≠ 0 := …                                   -- ✓ the measure is not zero,
  -- so bochnerDatumENorm is not identically 0 and "< η" is not free

example : Set.Nonempty forceClassCompact :=                           -- ✓ F_c is inhabited
  ⟨0, contDiff_const, HasCompactSupport.intro isCompact_empty …, …⟩

example (s : ℝ) (A : RealVectorSobolev s) :                           -- ✓ the ∀ b quantifier is not
    MemBochnerDatum 2 s (Set.indicator (Ioo (1:ℝ) 2) (fun _ => A)) := …   -- vacuous: nonzero targets exist
```

`forceClassCompact` is `{f | MemForceCompact f}` = smooth + `HasCompactSupport` +
`tsupport ⊆ positiveTimeDomain`; the *proof itself* produces non-trivial members
(`separatedField φ h` with `h_j ∈ C_c^∞` from `spatialApproxHomogeneous`), so the
conclusion is not satisfied merely by `0`.  `CompletedDenseHomogeneous` is
therefore not trivially true.

---

## 3. Consistency — PASS

### 3.1 `eLpNorm_smul_const` is not a Mathlib duplicate

Mathlib has only `MeasureTheory.eLpNorm_const_smul` (`LpSeminorm/SMul.lean:110`):
a scalar **constant** times a function of the *same* codomain.  The lane's lemma is
the different shape — a scalar **function** times a constant **vector**, which
changes the codomain from `ℝ` to `E`.  Searched and asked the library:

```
$ grep -rn 'eLpNorm.*smul_const\|smul_const.*eLpNorm' verification/.lake/packages/mathlib/Mathlib/
(no matches)

-- /tmp/rev110/attempt4.lean
example {E} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → ℝ) (v : E) {q μ} :
    eLpNorm (fun t => f t • v) q μ = eLpNorm f q μ * ‖v‖ₑ := by exact?
Try this: exact NSFormalization.Section4.B02.eLpNorm_smul_const f v
```
`exact?` finds nothing but the lane's own lemma.  Genuinely new; correctly placed.

### 3.2 No duplication anywhere in `formalization/`

```
$ grep -rn 'eLpNorm_smul_const' formalization/ verification/ research/
(only ApproxCompact.lean and its own ATTEMPTS/axioms files)
```

### 3.3 No overlap with `B01.approxCompact`

Read `Section4/B01/Compact.lean:150-175`.  Confirmed **monolithic**: it calls
`Paper3.exists_angular_real_vector_positive_physical_approx` and gets an
`IsSobolevPath` straight out; it never touches `temporalApprox`,
`spatialApprox` or `separatedAssembly`.  There is no homogeneous analogue of that
source theorem.  The lane's claim that B01 cannot be reused or parametrized is
correct, and the new glue duplicates none of it.

### 3.4 `SeparatedCompactHomogeneousDense` is a needed export, not an internal step

It is the shape `research/B02/Spec.lean:653` defines as a `def` and
`research/section4/STATEMENTS.md:831-836` asks for — the object `R46`'s two-radius
argument (`04-whole-space.tex:262`) inspects, exposing `φ`, `h`, `A` that the
`CompletedDenseVia` conclusion hides behind existentials.  It must stay public.
Note the asymmetry, worth recording: B01's twin `SeparatedCompactDense` exists only
as a spec `def` (`research/B01/Spec.lean:405`) and has **no** `formalization/`
counterpart, so this is the first of the pair to reach the Lean tree.

### 3.5 Imports and opens

The three imports (`Remaining`, `AnnularReal`, `SeparatedAssembly`) have disjoint
import lines and each supplies exactly one used theorem (`temporalApprox`,
`spatialApproxHomogeneous`, `separatedAssembly`).  None is redundant.

The module's closure contains **no** HeliCorgi `Formal.*` module (checked every
transitive `import` line down to `D01/ForceClass`, `B01/Separated`); the only
vendor imports are `NavierStokes.R3.*` from the OpenAI package.  So a future
`Tests.HomogeneousPartialV2` reaching this module through `Bindings` will not trip
the `warningAsError = true` rule.

> **Finding 3-A (severity: trivial, simplifier pass).**  `open scoped ContDiff
> ENNReal SchwartzMap` (line 65) — `SchwartzMap` is unused; no `SchwartzMap`/`𝓢`
> token occurs in the file.  Verified removable: a copy with the open trimmed to
> `open scoped ContDiff ENNReal` compiles silently (`/tmp/rev110/NoSchwartz.lean`,
> EXIT=0, no output).  Fold into the eventual `SIMP` pass rather than reopening
> the lane.

---

## 4. Honesty of `ATTEMPTS_APPROX_COMPACT.md` — mostly verified, one item refuted

### 4.1 Pitfall 1, the `add_le_add_right` non-termination — **REPRODUCED, verbatim**

`/tmp/rev110/attempt1.lean`, `set_option maxHeartbeats 400000` (bounded, as asked):

```
@add_le_add_right : ∀ {α} [Add α] [LE α] [AddLeftMono α] {b c : α},
  b ≤ c → ∀ (a : α), a + b ≤ a + c
```
confirming the recorded orientation — `add_le_add_right h c` gives `c + a ≤ c + b`,
addition on the **left**.

Control (plain `ℝ≥0∞` variables) — fast, clean type error, exactly as recorded:
```
/tmp/rev110/attempt1.lean:12:54: error: Type mismatch
  add_le_add_right h c
has type
  c + a ≤ c + b
but is expected to have type
  a + c ≤ b + c
```

The real case (`eLpNorm` terms, the lane's goal orientation at `ApproxCompact.lean:198`):
```
/tmp/rev110/attempt1.lean:21:2: error: (deterministic) timeout at `isDefEq`,
  maximum number of heartbeats (400000) has been reached
```
`lake env lean … 13.28s user` — the whole 400000-heartbeat budget is burned on one
`isDefEq`.  The recorded diagnosis (commutativity check forces `whnf` into the
`∫⁻`/`essSup` bodies; the fix is `add_le_add h le_rfl`, which matches the goal
orientation directly) is **accurate**, and the merged file uses the fix.  This is a
genuinely useful negative example — it belongs in `logs/LESSONS.md`.

### 4.2 Pitfall 2, `enorm_norm'` vs `enorm_norm` — **REPRODUCED, verbatim**

```
@enorm_norm  : ∀ {E} [SeminormedAddCommGroup E] (x : E), ‖‖x‖‖ₑ = ‖x‖ₑ
@enorm_norm' : ∀ {E} [SeminormedCommGroup E]    (x : E), ‖‖x‖‖ₑ = ‖x‖ₑ
/tmp/rev110/attempt2.lean:9:48: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖‖?x‖‖ₑ
in the target expression
  ‖‖v‖‖ₑ = ‖v‖ₑ
```
Exactly the recorded symptom, including "pattern not found on a goal that literally
displayed `‖‖v‖‖ₑ`".

### 4.3 Pitfall 4, `mul_le_mul_left'` / `mul_le_mul_right'` — **REPRODUCED, verbatim**

```
/tmp/rev110/attempt2.lean:15:8: error(lean.unknownIdentifier): Unknown identifier `mul_le_mul_left'`
/tmp/rev110/attempt2.lean:16:8: error(lean.unknownIdentifier): Unknown identifier `mul_le_mul_right'`
```

### 4.4 Pitfall 3, "`ring` refused on `ℝ≥0∞`" — **NOT REPRODUCIBLE**

The recorded claim is that `ring` refused to close
`‖f t‖ₑ * ‖v‖ₑ = ‖v‖ₑ * ‖f t‖ₑ` and suggested `ring_nf`.  Tested at the exact
recorded goal, for `v : ℝ` and for `v : E` a general normed group
(`/tmp/rev110/attempt3.lean`, `/tmp/rev110/attempt4.lean`):

```lean
example (f : ℝ → ℝ) (t v : ℝ) : ‖f t‖ₑ * ‖v‖ₑ = ‖v‖ₑ * ‖f t‖ₑ := by ring          -- EXIT=0, accepted
example {E} [NormedAddCommGroup E] (f : ℝ → ℝ) (t : ℝ) (v : E) :
    ‖f t‖ₑ * ‖v‖ₑ = ‖v‖ₑ * ‖f t‖ₑ := by ring                                      -- EXIT=0, accepted
example (a b : ℝ≥0∞) : a * b = b * a := by ring                                    -- EXIT=0, accepted
```

All three succeed.  `ring` works fine on `ℝ≥0∞` and on this goal.

> **Finding 4-A (severity: low, negative-example accuracy).**  `ATTEMPTS` pitfall 3
> is wrong as written.  Whatever `ring` actually failed on, it was a different goal
> (most likely one still carrying the un-rewritten `‖((‖v‖ : ℝ) • f) t‖ₑ`, i.e. a
> `Pi.smul_apply` obstruction rather than a `ring` limitation).  CLAUDE.md rule 4
> asks for negative examples precisely so they can be trusted later; a
> non-reproducible one is worse than none, because the next lane will avoid `ring`
> on `ℝ≥0∞` for no reason.  Ask the worker to correct or delete the entry.  Note
> this does **not** affect the proof — the merged line 81 uses an explicit
> `rw [… , mul_comm]` chain, which is correct either way.

Pitfalls 5 and 6 (calc-mixing `bochnerDatumENorm` with `eLpNorm`; re-elaborating
`separatedAssembly` three times) are performance observations, not falsifiable
error messages; the merged file follows both fixes (line 191 `show eLpNorm …`,
line 202 `have hasm := …` computed once).  The "Reuse checks" and "Commands"
sections of `ATTEMPTS` all match what I re-ran.

---

## 5. For the lead — `HomogeneousApproxAPI` status and the V2 question

### 5.1 Is every field of `HomogeneousApproxAPI` now proved?  **No — two are not.**

`research/B02/Spec.lean:274` `structure HomogeneousApproxAPI` has 1 data field
(`χ`) + 19 `Prop` fields.  With lane 110, **18 of 20** are discharged.  Still open:

1. **`annularPathApprox`** (`Spec.lean:337`) — **no proof exists anywhere.**
   `grep -rn 'annularPathApprox' formalization/ verification/` returns only
   docstrings and review prose; `REMAINING_SPLIT.md` row 7 is still open, and
   `Contracts/V1/HomogeneousPartial.lean:208` already names it as unproved.  Per
   `COMPARISON.md:103` and `REVIEW_CONTRACT.md:341` it is **not on the manuscript's
   chain** (the paper does the Bochner reduction first at `:251`), nothing consumes
   it, and `approxCompactHomogeneous` does **not** route through it.  Safe to leave
   open or to drop from a V2.

2. **`separatedAssembly`** (`Spec.lean:582`) — proved **only on `-3/2 < s`**, not
   in the field's stated `∀ (s : ℝ)` form:
   ```
   formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean:211:
   theorem separatedAssembly (s : ℝ) (hs : -3 / 2 < s) {J : ℕ} (φ : Fin J → ℝ → ℝ) …
   ```
   Lane 110 consumes it as `separatedAssembly s hs.1 …` (`ApproxCompact.lean:202`),
   taking `-3/2 < s` from `SplitRange.1`.  That is legitimate here — `SplitRange`
   supplies it — but the *field* as written at `:582` remains unproved.

So the answer the lead wants: **`approxCompactHomogeneous` is done and is the last
field on the manuscript's critical chain**, but `HomogeneousApproxAPI` as a whole is
not inhabitable yet, and `homogeneousApproxStatement := Nonempty HomogeneousApproxAPI`
(`Spec.lean`, end) is still out of reach on two counts.

### 5.2 The ⚠ note "near `Spec.lean:582`" — **it does not exist**

```
$ grep -n '⚠' research/B02/Spec.lean
466:  ⚠ *The original statement of this field (no integrability hypotheses) was
```
The **only** ⚠ in `Spec.lean` is at `:466`, and it belongs to
**`homogeneousDatumSub`** (field at `:490`), not to `separatedAssembly`.  That note
**is still accurate**: it says the hypothesis-free form was refuted by lane 068 and
that the corrected, integrability-carrying form is what is proved — and indeed the
field at `:490-496` carries the two `Integrable` side conditions, discharged by
`LebesgueDatum.lean:446 isHomogeneousSliceDatum_sub_of_integrable`
(`REMAINING_SPLIT.md` "already discharged" table).  No change needed there.

What the lead is remembering is the **recommendation** from lane 103, recorded in
`REMAINING_SPLIT.md` row 6: *"recommendation: register with `-3/2 < s` (not
`SplitRange`) in a V2 of `B02.homogeneous_partial` and add a ⚠ note at
`Spec.lean:582`."*  **That note was never added**, and lane 110 did not add it.

> **Finding 5-A (severity: medium, ledger accuracy — pre-existing, not this lane's
> fault, but now load-bearing).**  `Spec.lean:576-581`, the docstring immediately
> above `separatedAssembly`, still reads "`research/B01/Spec.lean`'s
> `separatedAssembly` with exactly one substitution … `MemForceCompact` and the
> strong measurability are word-for-word the same and are proved once."  With
> lane 103 merged, that now **overstates the record**: a reader takes it to mean
> the `∀ s` field is proved, when only `-3/2 < s` is.  Add the ⚠ note lane 103
> asked for before writing a V2 contract against this spec.

> **Finding 5-B (severity: low, ledger accuracy — pre-existing).**
> `REMAINING_SPLIT.md`'s "already discharged" table annotates
> `spatialApproxHomogeneous` as "**(unconditional)**".  It is not:
> ```
> AnnularReal.lean:225: theorem spatialApproxHomogeneous :
>     ∀ s : ℝ, SplitRange s → ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η → …
> ```
> It requires `SplitRange s`, matching the field at `Spec.lean:539`.  The lead will
> read this table when scoping V2; the word should go.

### 5.3 Is anything blocking a V2 contract?  **No technical blocker.**

A V2 registering (a) `separatedAssembly` on `-3/2 < s` and (b)
`approxCompactHomogeneous` is writable today:

* Both theorems are proved with exactly `[propext, Classical.choice, Quot.sound]`
  (§1), and the conformance file already transcribes the target types into the
  `Contracts.V1.Data` vocabulary and typechecks them.
* The contract-import policy is satisfiable without any new whitelist entry:
  `Contracts/V1/HomogeneousPartial.lean` already restates everything needed
  (`SplitRange` at `:197`, and `Data.lean` carries `CompletedDenseHomogeneous`
  `:752`, `CompletedDenseVia` `:732`, `forceClassCompact` `:563`,
  `MemForceCompact` `:559`, `bochnerDatumENorm` `:205`, `MemBochnerDatum` `:212`).
* The `Tests` `warningAsError` rule is safe: the new module's transitive import
  closure contains no HeliCorgi `Formal.*` (§3.5), and the module itself compiles
  with **zero** warnings.
* `Contracts/V1/HomogeneousPartial.lean:207-209` already documents the three
  excluded obligations, so a V2 is exactly "V1 + `separatedAssembly@(-3/2<s)` +
  `approxCompactHomogeneous`", with `annularPathApprox` still excluded.

Three decisions belong to the lead, none of them blockers:
1. Register `separatedAssembly` with the hypothesis `-3/2 < s` (lane 103's
   recommendation) rather than `SplitRange s` — the weaker hypothesis is the
   honest one and is what the theorem proves; `approxCompactHomogeneous` needs
   only `SplitRange.1` to feed it.
2. Settle finding 5-A first, so the V2 contract's docstrings point at a spec that
   does not overstate.
3. Decide whether `annularPathApprox` is dropped from the spec outright (it is off
   the manuscript's chain and feeds nothing) or carried as a permanent known gap.

---

## 6. Commands run (all from the worktree, after `. scripts/lean-env.sh`)

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.B02.ApproxCompact` | EXIT=0, "Build completed successfully (9892 jobs)" |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/B02/ApproxCompact.lean` | EXIT=0, **0 bytes** output |
| `cd verification && lake env lean ../research/B02/axioms_approx_compact.lean` | EXIT=0, 2 `example`s typecheck, 5 × `[propext, Classical.choice, Quot.sound]` |
| `make check` | EXIT=0, 13 policy tests OK, 30 work items consistent |
| `make test` | EXIT=0, every registered contract "standard logical axioms only" |
| `lake env lean /tmp/rev110/fidelity.lean` | `rfl` defeq spec↔lane ✓; `#check` dump; non-vacuity 1–2 ✓ |
| `lake env lean /tmp/rev110/fidelity3.lean` | EXIT=0, `forceClassCompact` inhabited ✓ |
| `lake env lean /tmp/rev110/fidelity2.lean` | `#print` of spec type; `MemBochnerDatum` inhabited by a nonzero path ✓ |
| `lake env lean /tmp/rev110/attempt1.lean` (`maxHeartbeats 400000`) | pitfall 1 reproduced: `(deterministic) timeout at isDefEq` |
| `lake env lean /tmp/rev110/attempt2.lean` | pitfalls 2 and 4 reproduced verbatim |
| `lake env lean /tmp/rev110/attempt3.lean`, `attempt4.lean` | pitfall 3 **refuted** (EXIT=0); `exact?` finds no Mathlib duplicate |
| `lake env lean /tmp/rev110/NoSchwartz.lean` | EXIT=0 — the `SchwartzMap` open is removable |

## 7. Summary of findings

| # | severity | where | what |
|---|---|---|---|
| 2-A | low | `REMAINING_SPLIT.md` row 8, `ATTEMPTS` | "token-identical to `Spec.lean:607`" — it is defeq (`rfl`-checked), not token-identical; 3 token diffs |
| 2-B | info | lane summary | gluing estimate also needs `∀ j, AEStronglyMeasurable (φ j) forceTimeMeasure`, not "only `1 ≤ q`" |
| 2-C | low | `ApproxCompact.lean` docstrings (28, 69, 85) + `ATTEMPTS` + `REMAINING_SPLIT` | `04-whole-space.tex:257` should be `:253-255` (content line 254) |
| 3-A | trivial | `ApproxCompact.lean:65` | unused `open scoped … SchwartzMap`; verified removable |
| 4-A | low | `ATTEMPTS` pitfall 3 | "`ring` refused on `ℝ≥0∞`" is not reproducible — `ring` closes the recorded goal |
| 5-A | medium | `Spec.lean:576-581` (pre-existing) | missing ⚠: `separatedAssembly` is proved only on `-3/2 < s`, docstring implies the `∀ s` form |
| 5-B | low | `REMAINING_SPLIT.md` (pre-existing) | `spatialApproxHomogeneous` annotated "(unconditional)"; it needs `SplitRange s` |

None of these touches a proof.  **ACCEPT-WITH-NOTES** — merge; fold 2-A, 2-C and
4-A into the lane's own md files, 3-A into the next `SIMP` pass, and settle 5-A /
5-B before writing the V2 contract.
