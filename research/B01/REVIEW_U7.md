# B01 unit 7 review — `separatedTemporalDense` / `temporalApprox`

Lane 063, worktree `.claude/worktrees/063-B01-unit-7-split`, commit `8d9a621`.
Module `formalization/NSFormalization/Section4/B01/Temporal.lean` (178 lines),
conformance `research/B01/axioms_u7.lean`, logs `research/B01/{ATTEMPTS_U7,U7_SPLIT}.md`.

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is correct, the two theorems are the spec objects token-for-token,
the axiom audit is clean, and nothing is re-copied.  Three LOW findings, all about
the heartbeat bump and the prose that documents it; no code defect.

---

## 1. Commands and results

All run with `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, one lake at a time,
from `verification/` unless stated.

| # | Command | Result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | `== OK` |
| 2 | `lake build NSFormalization.Section4.B01.Temporal` | **EXIT 0**, `Build completed successfully (9882 jobs)`; `grep "B01/Temporal"` over the full log → **no diagnostics from the file** |
| 3 | `lake env lean ../formalization/NSFormalization/Section4/B01/Temporal.lean` (fresh, uncached elaboration of the source) | **EXIT 0, 0 bytes of output** — no `sorry` warning, no linter warning |
| 4 | `lake env lean ../research/B01/axioms_u7.lean` | **EXIT 0**; both spec-typed `example`s typecheck; three `#print axioms` all exactly `[propext, Classical.choice, Quot.sound]` (`lp_coeFn_finsetSum`, `separatedTemporalDense`, `temporalApprox`) |
| 5 | `grep -nE "sorry\|admit\|native_decide\|axiom\|set_option"` on the module | 2 hits: line 38 (`axioms_u7.lean` inside a docstring — prose), **line 71 `set_option maxHeartbeats 1000000 in`**.  No `sorry`, no `admit`, no `native_decide`, no `axiom` declaration. |
| 6 | same grep on `research/B01/axioms_u7.lean` | 5 hits, all prose or the three `#print axioms` lines.  Clean. |
| 7 | `make check` (from worktree root) | **EXIT 0** — `check_formalization_plan --check`, `check_contracts`, `test_contract_policy` (13 tests OK), `check_work_queue` (30 work items consistent) |

Scratch bisection and heartbeat counting were done on copies in `/tmp/u7scratch/`;
**nothing in the worktree was modified** except this file.

---

## 2. Heartbeat audit

The bump is `set_option maxHeartbeats 1000000 in` on line 71, **targeted** at
`separatedTemporalDense` only (not file-level).  `temporalApprox` and
`lp_coeFn_finsetSum` sit outside it and compile at the default 200 000.

### 2.1 Is it needed?  Yes.

`#count_heartbeats in` on the declaration (Mathlib `Mathlib/Util/CountHeartbeats.lean`,
`set_option Elab.async false`):

```
Used 375034 heartbeats, which is greater than the current maximum of 200000.
Try this:
  [apply] set_option maxHeartbeats 400000 in
```

Direct bisection (`sed '71s/.*/set_option maxHeartbeats N in/'`, then `lake env lean`):

| `maxHeartbeats` | result |
|---|---|
| (line deleted → default 200 000) | **FAIL** `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` |
| 300 000 / 350 000 / 370 000 / 372 000 / 373 000 / 374 000 | **FAIL** `timeout at isDefEq` |
| **375 000** | **PASS** |
| 376 000 / 380 000 / 400 000 | PASS |

So the true minimum is in `(374000, 375000]`, matching the 375 034 count.
The `simp only [Set.mem_ofPred_eq]` fix does **not** remove the need for a bump.

### 2.2 Finding 1 — LOW — `separatedTemporalDense`: the bump is 2.7× oversized

`1000000` is 2.7× the measured requirement of ~375 000, and Mathlib's own
`#count_heartbeats` "Try this" suggests `400000`.  An oversized ceiling hides future
regressions: the proof could silently double in cost and still compile.

**Fix:** change line 71 to `set_option maxHeartbeats 400000 in`.

### 2.3 Finding 2 — LOW — the recorded cause is **inaccurate**

Module docstring (lines 76-78):

> The `maxHeartbeats` bump covers the one expensive step: reducing the heavy separated-span
> membership predicate (through `separatedLp` and the `RealVectorSobolev`/Fourier carriers) to its
> existential normal form while destructuring `(g i).2`.

`ATTEMPTS_U7.md:22-26` and `U7_SPLIT.md:20,36` ("leaving a single `maxHeartbeats 1000000` bump
for the still-heavy reduction") say the same.  **That is not where the cost is.**

Measured by `#count_heartbeats in` on the declaration with progressively `sorry`'d tails
(all in `/tmp/u7scratch/v_*.lean`):

| prefix elaborated | heartbeats | marginal cost of the step |
|---|---|---|
| statement only (`:= by sorry`) | 3 431 | — |
| … through `choose` (incl. `hdtf`, `hdense`, `mem_span_set'`, `key`) | 81 282 | setup + `key` ≈ 77 850 |
| … through the three easy bullets (`ContDiff`/`HasCompactSupport`/`tsupport`) | 81 643 | ≈ 360 |
| … + `hFi` | 174 040 | **≈ 92 400 (25 %)** |
| … + `hyae` | 183 586 | ≈ 9 550 |
| … + `hBcoe`, `hdiff` | 186 331 | ≈ 2 750 |
| … + `hnorm_lt`, `hval` | 374 877 | **≈ 188 550 (50 %)** |
| whole declaration | 375 034 | final `calc` ≈ 160 |

Cross-check: replacing the entire proof of `key` (the documented step) with `sorry`
still costs **334 441** heartbeats — i.e. the `(g i).2` destructure is only
**≈ 40 600 (11 %)** of the budget, and the declaration would *still* need a bump
(334 441 > 200 000) if that step were free.

Lean itself agrees: every timeout in the bisection is reported at
`Temporal.lean:162` (`rw [eLpNorm_congr_ae hdiff, ← Lp.enorm_def]`, column 34 =
`← Lp.enorm_def`) and `:164` (the `calc`), i.e. inside `hval` — never inside `key`.

So the real cost centres are, in order:
1. **`hval` (≈ 50 %)** — the `show eLpNorm (separatedPath …) q forceTimeMeasure = ‖y - B‖ₑ`
   delta-unfolding of `bochnerDatumENorm` over the `RealVectorSobolev s` carrier, plus
   `rw [eLpNorm_congr_ae hdiff, ← Lp.enorm_def]`;
2. **`hFi` (≈ 25 %)** — the per-summand `Lp.coeFn_smul` / `smul_smul` bookkeeping;
3. `key` (≈ 11 %) — the step the docstring names.

**Fix:** correct the attribution in `Temporal.lean:76-78`, `ATTEMPTS_U7.md` §1 and
`U7_SPLIT.md:20,36`.  The bump is for `hval`/`hFi`, not for the `(g i).2` destructure.
(Optional, not required for acceptance: `hval` is the obvious target if anyone wants the
number below 200 000 — e.g. a `bochnerDatumENorm`-level rewrite lemma proved once outside
the heavy carrier, instead of the in-proof `show`.)

### 2.4 What *is* accurate about the recorded cause

The claim that an unguarded `obtain … := (g i).2` blows past even 1 000 000 heartbeats is
true — see honesty check H1 below.  The `simp only [Set.mem_ofPred_eq]` rewrite is a real and
necessary fix; it just is not what the surviving bump pays for.

Severity: the bump is **targeted and needed** → LOW per the review rubric; findings 1 and 2
are documentation/hygiene, not correctness.

---

## 3. Spec conformance — clean

Normalised (whitespace-collapsed) textual comparison:

* **`temporalApprox`**: `Temporal.lean:170-175` is **token-for-token identical** to the
  `BochnerApproxAPI` field type at `research/B01/Spec.lean:273-279`, including the quantifier
  order `∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s b, MemBochnerDatum q s b → ∀ η, 0 < η → …`, the three
  properties in the order `ContDiff ℝ ∞ (φ j)`, `HasCompactSupport (φ j)`,
  `tsupport (φ j) ⊆ Ioi (0 : ℝ)`, and the **subtraction order** `separatedPath φ A - b`
  (not `b - separatedPath φ A`).  Proof term is `fun q hq1 hqt s b hb η hη =>
  separatedTemporalDense …` — a plain eta-expansion, no extra hypotheses.
* **`SeparatedTemporalDense`**: `Temporal.lean:81-84` (the conclusion of
  `separatedTemporalDense`) is the body of `Spec.lean:382-388` verbatim.
* **`axioms_u7.lean` examples**: example 2 is the field type verbatim, discharged by
  `NSFormalization.Section4.B01.temporalApprox` with no arguments; example 1 is the
  `SeparatedTemporalDense` body verbatim under the guards `1 ≤ q → q ≠ ⊤`.  Both are stated
  in the **contract** vocabulary — the file `open`s `BlowupDensity.Contracts.V1.Data`, so
  `MemBochnerDatum` and `bochnerDatumENorm` there are the `Contracts/V1/Data.lean:212,205`
  declarations, not the `Section4/B01` restatements; the examples therefore genuinely test the
  defeq bridge.  `separatedPath` is restated in `axioms_u7.lean:30-32` verbatim from
  `Spec.lean:147-149`.
* **No re-copies.**  `grep -nE "^(def|abbrev|structure|instance)"` on `Temporal.lean` → **none**.
  `separatedField`/`separatedPath` come from the merged `Section4/B01/Separated.lean:58,63`;
  `MemBochnerDatum`/`bochnerDatumENorm`/`bochnerSpace` from `Section4/B01/Compact.lean:68,75,103`;
  `forceTimeMeasure` from `Section4/D01/ForceClass.lean:147`.  The module contains only three
  `theorem`s.
* **`B02` compatibility**: `research/B02/Spec.lean:609-615` defines `SeparatedTemporalDense`
  with byte-identical text, so this unit is directly reusable by `B02` stage 4 as planned.

### Finding 3 — LOW (note only) — the standalone `def` is proved under the field's guards

`SeparatedTemporalDense (q s)` is a predicate for *arbitrary* `q`; this lane proves
`∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s, SeparatedTemporalDense q s`, not `∀ q s, SeparatedTemporalDense q s`.
Those guards are exactly the `temporalApprox` field's own guards, exactly the manuscript's
`1 ≤ q < ∞` (`04-whole-space.tex:251`), and exactly the documented consumption shape
(`research/B01/REVIEW.md:74`: "`api.temporalApprox q h1 h2 s : SeparatedTemporalDense q s`").
**No action required** — recorded only so unit 10 does not later assume the unguarded form.

---

## 4. Mathematics — correct

Route audited line by line against `research/B01/COMPARISON.md:151` row 7.

1. **Density instantiation.**  `dense_span_separatedLp` (`Paper3/SeparatedBochnerDensity.lean:30`)
   at `H := RealVectorSobolev s`, `μ := forceTimeMeasure`, `D := Set.univ` (`dense_univ`), and
   `A := ` the positive-time factor set with `hdtf := dense_positive_temporal_factors q hqt`
   (`Paper3/PositiveTemporalDensity.lean:73`), whose members carry
   `HasCompactSupport a ∧ ContDiff ℝ ∞ a ∧ tsupport a ⊆ Ioi 0` — the exact three properties the
   spec demands of `φ j`.
   **`forceTimeMeasure = positiveTimeMeasure` on the nose**: `Section4/D01/ForceClass.lean:147`
   is `abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure`, and
   `Contracts/V1/Data.lean:118` is the same `abbrev`, with
   `Paper3/PositiveTemporalDensity.lean:11` `abbrev positiveTimeMeasure := volume.restrict (Ioi 0)`.
   The lane's "retype at `forceTimeMeasure`" (`Temporal.lean:91-93`) is therefore
   **reducible defeq**, not a coercion or a re-proof.  The stated motive (a uniform-measure
   generator set) is sound and matches recorded snag 2.
2. **Span unwrapping.**  `Submodule.mem_span_set'.mp` gives `n`, `f : Fin n → ℝ`,
   `g : Fin n → ↥Gen`, `∑ i, f i • ↑(g i) = y`.  Per index, `(g i).2` yields a coefficient
   `hcoef i : RealVectorSobolev s` and a factor `gg` with smooth representative `afn i`, and
   `separatedLp_ae` (`SeparatedBochnerDensity.lean:23`) turns `↑(g i)` into
   `fun t => afn i t • hcoef i` a.e.
   **Re-absorption is genuine**: `c • separatedLp q A g` becomes `(c • g) • A` via
   `hFi` (`Lp.coeFn_smul`, then `smul_smul`/`smul_eq_mul`:
   `f i • (afn i t • hcoef i) = (f i • afn i t) • hcoef i`), so the produced `φ i := f i • afn i`
   is a *scalar multiple of a positive-time factor*, hence again one:
   `ContDiff.const_smul`, `HasCompactSupport.smul_left`, and
   `tsupport_smul_subset_right (fun _ => f i) (afn i) |>.trans (hsupp i)`.
   Correct — the ℝ-linear span adds no non-separated terms.
3. **`Lp`-quotient → representative.**  `lp_coeFn_finsetSum` (proved by `Finset.induction`
   with `Lp.coeFn_zero`/`Lp.coeFn_add`, a genuine gap in Mathlib — only `lp.coeFn_sum` exists,
   for the sequence space) gives `⇑(∑ i, F i) =ᵐ fun t => ∑ i, ⇑(F i) t`; combined with
   `ae_all_iff.mpr hFi` and `← hsum` this yields `⇑y =ᵐ separatedPath (fun i => f i • afn i) hcoef`.
   `hBcoe := hb'.coeFn_toLp` gives `⇑B =ᵐ b`, and
   `(hyae.symm.sub hBcoe.symm).trans (Lp.coeFn_sub y B).symm` gives
   `separatedPath φ A - b =ᵐ ⇑(y - B)`.  Each `EventuallyEq` step is a.e.-correct; the
   `filter_upwards` sets are finite intersections of full-measure sets.  Then
   `eLpNorm_congr_ae` + `← Lp.enorm_def` give
   `bochnerDatumENorm q s (separatedPath φ A - b) = ‖y - B‖ₑ`, legitimate because
   `bochnerDatumENorm q s G` is *definitionally* `eLpNorm G q forceTimeMeasure`
   (`Compact.lean:75`, `Data.lean:205`).
4. **`η = ⊤` handled** (`Temporal.lean:98-102`): `by_cases hηtop`; if `η = ⊤` take `ε := 1`
   (`ENNReal.ofReal 1 ≤ ⊤`), else `ε := η.toReal`, positive by
   `ENNReal.toReal_pos hη.ne' hηtop`, with `ENNReal.ofReal_toReal hηtop` giving
   `ENNReal.ofReal ε = η`.  The final chain
   `ofReal ‖y - B‖ < ofReal ε ≤ η` is strict, as the spec requires.
5. `Fact (1 ≤ q)` is supplied as a local instance (`have : Fact (1 ≤ q) := ⟨hq1⟩`), picked up
   by local-context instance search for `separatedLp`, `Lp`, `dense_span_separatedLp` and
   `dense_positive_temporal_factors`.

No gap found.  The coefficients `A j := hcoef j` are arbitrary elements of the fibre, as the
spec docstring (`Spec.lean:269-272`) explicitly intends — spatial compactness is `spatialApprox`'s job.

---

## 5. Honesty of `research/B01/ATTEMPTS_U7.md`

Two snags spot-checked, both **reproduced exactly**.

**H1 — snag 1** ("`obtain ⟨…⟩ := (g i).2` … the *deep* pattern … needs > 1 000 000").
Replaced `have hmem := (g i).2; simp only [Set.mem_ofPred_eq] at hmem; obtain … := hmem`
with the direct `obtain ⟨hcoef, -, gg, ⟨a, hgae, hac, hsm, hsupp⟩, heq⟩ := (g i).2`,
keeping `maxHeartbeats 1000000`:

```
/tmp/u7scratch/obtaindirect_1M.lean:115:4: error: (deterministic) timeout at `whnf`,
  maximum number of heartbeats (1000000) has been reached
```

Confirmed — and the timeout is at `whnf` on exactly the destructure line, as recorded.
The parenthetical "(`Set.mem_setOf_eq` works too but is deprecated in favour of
`Set.mem_ofPred_eq`)" is also true at this pin:
`Mathlib/Data/Set/Operations.lean:81` — `@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq`.

**H2 — snag 3** ("`/-- … -/` then `set_option … in` then `theorem` is a parse error").
Minimal file `/tmp/u7scratch/parsetest.lean`:

```
/-- A docstring. -/
set_option maxHeartbeats 400000 in
theorem foo : True := trivial
```

```
parsetest.lean:1:19: error: unexpected token 'set_option'; expected … 'theorem' or 'unif_hint'
```

Confirmed verbatim.  The module correctly puts `set_option … in` *before* the docstring,
so the bump is really in force (also independently confirmed: deleting line 71 makes the
file fail at 200 000).

The remaining claims in `ATTEMPTS_U7.md` (snags 2, 4, 5) are consistent with the shipped
proof text; only the *attribution* of the surviving bump (finding 2) is wrong.

---

## 6. Note (no severity) — build-graph reachability

`NSFormalization.Section4.B01.Temporal` is reachable only by naming it explicitly:
`formalization/NSFormalization.lean` (the root of the `NSFormalization` default target)
imports 303 modules and **none** from `Section4` (`grep -c Section4` → 0), and nothing under
`verification/` imports `Section4.B01.*`.  So `lake build` (default targets `Tests`, `Contracts`)
and `lake test` do not cover this module; it is validated by `research/B01/axioms_u7.lean`.
This is **pre-existing and uniform for every B01 unit** (`Compact.lean`, `Separated.lean` are in
the same position) and the wiring is scheduled as unit 10 of `COMPARISON.md` (promotion to
`verification/Contracts/V1/BochnerApprox.lean` + `Bindings` entry + `#print axioms` test).
**No action for this lane** — recorded so unit 10 does not forget it.

---

## 7. Summary of findings

| # | Severity | Declaration / file | What is wrong | Fix |
|---|---|---|---|---|
| 1 | LOW | `separatedTemporalDense`, `Temporal.lean:71` | `maxHeartbeats 1000000` is 2.7× the measured need (375 034; threshold in `(374000, 375000]`). Targeted and genuinely needed — the default 200 000 fails — but an oversized ceiling masks future cost regressions. | `set_option maxHeartbeats 400000 in` (Mathlib's own suggestion). |
| 2 | LOW | `Temporal.lean:76-78`, `ATTEMPTS_U7.md:17-26`, `U7_SPLIT.md:20,36` | The recorded cause misattributes the bump to the `(g i).2` destructure (`key`), which is only ≈ 40 600 heartbeats (11 %). The real cost is `hval` ≈ 188 550 (50 %) and `hFi` ≈ 92 400 (25 %); with `key := sorry` the declaration still needs 334 441 > 200 000. Lean's own timeout always points at `Temporal.lean:162`/`:164`, inside `hval`. | Rewrite the three prose passages to name `hval` (the `show eLpNorm …` unfold of `bochnerDatumENorm` + `rw [eLpNorm_congr_ae, ← Lp.enorm_def]`) and `hFi`. |
| 3 | LOW (note) | `axioms_u7.lean:36-43` | `SeparatedTemporalDense q s` is discharged only under `1 ≤ q` and `q ≠ ⊤`, not for all `q`. Faithful to the field's own guards and to `04-whole-space.tex:251`. | None; record for unit 10. |

No MEDIUM or HIGH findings.  No `sorry`, no `admit`, no `native_decide`, no added axiom;
all three declarations reduce to `[propext, Classical.choice, Quot.sound]`.
