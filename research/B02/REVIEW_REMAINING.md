# Review — lane 097 (B02, remaining spec fields)

Reviewer run: worktree `.claude/worktrees/097-B02-remaining-fields`, commit `c19aa54`.
Scope: `formalization/NSFormalization/Section4/B02/Remaining.lean`,
`research/B02/{REMAINING_SPLIT.md,ATTEMPTS_REMAINING.md,axioms_remaining.lean}`.

## Verdict: **ACCEPT-WITH-NOTES**

The five theorems are token-faithful to their spec fields, compile clean, carry only the
three standard axioms, and the `M`/`S` split is honest — I independently reproduced every
claim in it, including the two load-bearing negative ones (no homogeneous datum
`smul`/`sum` combinator; `B01`'s `approxCompact` is monolithic). Notes below are one
substantive route finding for row 6 and three bookkeeping nits. Nothing blocks merge.

---

## 1. Compile / audit checks

| command (from `WT/verification` unless noted) | result |
|---|---|
| `lake build NSFormalization.Section4.B02.Remaining` | `Build completed successfully (9883 jobs)`. Only pre-existing `Paper3.*` dependency warnings (`unnecessarySeqFocus`, `unusedVariables`, one `SchwartzMap.smul_apply` deprecation); **no** warning on any `Remaining.lean` line |
| `lake env lean ../formalization/NSFormalization/Section4/B02/Remaining.lean` | silent, exit 0 |
| `lake env lean ../research/B02/axioms_remaining.lean` | exit 0; 5 declarations, each **exactly** `[propext, Classical.choice, Quot.sound]` (`chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range`, `temporalApprox`) |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' Remaining.lean axioms_remaining.lean` | only docstring prose and the five `#print axioms` lines; no declaration, no option |
| `make check` (WT root) | passed — architecture checks, `test_contract_policy.py` 13/13 OK, `check_work_queue.py` "30 work items … consistent" |
| `make test` (WT root, reviewer extra) | passed — every registered contract "checked; standard logical axioms only" |

`git show --stat c19aa54`: 4 files, 447 insertions, 0 deletions. No frozen `Contracts/V1` or
`Tests` file touched. `formalization/lakefile.toml`'s `NSFormalization` lib has no explicit
`roots`, so `Section4/B02/Remaining.lean` is globbed and will be built by CI.

## 2. Statement fidelity

**The four `χ` fields — exact.** Diffed against `Spec.lean:280,282,285,287`; each module
theorem is the field with `χ` replaced by `baseCutoff` and nothing else:

| spec field | spec type | `Remaining.lean` |
|---|---|---|
| `chi_smooth` :280 | `ContDiff ℝ ∞ χ` | `:67`, `(baseCutoff : Space → ℝ)` |
| `chi_one` :282 | `∀ x : Space, ‖x‖ ≤ 1 → χ x = 1` | `:72` |
| `chi_vanishes` :285 | `∀ x : Space, 2 ≤ ‖x‖ → χ x = 0` | `:78` |
| `chi_range` :287 | `∀ x : Space, χ x ∈ Icc (0 : ℝ) 1` | `:83` |

Both inequalities are **non-strict, in the spec's direction**: `‖x‖ ≤ 1` and `2 ≤ ‖x‖`, not
`<`. They match the vendor hypotheses verbatim — `baseCutoff_eq_one {x} (hx : ‖x‖ ≤ 1)`
(`ComparisonCutoffs.lean:46`) and `baseCutoff_eq_zero {x} (hx : 2 ≤ ‖x‖)` (`:50`) — so the
`fun _ hx => …` wrappers are pure eta, no weakening.

**Same cutoff as `B01`? Yes.** `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff` is the
identical object bound at `Bindings/BochnerPartial.lean:66`, and `chi_range`'s anonymous
constructor is the identical `⟨baseCutoff_nonneg x, baseCutoff_le_one x⟩` of `:70-71`. A
future joint consumer (R46) therefore sees one cutoff across `B01` and `B02`.

**Vacuity: none.** `baseCutoff` is the underlying function of `baseBump`, a genuine
`ContDiffBump`; `chi_one` forces the value 1 on the unit ball, so `χ ≡ 0` is excluded and
`chi_range`/`chi_vanishes` are not satisfied trivially.

**`temporalApprox` — token-identical to the registered `B01` field.** I printed both types
with `pp.fullNames`:

```
BochnerPartialAPI.temporalApprox        NSFormalization.Section4.B02.temporalApprox
  … Data.MemBochnerDatum q s b …          … B01.MemBochnerDatum q s b …
  … Data.bochnerDatumENorm q s            … B01.bochnerDatumENorm q s
      (BochnerPartial.separatedPath φ A - b) < η   (B01.separatedPath φ A - b) < η
```

identical except for those three names, and all three are `rfl`-equal. Verified by a
throwaway `/tmp` file, all accepted (exit 0):

```lean
example … : specSeparatedPath φ A = NSFormalization.Section4.B01.separatedPath φ A := rfl
example … : Contracts.V1.BochnerPartial.separatedPath φ A
              = NSFormalization.Section4.B01.separatedPath φ A := rfl
example … : Data.MemBochnerDatum q s b   = B01.MemBochnerDatum q s b   := rfl
example … : Data.bochnerDatumENorm q s b = B01.bochnerDatumENorm q s b := rfl
```

where `specSeparatedPath` is `Spec.lean:219` copied verbatim. So the split table's
"`separatedPath` differs only in namespace, the two `def`s are defeq" is machine-confirmed,
in both directions (spec-local and contract-local). `axioms_remaining.lean:65-71`
independently states the field in the `Contracts.V1.Data` vocabulary and accepts
`B02.temporalApprox`, so the defeq bridge is exercised, not just asserted.

## 3. Findings

### F1 — (info / route correction, row 6) A shorter route to `separatedAssembly` exists, but only on `-3/2 < s`
*Severity: informational. Location: `REMAINING_SPLIT.md` row 6, `ATTEMPTS_REMAINING.md` §1.*

The split proposes `isHomogeneousPath_separated` built by generalising the `_sub`
combinators from "difference of two" to "`ℝ`-combination of `Fin J`". That is correct and
I confirm the blocker: grepping `Section4` for any `add`/`smul`/`sum`/`neg`/`zero`
combinator on `IsHomogeneousDatum` / `IsHomogeneousVectorDatum` / `IsHomogeneousSliceDatum`
/ `IsSliceDistribution` returns **nothing**; only the four `_sub` forms exist
(`HomogeneousWitness.lean:534`, `:551`, `:565` `isSliceDistribution_sub`, `:585`).

But the split misses a second route, which the contract lane should know about:

* `isSliceDistribution_unique` / `isHomogeneousSliceDatum_unique` (`:445`) are
  **unconditional** — the totalization caveat breaks *additivity*, not uniqueness.
* `isHomogeneousPath_compact` (`:658`) already gives
  `IsHomogeneousPath s (separatedField φ h) (compactHomogeneousPath hs hF hC)` for any
  smooth compact spacetime field, and `separatedField φ h` is one (B01's
  `contDiff_separatedField` / `hasCompactSupport_separatedField`).
* So conjunct 2 would follow from linearity of the **concrete** `homogeneousVectorDatum`,
  which by `homogeneousVectorDatum_coe` (`:379`, `rfl`) and
  `homogeneousProfile s f ξ = ‖ξ‖^s · angularFourier f ξ` (`:131`) reduces to linearity of
  `angularFourier` plus `MemLp.toLp` congruence — roughly 40 lines and **no integrability
  side conditions at all**, since every profile here is Schwartz.

The catch, and the reason the split's classification still stands: `isHomogeneousPath_compact`
carries `hs : -3/2 < s`, while the spec field `separatedAssembly` (`Spec.lean:582`)
quantifies over **all real `s`** with no `SplitRange` hypothesis. So this route proves the
field only on `-3/2 < s` — which is nevertheless the entire range
`approxCompactHomogeneous` uses (`SplitRange s := -3/2 < s ∧ s ≤ 0`, `Spec.lean:237`).
**Recommendation for the contract lane:** decide explicitly whether `separatedAssembly`
should keep `∀ s : ℝ`. If adding `-3/2 < s` survives the two-agent fidelity check, row 6
drops from `M` to `S-M` and row 8 unblocks much sooner. If it stays `∀ s : ℝ`, the split's
general-additivity route is the right one.

*Fix:* add a paragraph to `REMAINING_SPLIT.md` row 6 recording both routes and the `s`-range
trade-off. No code change.

### F2 — (minor) Row 6 size estimate is slightly low
*Severity: minor. Location: `REMAINING_SPLIT.md:58` "M (~80-120 ln)".*

The `_sub` block is ~60 lines for "difference of two" at three levels. The `Fin J` +
`ℝ`-smul generalization needs `Lp.coeFn_sum`, `integral_finset_sum` and `map_sum` at each
of the three levels, and the per-term integrability the totalization forces. Reusable
pieces do exist (`Separated.lean:73` `integrable_schwartz_mul`, `:90-102`
`coe_sum_smul_apply` / `space_sum_apply`, and `isSobolevPath_separated` `:182` as the exact
shape template). Realistic: **110-160 lines**. A mild underestimate, not a misclassification.

*Fix:* adjust the number.

### F3 — (minor) Row 7's real blocker is narrower than stated, and the row is off the critical path
*Severity: minor. Location: `REMAINING_SPLIT.md:91-103`.*

Confirmed the premise: `Section4/B02/Annular.lean` contains **no** path-level statement.
Every declaration is slice-level — `IsAnnularRestriction δ R (A Z : RealVectorSobolev s)`
(`:75`) takes single elements, and the tokens `Path`, `MemBochnerDatum`,
`bochnerDatumENorm` do not occur in the file at all. So the stated route (measurable
selection in `t` of `annularTruncLp`, path-level DCT) is indeed new work and is the right
route.

Two refinements worth recording:

1. Blocker (a) is smaller than "no measurable-in-`t` selection exists". `annularTruncLp δ R`
   (`:205`) is multiplication by `indicator (frequencyAnnulus δ R) 1` on `L²`, i.e. a
   bounded linear map `RealSobolevHilbert s → FourierData`. Prove *that* (short), and
   measurability of `t ↦ annularTruncLp δ R (b t)` is `Measurable.comp` / continuity
   composed with `b`'s strong measurability, and `MemBochnerDatum q s D` follows from the
   contraction bound. The genuinely new work is then only blocker (b), the DCT in `(δ,R)`.
2. By the spec's own docstring (`Spec.lean:339-341`), `annularPathApprox` is "**not** a step
   of the manuscript's own proof" — the manuscript does the Bochner reduction first
   (`04-whole-space.tex:251`) and truncates the finitely many fibre values afterwards. It
   feeds nothing: `approxCompactHomogeneous` goes through `temporalApprox` +
   `spatialApproxHomogeneous` + `separatedAssembly`. It is therefore the **lowest-value**
   `M` row, and the contract lane may reasonably ask whether it belongs in the API at all.

### F4 — (confirmed, no action) Row 8's "monolithic" claim is exactly right
*Severity: none — verification of the worker's key negative finding.*

I read `Section4/B01/Compact.lean:155-181`. The proof body is

```lean
obtain ⟨F, hF, hFc, hFs, f, hf, hc, hFi, he⟩ :=
  exists_angular_real_vector_positive_physical_approx s q hq2 (hb'.toLp b) hεpos
```

followed by packaging through `angularRealVectorSlice` / `isSobolevPath_angularRealVectorSlice`.
It never mentions `temporalApprox`, `spatialApprox` or `separatedAssembly`. So there is no
temporal+spatial glue to parametrize, and the worker is right that the task brief's "glued
exactly as `B01`'s `approxCompact` glues its inputs" does not describe the code.

**Homogeneous analogue of the source theorem: none.** Grepped `formalization/NSFormalization/{Paper3,Source}`
for `homogeneous`. All hits are norm / integrability / scaling facts —
`compact_homogeneous_norm_bound`, `schwartz_homogeneous_negative_integrable`,
`compact_fourier_homogeneous_negative_integrable`, `stronglyMeasurable_homogeneousFourier_time`,
`compact_homogeneousFourier_time`, `homogeneousFourierNorm_translate`,
`homogeneous_energy_le_bound_add_L2`, `homogeneousFourierNorm_le_physical`,
`uniform_homogeneousFourier_time`, `memLp_homogeneousFourier_time`,
`homogeneous_low_frequency_integrable`, `homogeneous_negative_integrable`,
`homogeneous_energy_dilate`. **No density / approximation theorem.** Confirmed.

**Is `SeparatedCompactHomogeneousDense` (`Spec.lean:640-664`) the shortest route? Yes** — it
is the only route, given F4. One addition the split does not name: the triangle-inequality
glue it needs, bounding `bochnerDatumENorm q s (separatedPath φ A' - separatedPath φ A)` by
the weighted sum of fibre errors `‖A' j - A j‖ₑ`, is **realization-independent** (it mentions
neither `IsSobolevPath` nor `IsHomogeneousPath`), so it should be proved once next to
`separatedPath` and reused. `B01` never needed it, so nothing exists.

### N1 — (nit) `B02.temporalApprox` is a pure re-export
*Severity: nit. Location: `Remaining.lean:101-109`.*

`theorem temporalApprox := NSFormalization.Section4.B01.temporalApprox` restates the whole
type just to re-export it under `B02`. Harmless and well documented, but it duplicates a
statement that must now be kept in sync by hand. The split table already says the binding
may point straight at `B01.temporalApprox`; I'd make that the contract lane's choice and
keep the `B02` copy as documentation only.

### N2 — (nit) "19 fields" vs 20 structure fields
*Severity: nit. Location: `ATTEMPTS_REMAINING.md:104`, `REMAINING_SPLIT.md:5-6`.*

`HomogeneousApproxAPI` has **20** fields; `χ : Space → ℝ` is *data* supplied by the binding,
not a proof obligation. So the honest phrasing is "16 of the **19 proof obligations** (20
fields, of which `χ` is the carrier)". The arithmetic 11 + 5 + 3 = 19 is right; only the
wording is loose.

### N3 — (nit, pre-existing) stale spec line reference
*Severity: nit. Location: `Section4/B02/AnnularReal.lean:224` docstring.*

It cites `research/B02/Spec.lean:515-518` for `spatialApproxHomogeneous`, which now lives at
`:539-543` (lane 090's table already uses `:539`). Not this lane's file; flagged because the
contract lane will read that docstring. Similarly `LebesgueDatum.lean:446` cites
`Spec.lean:470` for `homogeneousDatumSub`, now `:490` — `ATTEMPTS_REMAINING.md:75` already
calls that ref stale, which is good practice.

## 4. Honesty of ATTEMPTS — 16/19 confirmed

I opened every cited declaration. All 11 pre-existing ones exist at the cited line under the
cited name:

| # | spec field | Spec:line | discharging theorem (verified at line) |
|---|---|---|---|
| 1 | `annularRestriction` | :302 | `B02/Annular.lean:240 annularRestriction` |
| 2 | `annularSmoothing` | :314 | `B02/Annular.lean:337 annularSmoothing` |
| 3 | `annularSchwartz` | :362 | `B02/AnnularReal.lean:205 annularSchwartz` |
| 4 | `lowFrequencyIntegrable` | :370 | `B02/LowFrequency.lean:56` |
| 5 | `lowFrequencyIntegral` | :378 | `B02/LowFrequency.lean:67` |
| 6 | `fourierSupBound` | :397 | `B02/LowFrequency.lean:124` |
| 7 | `lowHighSplit` | :421 | `B02/LowHigh.lean:200` |
| 8 | `lebesgueHomogeneousDatum` | :454 | `B02/LebesgueDatum.lean:405` |
| 9 | `homogeneousDatumSub` | :490 | `B02/LebesgueDatum.lean:446 isHomogeneousSliceDatum_sub_of_integrable` |
| 10 | `cutoffLebesgue` | :513 | `B02/Cutoff.lean:225` |
| 11 | `spatialApproxHomogeneous` | :539 | `B02/AnnularReal.lean:225` (unconditional) |
| 12-15 | `chi_smooth/one/vanishes/range` | :280-287 | `B02/Remaining.lean:67,72,78,83` |
| 16 | `temporalApprox` | :563 | `B02/Remaining.lean:101` (`= B01.temporalApprox`) |

This matches lane 090's conformance table (`ATTEMPTS_SIMP.md:189-199`) row for row, and
lane 090 records a conformance `example` for each of rows 1-11.

**Row 9 is not an inflated count.** I checked the spec text: `Spec.lean:460-496` carries a
⚠ block recording that the hypothesis-free `homogeneousDatumSub` was *refuted* (lane 068,
`REVIEW_U6.md` §4, totalization counterexample), and the field itself has been **amended** to
carry the two `Integrable (fun x => ψ x * (z x i : ℂ))` side conditions.
`isHomogeneousSliceDatum_sub_of_integrable` matches the amended field token-for-token. So the
16 are 16 genuine discharges, not one discharge of a weakened statement passed off as the
original. `ATTEMPTS_REMAINING.md:71-75` states this correctly and warns the contract lane not
to register the historical shape — good negative record.

The commands table at `ATTEMPTS_REMAINING.md:107-115` matches what I reproduced. The claim
"No approach that was tried failed to compile; the only failures are the three `M`
classifications" is consistent with what I see.

## 5. Should the B02 contract be registered now?

**Register a partial contract now — do not wait for the three `M` fields.** Three reasons.
First, `collaboration/work_items.json` shows `B02` with `"contracts": []`: eight merged
`B02` modules and not one registered statement. `make test` builds only registered contract
closures, so everything `B02` has proved is currently outside CI's drift protection —
registering is the thing that freezes it. Second, the 16 fields are stable and independent
of the three open ones: each has a conformance `example` and audits to
`[propext, Classical.choice, Quot.sound]`, and nothing in rows 6/7/8 can change any of
their statements. Third, the precedent is exact: `B01.bochner_partial` is
`BochnerPartialAPI`, itself the full `B01` API minus two fidelity-only displays, and it has
been carrying `B01` for several lanes. Model `verification/Contracts/V1/HomogeneousApprox.lean`
on `Contracts/V1/BochnerPartial.lean` field for field, name it
`HomogeneousApproxPartialAPI`, and bind `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff`
so the eventual R46 consumer sees one cutoff shared with `B01`. Two hard requirements for
that lane: register `homogeneousDatumSub` **only** in the integrability-carrying form and
copy the ⚠ refutation note into the contract docstring (a V1 contract is frozen, and the
false shape must never appear in it); and state in the contract's module docstring which
three obligations of `HomogeneousApproxAPI` are deliberately absent, as `BochnerPartial`
does for its two.

**Attack `separatedAssembly` (row 6) first.** It is the only `M` row on the critical path:
`approxCompactHomogeneous` (row 8) depends on it, while `annularPathApprox` (row 7) is not a
step of the manuscript's proof and feeds nothing (F3). It is self-contained, every side
condition and bookkeeping lemma it needs already exists, and `isSobolevPath_separated`
(`Separated.lean:182`) is a line-by-line template for the homogeneous twin. Before starting,
settle the `s`-range question from F1 — if `separatedAssembly` may carry `-3/2 < s`, the
uniqueness route cuts the work by more than half. Then row 8, whose only remaining novelty
is the realization-independent triangle-inequality glue. Row 7 last, or dropped from the API
if the contract lane agrees it is not a manuscript obligation.
