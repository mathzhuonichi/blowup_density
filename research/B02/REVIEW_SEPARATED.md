# Review — lane 103 (B02 `separatedAssembly`, the `-3/2 < s` route)

Reviewer run: worktree `.claude/worktrees/103-B02-separated-assembly`, commit `5b29ca8`
(3 files, 417 insertions, 0 deletions; no `Contracts/V1` or `Tests` file touched).
Scope: `formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean`,
`research/B02/{ATTEMPTS_SEPARATED.md,axioms_separated.lean}`.

## Verdict: **ACCEPT-WITH-NOTES**

The theorem is the spec field with exactly one inserted hypothesis `hs : -3 / 2 < s` and
nothing else changed; I confirmed that token by token and machine-confirmed it by
re-stating the field with fully qualified `Contracts.V1.Data` names and inhabiting it with
the theorem. It compiles silent, all six declarations carry only the three standard axioms,
and the conjunct that matters is genuinely pinned — `isHomogeneousSliceDatum_unique` forces
each given `A j` to be the canonical datum, so an arbitrary `A j` is not accepted. The
`-3/2 < s` trade-off is **acceptable and, I argue below, better than the spec's `∀ s : ℝ`**:
below `-3/2` the field's own hypothesis is essentially unsatisfiable, so the generality the
spec asks for is near-vacuous. Notes are one contract-lane decision (F1), two bookkeeping
staleness items (F2, F3) and two nits. Nothing blocks merge.

---

## 1. Compile / audit checks

All from `WT/verification` unless noted, after `. ../scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, one `lake` at a time.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` (WT root) | idempotent; ended `== OK`, every registered contract "checked; standard logical axioms only" |
| `lake build NSFormalization.Section4.B02.SeparatedAssembly` | final line `Build completed successfully (9881 jobs)`, exit 0. Warnings only from pre-existing `Source.*`/`Paper3.*` dependencies (`unnecessarySeqFocus`, `unusedVariables`, `SchwartzMap.smul_apply` / `ContinuousLinearMap.sub_apply` deprecations); **no** warning on any `SeparatedAssembly.lean` line |
| `lake env lean ../formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean` | **printed nothing**, exit 0 |
| `lake env lean ../research/B02/axioms_separated.lean` | exit 0; the conformance `example` elaborates; 6 declarations, each **exactly** `[propext, Classical.choice, Quot.sound]` — `schwartzAngularFourier_finsetSum_smul`, `homogeneousProfile_finsetSum_smul_apply`, `homogeneousDatum_finsetSum_smul`, `hasCompactSupport_sum_smul`, `isHomogeneousSliceDatum_sum_smul`, `separatedAssembly` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` on both files | hits are only docstring prose and the six `#print axioms` lines. No declaration, no `set_option` of any kind in the module |
| `make check` (WT root) | passed — architecture checks, `test_contract_policy.py` 13/13 OK, `check_work_queue.py` "30 work items … consistent" |
| `lake env lean /tmp/b02rev/bridge.lean` (reviewer scratch, not a repo file) | exit 0 — see §2 |

CI coverage: `formalization/lakefile.toml`'s `NSFormalization` `lean_lib` has no explicit
`roots`, so the new module is globbed and will be built by CI.

## 2. Statement fidelity

### 2.1 Diff against `research/B02/Spec.lean:582-600`

```
spec :582   separatedAssembly : ∀ (s : ℝ)              (J : ℕ) (φ : Fin J → ℝ → ℝ)
thm  :211   theorem separatedAssembly (s : ℝ) (hs : -3 / 2 < s) {J : ℕ} (φ : Fin J → ℝ → ℝ)
```

Every remaining token matches. The complete list of differences:

| # | spec | theorem | verdict |
|---|---|---|---|
| 1 | — | `hs : -3 / 2 < s`, immediately after `s` | **the one declared deviation** (F1) |
| 2 | `(J : ℕ)` explicit | `{J : ℕ}` implicit | cosmetic; the conformance `example` restores it explicit and absorbs it with `fun s hs _ φ …` |
| 3 | `h : Fin J → SpatialField` | `h : Fin J → Space → Space` | `abbrev SpatialField := Space → Space` (`Data.lean:99`, restated `HomogeneousWitness.lean:226`), reducible — same type (nit N1) |
| 4 | bare `MemForceCompact`, `IsHomogeneousPath`, `separatedField`, `separatedPath`, `forceTimeMeasure` | `D01.`- and `B01.`-qualified local restatements | definitionally equal, machine-checked below |

The six hypotheses (`ContDiff ℝ ∞ (φ j)`, `HasCompactSupport (φ j)`,
`tsupport (φ j) ⊆ Ioi (0 : ℝ)`, `ContDiff ℝ ∞ (h j)`, `HasCompactSupport (h j)`,
`IsHomogeneousSliceDatum s (h j) (A j)`) are token-identical and in the spec's order.

### 2.2 The three conjuncts against `Data.lean`

* `MemForceCompact` — `Data.lean:559` `ContDiff ℝ ∞ f ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f`. The theorem discharges it with `D01.memForceCompact_of_smooth_support` fed by `B01.contDiff_separatedField`, `B01.hasCompactSupport_separatedField`, `B01.tsupport_separatedField_pos` — the *same three calls* as `B01/Separated.lean:220`.
* `IsHomogeneousPath s` — `Data.lean:375` `∀ t : ℝ, 0 ≤ t → IsHomogeneousSliceDatum s (fun x => f (t, x)) (G t)`, restated verbatim at `HomogeneousWitness.lean:624`. `IsHomogeneousSliceDatum` (`Data.lean:367`) unfolds to `∃ U, IsSliceDistribution z U ∧ IsHomogeneousVectorDatum s U G`, and I diffed `IsSliceDistribution` (`Data.lean:298` vs `:232`), `IsHomogeneousDatum` (`:324` vs `:237`, **including** the load-bearing `Integrable` clause) and `IsHomogeneousVectorDatum` (`:358` vs `:249`) — all character-identical.
* `AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure` — `forceTimeMeasure = positiveTimeMeasure` (`Data.lean:118`, restated `:617`). Discharged by `B01.aestronglyMeasurable_separatedPath`, again the same call as `B01`.

### 2.3 Machine-confirmed bridges (reviewer scratch file, `exit 0`)

Every restated predicate is `rfl`-equal to the `Data.lean` one:

```lean
example : Data.IsHomogeneousSliceDatum  = D01.Homogeneous.IsHomogeneousSliceDatum  := rfl
example : Data.IsHomogeneousPath        = D01.Homogeneous.IsHomogeneousPath        := rfl
example : Data.IsSliceDistribution      = D01.Homogeneous.IsSliceDistribution      := rfl
example : Data.IsHomogeneousDatum       = D01.Homogeneous.IsHomogeneousDatum       := rfl
example : Data.IsHomogeneousVectorDatum = D01.Homogeneous.IsHomogeneousVectorDatum := rfl
example : Data.MemForceCompact          = D01.MemForceCompact                      := rfl
example : Data.forceTimeMeasure         = D01.forceTimeMeasure                     := rfl
example … : specSeparatedField φ h = B01.separatedField φ h := rfl   -- Spec.lean:217 verbatim
example … : specSeparatedPath  φ A = B01.separatedPath  φ A := rfl   -- Spec.lean:229 verbatim
```

and the spec field type written with **fully qualified `BlowupDensity.Contracts.V1.Data`
names** (so no ambient `open` can have silently redirected a predicate), carrying only the
extra `hs`, is inhabited by `B02.separatedAssembly` applied directly. This reproduces what
`research/B02/axioms_separated.lean` asserts and rules out the failure mode where the
conformance example accidentally states the *local* predicates: the Bindings bridge will be
defeq.

### 2.4 Could a weak or wrong statement satisfy this?

**No, on three counts.**

1. **The datum is pinned, not guessed.** `isHomogeneousSliceDatum_sum_smul`'s step `hAB`
   is `fun j => isHomogeneousSliceDatum_unique (hA j) (hBdatum j)`, i.e. the *unconditional*
   uniqueness (`HomogeneousWitness.lean:445`, no `hs`) is what identifies the given `A j`
   with `homogeneousVectorDatum hs (compactSchwartzComponents …)`. Without it the proof
   could not close, so an arbitrary `A j` is impossible: the theorem really asserts that the
   combination `∑ⱼ φⱼ(t) • Aⱼ` is *the* datum of the slice.
2. **The hypothesis class is inhabited.** I checked by example that for `-3/2 < s` and any
   smooth compact `z`, `(isHomogeneousSliceDatum_compact hs hzs hzc).1` produces an `A` with
   `Data.IsHomogeneousSliceDatum s z A`. So the six hypotheses are jointly satisfiable and
   the theorem is not vacuously true.
3. **The conclusion is checked at every `t ≥ 0`**, not a.e. — `intro t _` then the core
   lemma at `c := fun j => φ j t`, matching `separatedField`/`separatedPath` by `rfl`.
   Note the proof uses `hφpos`/`hφc` *only* for conjunct 1 and `hφs` *only* for conjunct 3;
   conjunct 2 holds for arbitrary time factors, which is correct and is why the core lemma
   is stated for a bare `c : Fin J → ℝ`.

## 3. The `-3/2 < s` question

### (a) Where it enters — confirmed: one place only

I traced every `hs` in the chain. In `SeparatedAssembly.lean`, `hs` reaches exactly
`homogeneousDatum hs`, `homogeneousDatum_ae hs`, `homogeneousVectorDatum hs`,
`homogeneousVectorDatum_coe hs` and `isHomogeneousSliceDatum_schwartz hs`. In `D01`:

* `homogeneousDatum hs φ := (memLp_homogeneousProfile hs φ).toLp _` (`:162`) — `hs` is a
  *parameter of the definition*, and its only mathematical content is the `MemLp` witness
  (`:153`, via `integrable_homogeneous_schwartz` `:109`, i.e. `∫_{|ξ|<1}|ξ|^{2s} dξ < ∞`);
* `homogeneousDatum_ae`, `realSymmetry_homogeneousDatum`, `mem_realSubspace_homogeneousDatum`,
  `homogeneousVectorDatum`, `homogeneousVectorDatum_coe` take `hs` **only** to name that
  object;
* `isHomogeneousDatum_homogeneousDatum` (`:277`) — the one place where an *independent* use
  could have hidden: its `Integrable` clause is transported along `homogeneousDatum_weight_ae`
  onto `integrable_schwartz_mul_angularFourier` (`:268`), which is **unconditional in `s`**.
  So no second `s`-restriction is smuggled in;
* `homogeneousDatum_unique` (`:325`) and `isHomogeneousSliceDatum_unique` (`:445`) carry no
  `hs` at all, as `ATTEMPTS_SEPARATED.md` §2 claims.

**Confirmed: `-3/2 < s` enters only through `memLp_homogeneousProfile`.**

### (b) Is the trade-off acceptable for the contract? Yes — and the spec is the odd one out

* `SplitRange s := -3/2 < s ∧ s ≤ 0` (`Spec.lean:237`, `HomogeneousPartial.lean:197`)
  implies `-3/2 < s` by `.1`, so **`approxCompactHomogeneous` (`Spec.lean:607`) is
  unaffected**, as is `manuscriptHomogeneousApproximation` (`q = 2`, `s = -1`).
  `SeparatedCompactHomogeneousDense` (`Spec.lean:653`) takes `s` as a parameter and is only
  ever instantiated through `approxCompactHomogeneous`, i.e. under `SplitRange`.
* Every other `s`-quantified field of the API already uses `SplitRange`: `lowHighSplit`
  (`:421`), `lebesgueHomogeneousDatum` (`:454`), `spatialApproxHomogeneous` (`:539`),
  `approxCompactHomogeneous` (`:607`). `separatedAssembly`'s `∀ s : ℝ` is the only
  unrestricted one, inherited from `B01`, where it is genuine (`IsSobolevDatum` is defined
  through the `ℂ`-CLM `angularRealization`, which exists at every `s`).
* The manuscript never needs `s ≤ -3/2` in the homogeneous realization.
  `02-preliminaries.tex:59` eq:homogeneous-realization fixes **only** `Ḣ^{-1}(R³)`;
  `appendix-b-embeddings.tex:44` restricts the completion to `0 < a < 3/2`;
  `04-whole-space.tex:251-260` writes the separated-sum step for "any of the preceding
  separable Hilbert spaces", and the only homogeneous one among them is `Ḣ^{-1}`.
  So the manuscript's own use is `s = -1`, comfortably interior.
* **Stronger point, and my main reason for accepting:** below `-3/2` the field's hypothesis
  is essentially unsatisfiable, so the spec's extra generality is near-vacuous. Sketch
  (argued, **not** formalized — offered to the contract lane as a reason, not as a Lean
  fact): `IsHomogeneousSliceDatum s (h j) (A j)` forces `ĥⱼ = |ξ|^{-s} G` distributionally
  with `G ∈ L²`; for smooth compact `hⱼ` the transform `ĥⱼ` is continuous, so `G = |ξ|^s ĥⱼ`
  a.e., and `∫_{|ξ|<1} |ξ|^{2s}|ĥⱼ|² = ∞` whenever `2s ≤ -3` and `ĥⱼ(0) ≠ 0`. So at
  `s ≤ -3/2` the only admissible profiles are those with a vanishing zeroth moment. Proving
  the field there would be proving a statement about an almost-empty hypothesis class.

### (c) ATTEMPTS' account of the verbatim-`∀ s` route — accurate and honestly sized

`ATTEMPTS_SEPARATED.md` §4 says the general route needs (i) a finite-`sum`/scalar-`smul`
combinator for `IsHomogeneousDatum` lifted to `IsHomogeneousVectorDatum`, (ii) the same for
`IsSliceDistribution` **with per-term integrability side conditions** discharged via
`B01.integrable_schwartz_mul`, and (iii) `angularFourierDistribution` linearity plus `𝓢'`
sum-smul evaluation. I checked each premise:

* only the four `_sub` forms exist — `isHomogeneousDatum_sub` `:534`,
  `isHomogeneousVectorDatum_sub` `:551`, `isSliceDistribution_sub` `:565`,
  `isHomogeneousSliceDatum_sub` `:585`. No `add`/`smul`/`sum`/`neg`/`zero` form. Confirmed;
* the totalization caveat is real and is the one that refuted the hypothesis-free
  `homogeneousDatumSub` (`Spec.lean:460-496` ⚠ block). Correctly cited;
* `B01.integrable_schwartz_mul` (`Separated.lean:73`), `B01.coe_sum_smul_apply` (`:90`),
  `B01.space_sum_apply` (`:98`) exist at the cited lines under the cited names and do the
  jobs claimed.

§5's three coding findings also check out: mathlib at this pin has **no** finite-sum
`HasCompactSupport` lemma (`Topology/Algebra/Support.lean` has `.mul_left/.mul_right/
.smul_left/.smul_right/.div/.abs` and nothing over `∑`); `SchwartzMap.smul_apply` is
deprecated (the build log emits exactly that warning from a `Paper3` dependency); `push_neg`
is deprecated (`Mathlib/Tactic/Push.lean:284,351` — "`push_neg` has been deprecated. Prefer
using `push Not` instead."). §6's command table matches what I reproduced. **No overclaim
found anywhere in ATTEMPTS.**

### (d) Recommendation to the contract lane: register now, with `-3/2 < s`

**Do not wait.** The three-field gap in `Contracts/V1/HomogeneousPartial.lean` (PR #99)
drops to two, and this statement is stable — the `M`-row it closes cannot change the shape
of any already-registered field.

Register it in a **V2** of `B02.homogeneous_partial` (V1 is frozen) with the hypothesis
spelled **`-3 / 2 < s`, not `SplitRange s`**:

* it is exactly what is proved; `SplitRange` would additionally assert `s ≤ 0`, which this
  proof does not need and which would silently discard the positive orders
  `0 < a < 3/2` that `appendix-b-embeddings.tex:44` uses;
* a consumer under `SplitRange` pays a one-token `.1`, so nothing downstream is harder;
* `HomogeneousPartial.lean` already restates `SplitRange`, so either spelling is available —
  this is a fidelity choice, not a plumbing one.

Two hard requirements for that lane, by the `homogeneousDatumSub` precedent:

1. run the two-agent fidelity check on the **amended** field (the deviation from
   `Spec.lean:582` is a mathematical change, not a rename), and
2. amend `research/B02/Spec.lean:582` itself to carry `-3/2 < s` with a ⚠ note recording
   that the `∀ s : ℝ` shape was *not* proved, is presumably true, needs the
   general-additivity route, and is near-vacuous below `-3/2` (§3(b)). Otherwise the spec and
   the contract disagree and the next reader re-opens this question.

## 4. Consistency

* **Imports canonical.** Two only: `NSFormalization.Section4.B01.Separated`,
  `NSFormalization.Section4.D01.HomogeneousWitness`. No `Contracts.*` import (correct —
  `formalization/` may not), no HeliCorgi `Formal.*`.
* **No restated definitions.** The module introduces six `theorem`s and zero `def`s; every
  predicate and object comes from `B01`/`D01`. This is the right side of the "one local
  restatement only" rule.
* **Conjuncts 1 and 3 reused, not copied.** Diffed against `B01/Separated.lean:220-233`:
  the B02 proof issues the identical `memForceCompact_of_smooth_support (contDiff_…)
  (hasCompactSupport_…) (tsupport_…_pos)` and `aestronglyMeasurable_separatedPath s φ A hφs`
  calls. No duplicated proof text.
* **The reusable core.** `isHomogeneousSliceDatum_sum_smul` (`:146`) is the piece
  `approxCompactHomogeneous` and any future homogeneous assembly should reuse. Exact
  statement:

  ```lean
  theorem isHomogeneousSliceDatum_sum_smul {s : ℝ} (hs : -3 / 2 < s) {J : ℕ}
      (c : Fin J → ℝ) (h : Fin J → Space → Space) (A : Fin J → RealVectorSobolev s)
      (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
      (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
      IsHomogeneousSliceDatum s (fun x => ∑ j, c j • h j x) (∑ j, c j • A j)
  ```

  Note it is stated for a bare coefficient vector `c`, with **no** time and **no** support
  condition — the right level of generality, and strictly more reusable than an
  `isHomogeneousPath_separated` would have been.
* **ATTEMPTS honesty.** Verified above (§3(c)); every cited declaration exists at the cited
  line under the cited name, and the two load-bearing negative claims (no sum/smul
  combinator; `-3/2 < s` unavoidable on this route) are correct.

## 5. Findings

### F1 — (major, by design; accepted) the theorem is not the verbatim spec field
*Severity: major-but-accepted. Location: `SeparatedAssembly.lean:211` vs `Spec.lean:582`.*

`hs : -3 / 2 < s` is inserted. This is disclosed in three places (module docstring §"The
homogeneous conjunct and the range of `s`", `ATTEMPTS_SEPARATED.md` §1/§3/§4,
`axioms_separated.lean` header) and was the route the lane was instructed to take. I accept
it on the analysis of §3(b): no consumer is affected, the manuscript never uses a
homogeneous space below `-3/2`, and the lost generality is near-vacuous.

*Fix:* none in this lane. The **contract lane** must act — register in V2 with `-3/2 < s`
and amend `Spec.lean:582` with a ⚠ note (§3(d)). Until that happens, the tree contains a
theorem whose name matches a spec field it does not prove verbatim; that is exactly the
situation the ⚠-note convention exists for.

### F2 — (minor) `REMAINING_SPLIT.md` row 6 is now stale and will mislead the contract lane
*Severity: minor. Location: `research/B02/REMAINING_SPLIT.md:57` (table row 6) and the
"Row 6 — `separatedAssembly`" paragraph.*

Row 6 still reads `M (~80-120 ln)` with blocker "no scalar-`smul`/finite-`sum` combinator
for `IsHomogeneousSliceDatum` exists — only `isHomogeneousSliceDatum_sub`", and its
paragraph describes only the general-additivity route. That blocker is no longer the whole
story: the row is now **done** on `-3/2 < s`, by a different route, in 228 lines. The
previous review's F1 fix ("add a paragraph to row 6 recording both routes and the `s`-range
trade-off") was never applied — this lane's commit touches 3 files and not this one.

*Fix:* one paragraph in row 6: route taken, the `-3/2 < s` hypothesis, the pointer to
`ATTEMPTS_SEPARATED.md` §3-4, and the reclassification of the remaining `∀ s : ℝ` gap.

### F3 — (minor, unfixable here) the frozen V1 contract docstring is now factually superseded
*Severity: minor. Location: `verification/Contracts/V1/HomogeneousPartial.lean:82-88`.*

The registered V1 docstring says `separatedAssembly` "needs a scalar-`smul`/finite-`sum`
additivity combinator for `IsHomogeneousSliceDatum` that does not exist". That was true when
PR #99 froze it; it now describes a route nobody needs to take. V1 is frozen and **must not
be edited**.

*Fix:* none here. The V2 lane must not copy that paragraph forward; it should say instead
that the field is proved on `-3/2 < s` by the uniqueness route and that the `∀ s : ℝ` shape
remains open (and near-vacuous).

### N1 — (nit) `Space → Space` where the spec and `B01` write `SpatialField`
*Severity: nit. Location: `SeparatedAssembly.lean:148,213` (`h : Fin J → Space → Space`).*

`SpatialField` is in scope (`HomogeneousWitness.lean:226`, opened via
`NSFormalization.Section4.D01.Homogeneous`) and is what `Spec.lean:583` and
`B01/Separated.lean:221` both write. Reducible `abbrev`, so no fidelity consequence — the
conformance example typechecks against `Data.SpatialField` — but a token-level diff against
the spec reads cleaner with the spec's own spelling.

### N2 — (nit) `hasCompactSupport_sum_smul` partly duplicates `B01.tsupport_finsetSum_subset`
*Severity: nit. Location: `SeparatedAssembly.lean:121` vs `B01/Separated.lean:136`.*

`B01.tsupport_finsetSum_subset` is already the "support of a finite sum ⊆ union of supports"
lemma, but its domain is hard-coded to `SpaceTime`, so it cannot serve a `Space → Space`
sum. Re-proving was the right call for this lane (B01 is merged and not to be edited here).
Confirmed mathlib supplies nothing (`Topology/Algebra/Support.lean` has no `∑` form).

*Fix:* not this lane. A future consolidation lane should generalize
`tsupport_finsetSum_subset`'s domain to an arbitrary topological space and derive both
`B01.hasCompactSupport_separatedField` and `B02.hasCompactSupport_sum_smul` from it.

### N3 — (nit, bookkeeping) commit trailer
*Severity: nit.* `5b29ca8` is signed `Co-Authored-By: Claude Fable 5.1`. Noted only so the
lead's `logs/AGENT_RUNS.csv` row records the worker model accurately.

## 6. What `approxCompactHomogeneous` needs now

With this lane merged, row 8 has all three of its mathematical inputs in the tree:
`temporalApprox` (`B02/Remaining.lean:101`, `= B01.temporalApprox`),
`spatialApproxHomogeneous` (`B02/AnnularReal.lean:225`, unconditional) and
`separatedAssembly` (this lane; its `-3/2 < s` is supplied by `SplitRange s |>.1`, so the
`s`-restriction costs row 8 nothing). The target,
`CompletedDenseHomogeneous q s forceClassCompact = CompletedDenseVia q s (IsHomogeneousPath s)
forceClassCompact` (`Data.lean:732,752`), asks for `f ∈ F_c` and a path `D` with
`IsHomogeneousPath s f D`, `AEStronglyMeasurable D forceTimeMeasure` and
`bochnerDatumENorm q s (D - b) < r` — and **not** `MemBochnerDatum q s D`, which is one
obligation fewer than one might expect. The assembly is therefore: `temporalApprox` at `r/2`
gives `J, φ, A'`; `spatialApproxHomogeneous` replaces each `A' j` by the homogeneous datum
`A j` of a physical `h j ∈ C_c^∞`; `separatedAssembly` turns `(φ, h, A)` into
`f := separatedField φ h` with its two realization conjuncts.

**The one genuinely new piece is the triangle-inequality gluing across the realization**, and
it is realization-independent — it mentions neither `IsSobolevPath` nor `IsHomogeneousPath`,
so it belongs next to `separatedPath` in `B01/Separated.lean` (or a shared module) and should
be proved once:

```
bochnerDatumENorm q s (separatedPath φ A - b)
  ≤ bochnerDatumENorm q s (separatedPath φ A - separatedPath φ A')
  + bochnerDatumENorm q s (separatedPath φ A' - b)                       -- eLpNorm triangle
bochnerDatumENorm q s (separatedPath φ A - separatedPath φ A')
  ≤ ∑ j, eLpNorm (φ j) q forceTimeMeasure * ‖A j - A' j‖ₑ                -- the fibre bound
```

which is the Lean form of the manuscript's own displayed error
`∑_{j≤J} |E_j|^{1/q} ‖b_j - h_j‖_X` (`04-whole-space.tex:257`). Ingredients, all present at
this pin: `separatedPath φ A - separatedPath φ A' = fun t => ∑ j, φ j t • (A j - A' j)`
(`Finset.sum_sub_distrib` + `smul_sub`); `eLpNorm_sum_le`
(`LpSeminorm/TriangleInequality.lean:127`, needs `1 ≤ q` and per-summand
`AEStronglyMeasurable`, free from continuity of `fun t => φ j t • v`); finiteness
`eLpNorm (φ j) q forceTimeMeasure < ⊤` from `Continuous.memLp_of_hasCompactSupport`
(`LpSpace/Indicator.lean:83`). The **one missing shape** is the exact scalar identity
`eLpNorm (fun t => φ j t • v) q μ = ‖v‖ₑ * eLpNorm (φ j) q μ` (function-times-constant-vector);
mathlib's `eLpNorm_const_smul_le` (`LpSeminorm/SMul.lean:43`) is the transposed case
(constant scalar times function), so this needs a short `enorm_smul` + `eLpNorm_const_mul`
argument rather than a citation.

**Size: 90-140 lines.** Roughly 50-70 for the fibre-bound lemma (the `ℝ≥0∞` bookkeeping and
the `eLpNorm_sum_le` side conditions are the bulk, not the analysis), 40-60 for the assembly.
The fiddly part is choosing `η_j := r / (2 * J * (1 + eLpNorm (φ j) q))` in `ℝ≥0∞` while
avoiding `⊤` and `0` and handling `J = 0` — budget for that, not for the estimate. Note that
`B01` never needed this glue (its `approxCompact` is monolithic, applying the source density
theorem directly, `B01/Compact.lean:155-181`), so nothing exists to copy and there is no
homogeneous analogue of that source theorem — which is precisely why row 8 must be assembled
from `temporalApprox` + `spatialApproxHomogeneous` + `separatedAssembly` rather than reused.
