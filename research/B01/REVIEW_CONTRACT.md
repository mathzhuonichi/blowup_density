# Lane 071 contract review — `B01.bochner_partial`

Reviewer: opus, lane 071. Worktree `.claude/worktrees/071-B01-partial-contract`,
commit `7059fbd` on base `4067c4f`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean content is correct and honest. Every registered field is token-for-token
the corresponding field of `research/B01/Spec.lean`; the binding contains no
proof content; the axiom test reports only the standard logical axioms; all four
gates pass. The five findings below are documentation defects only — wrong
`research/B01/Spec.lean` line numbers in prose, three of which are replicated
into the durable `verification/contracts.json` `scope` string. No Lean statement,
no binding, no build is affected, and none of them needs a rebuild to fix.

## 1. Gates

All commands run from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
no `-j`, one lake at a time.

### 1.1 `cd verification && lake build Contracts.V1.BochnerPartial Bindings.BochnerPartial Tests.BochnerPartial`

```
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
Build completed successfully (9891 jobs).
```

No errors. Warnings emitted during the build are pre-existing linter warnings in
`NSFormalization/{Paper3,Source}/*` and `NavierStokes/*`, none in any of the
three new files.

### 1.2 `make check`

```
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The architecture dump lists `Tests.BochnerPartial` in the checked module set.

### 1.3 `make test`

Full replay, every registered contract re-checked, including

```
info: Tests/BochnerPartial.lean:14:0: Contract BlowupDensity.Tests.checkedBochnerPartial: checked; standard logical axioms only
```

### 1.4 `make test-mutations`

```
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

### 1.5 `python3 experiments/check_contracts.py --base-ref origin/erenup/integration`

```
AssertionError: Removed stable specification: verification/Contracts/V2/MaximalPartial.lean
```

**This is base drift, not a lane defect.** The worktree branched from `4067c4f`,
which predates `A02.maximal_partial_v2` (lane 069) on `origin/erenup/integration`.
Verified that this is the *only* divergence:

```
$ git ls-tree -r --name-only origin/erenup/integration -- verification/Contracts  vs  HEAD
0a1
> verification/Contracts/V1/BochnerPartial.lean
15d15
< verification/Contracts/V2/MaximalPartial.lean

$ contract ids, base vs worktree
2d1
< A02.maximal_partial_v2
6a6
> B01.bochner_partial
```

One removal (the base-drift item), one addition (this lane). Re-running against
the true merge-base is clean:

```
$ python3 experiments/check_contracts.py --base-ref 4067c4f
rc=0
"registered_contracts": 14
```

The registry check will pass once the lane is rebased onto current integration.

### 1.6 Trust-boundary and hygiene greps

* `checkedBochnerPartial`: standard logical axioms only (1.1, 1.3). Independently,
  `#print axioms BlowupDensity.Bindings.bochnerPartial` →
  `[propext, Classical.choice, Quot.sound]`.
* Contract imports: `verification/Contracts/V1/BochnerPartial.lean:1` is
  `import Contracts.V1.Data` and nothing else — only `Contracts.*`, as required.
* `grep -n "maxHeartbeats\|sorry\|^axiom \|native_decide\|set_option"` over the
  three new files: **none found**.
* Frozen files: `git diff --name-only origin/erenup/integration...HEAD` touches
  only the three new `verification/{Contracts/V1,Bindings,Tests}/BochnerPartial.lean`
  files plus bookkeeping (`verification/contracts.json` append,
  `collaboration/TASKS.md`, `collaboration/tasks/B01.md`,
  `collaboration/work_items.json`, `research/B01/ATTEMPTS_CONTRACT.md`).
  **No file under `formalization/`, no `Contracts/V1/Data.lean`, no
  `research/B01/Spec.lean`, no pre-existing contract spec is modified.**

## 2. Statement fidelity

### 2.1 Fields vs `research/B01/Spec.lean`

Mechanical comparison: docstrings and comments stripped from
`Contracts/V1/BochnerPartial.lean:104-187` and from `Spec.lean:191-358`, the two
excluded fields removed from the spec side, structure names normalised, then
`difflib.unified_diff`:

```
IDENTICAL (byte-for-byte, after removing schwartzApprox/cutoffApprox and the structure name)
```

Field-by-field anchor confirmation against `Spec.lean`:

| field | `Spec.lean` | contract | verdict |
|---|---|---|---|
| `χ` | :195 | :108 | verbatim |
| `chi_smooth` | :197 | :110 | verbatim |
| `chi_one` | :199 | :112 | verbatim |
| `chi_vanishes` | :202 | :115 | verbatim |
| `chi_range` | :204 | :117 | verbatim |
| `spatialApprox` | :250 | :123 | verbatim |
| `temporalApprox` | :273 | :132 | verbatim |
| `separatedAssembly` | :292 | :145 | verbatim |
| `approxCompact` | :312 | :159 | verbatim |
| `completionRepresentative` | :320 | :165 | verbatim |
| `completionSurjective` | :325 | :170 | verbatim |
| `completionNorm` | :331 | :175 | verbatim |
| `completionCongr` | :337 | :180 | verbatim |
| `compactSubsetForceR` | :358 | :187 | verbatim |

### 2.2 The three restated `def`s

Byte-identical to the spec, with correct source lines cited in the contract at
`:77`, `:83`, `:89` (`research/B01/Spec.lean:140,147,158`):

* `separatedField` — `Spec.lean:140-142` = contract `:79-81`
* `separatedPath` — `Spec.lean:147-149` = contract `:85-87`
* `bochnerSpace` — `Spec.lean:158` = contract `:91`

`scaledCutoff` and `schwartzVector` are correctly *not* restated: they are
mentioned only by the two excluded fields.

### 2.3 Vocabulary

`set_option pp.fullNames true` on the elaborated field types shows only
`BlowupDensity.Contracts.V1.Data.*`, the three
`BlowupDensity.Contracts.V1.BochnerPartial.*` restatements,
`NSFormalization.Paper3.RealVectorSobolev` (the datum type `Data.lean` itself
uses) and Mathlib. **No `NSFormalization.Section4.*` name leaks into the
contract.** Spot-checked `Data.lean` targets are non-vacuous:
`CompletedDense` (:743) = `CompletedDenseVia q s (IsSobolevPath s)`,
`bochnerDatumENorm` (:205) = `eLpNorm`, `MemBochnerDatum` (:212) = `MemLp`,
`forceClassCompact` (:563) = `{f | MemForceCompact f}`.

### 2.4 Paper citations

All verified against the sources in this worktree:

* `04-whole-space.tex:218-260` — proposition at 218-229, `\begin{proof}` at 230,
  proof body 231-260. Contract's "`:218-229`, proof at `:231-260`" is right.
* `:235` — "choose `χ∈C_c^∞` equal to one on the unit ball and zero outside the
  ball of radius two, with `0≤χ≤1`". Matches all five `chi_*` docstrings.
* `:231-239,249` (`spatialApprox`) — 239 ends "proves spatial compact-smooth
  density in `H^s` for every real `s`"; 249 has "These constructions also prove
  the real vector-valued versions: take real parts". Correct.
* `:251-260` (`temporalApprox`) — the Bochner step. Correct.
* `:260` (`separatedAssembly`) — "Thus the finite sum `Σ_j φ_j(t)h_j(x)` … jointly
  smooth with compact support strictly inside `R³×(0,∞)`". Correct.
* `:219` (`approxCompact`) — prop:Renergy first clause. Correct.
* `:183` (`compactSubsetForceR`) — "Define the following two subclasses of
  `F_R`". Correct. `:194-196` is `cor:Rclasses` with the quote on `:195`;
  `02-preliminaries.tex:17` is `\begin{equation}\label{eq:Rclasses}`. Both correct.
* `:262` — the singular-force paragraph, correctly named in the scope string as
  *not* asserted.
* `research/section4/STATEMENTS.md:823-838` / `:823-830` / `:825-830` and
  `formalization/blueprint/DEPENDENCY_GRAPH.md:313-320` all point at the right
  blocks.

The only citation errors are to `research/B01/Spec.lean` itself; see findings 1-5.

## 3. Binding honesty

`verification/Bindings/BochnerPartial.lean`.

* **Zero `by` blocks.** `grep -n "\bby\b"` returns two hits, both inside
  docstring prose (`:14` "record by `rfl`", `:30` "shared by all adapters").
  No tactic block anywhere in the file.
* **Every field is `:= Local.theorem`, eta, or an explicit-`J` permutation:**
  * `spatialApprox`, `temporalApprox`, `approxCompact`,
    `completionRepresentative`, `completionSurjective`, `completionNorm`,
    `completionCongr` — bare identifiers, no arguments. Confirmed the local
    theorems carry exactly the field shapes:
    `Section4/B01/Spatial.lean:134`, `Temporal.lean:170`, `Compact.lean:155`,
    `Completion.lean:31,38,46,53`.
  * `separatedAssembly := fun s _J φ h A hφs hφc hφpos hhs hhc hA => …` — pure
    eta with `J` made explicit; `Separated.lean:220` has `{J : ℕ}` implicit, the
    contract field has it explicit. No proof content.
  * `compactSubsetForceR := fun _ hf => D01.memForceR_of_memForceCompact hf` —
    the set inclusion between two `{f | …}` sets unfolds to the pointwise
    implication. **This is the merged D01 theorem, not a re-proof:**
    `formalization/NSFormalization/Section4/D01/ForceClass.lean:189`
    (`theorem memForceR_of_memForceCompact {f : VelocityField} (h : MemForceCompact f) : MemForceR f`)
    is present verbatim on `origin/erenup/integration`, and this lane modifies no
    file under `formalization/` at all (see 1.6).
* **`χ := baseCutoff` with the vendor estimates.**
  `vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean`:
  `def baseCutoff` (:29), `baseCutoff_smooth` (:40), `baseCutoff_nonneg` (:42),
  `baseCutoff_le_one` (:44), `baseCutoff_eq_one {x} (hx : ‖x‖ ≤ 1)` (:46),
  `baseCutoff_eq_zero {x} (hx : 2 ≤ ‖x‖)` (:50). The binding's
  `fun _ hx => … hx` wrappers exist only to make the implicit `x` explicit, and
  `chi_range := fun x => ⟨baseCutoff_nonneg x, baseCutoff_le_one x⟩` is the
  `Set.Icc` pair. Hypothesis directions match the contract exactly. It is a
  genuine cutoff, not a degenerate stand-in (`baseCutoff_tsupport` at :57 gives
  `tsupport baseCutoff = closedBall 0 2`).
* **The three `rfl` bridges pair the right definitions.**
  * `bochnerPartial_separatedField_eq` : contract `separatedField`
    = `NSFormalization.Section4.B01.separatedField`
    (`Section4/B01/Separated.lean:58-60`, same body `fun z => ∑ j, φ j z.1 • h j z.2`).
  * `bochnerPartial_separatedPath_eq` : contract `separatedPath`
    = `Section4/B01/Separated.lean:63-65` (`fun t => ∑ j, φ j t • A j`).
  * `bochnerPartial_bochnerSpace_eq` : contract `bochnerSpace`
    = `Section4/B01/Compact.lean:103`
    (`Lp (RealVectorSobolev s) q forceTimeMeasure`).
  Each pairs the contract object with the module the corresponding theorems are
  stated in; all three hold by `rfl`, i.e. the bridge is definitional, not a
  reinterpretation.

## 4. Round trip

Scratch file elaborated with `lake env lean` from `verification/` (never written
into the worktree; deleted afterwards; `git status --porcelain` clean).

* `Bindings.bochnerPartial.approxCompact q hq1 hq2 s` accepted at the goal
  `CompletedDense q s forceClassCompact` stated purely in
  `Contracts.V1.Data` names.
* `Bindings.bochnerPartial.temporalApprox q hq1 hq2 s b hb η hη` accepted at the
  full existential goal restated by hand in contract vocabulary
  (`MemBochnerDatum`, `bochnerDatumENorm`, `separatedPath`, Mathlib `ContDiff` /
  `HasCompactSupport` / `tsupport` / `Ioi`).
* The `temporalApprox` output destructured and re-packaged — the data is usable
  downstream, not an opaque conclusion.
* `#check` with `pp.fullNames` confirms no implementation namespace in either
  conclusion (section 2.3).
* `#print axioms BlowupDensity.Bindings.bochnerPartial` →
  `[propext, Classical.choice, Quot.sound]`.

Nothing in either conclusion mentions `NSFormalization.Section4.*`.

## 5. Scope string

`verification/contracts.json`, `B01.bochner_partial`. Checked clause by clause
against the registered fields — it is honest.

* Field list matches the structure exactly (14 fields, all named).
* Discharge attribution correct: `Section4/B01/{Compact,Completion,Separated,Spatial,Temporal}.lean`
  and `Section4/D01/ForceClass.lean`, plus the vendor `baseCutoff` estimates
  (all five named correctly).
* Binding shape described accurately (`separatedAssembly` with `J` explicit;
  `compactSubsetForceR` as pointwise membership repackaged; `chi_range` as the
  `nonneg, le_one` pair; three `rfl` bridges).
* **Exclusions all declared:** `schwartzApprox`, `cutoffApprox`, and the
  `SeparatedCompactDense` packaging, each with a reason. The reason given for the
  first two — "`spatialApprox` is the only spatial input `approxCompact` uses" —
  is confirmed by `Compact.lean:155ff`, which calls `spatialApprox` and no
  Schwartz/cutoff display.
* Negative clause "Nothing here asserts the singular-force threshold `s < s_q`
  (`04-whole-space.tex:262`), the breakdown condition `T^ν_{max,R}(a,f) ≤ T`, or
  any PDE norm estimate" is true: `approxCompact` is
  `∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, CompletedDense q s forceClassCompact`, with no
  threshold and no breakdown hypothesis.

Worth recording for the lead, though not a defect: the registered `approxCompact`
is *wider in range* than the manuscript's `prop:Renergy` display (all
`q ∈ [1,∞)`, all real `s`, vs the paper's `q ∈ {1,2}`, `s < s_q`) and *narrower
in content* (it drops the "with `T^ν_{max,R}(a,f) ≤ T`" qualifier). This is
exactly what `Spec.lean:303-311` documents and what the scope string discloses;
`R46` is the consumer that must re-impose the breakdown condition from `R41D`.

## Findings

1. **Minor (documentation, replicated into the registry).**
   `verification/Contracts/V1/BochnerPartial.lean:35` cites the excluded
   `schwartzApprox` as `research/B01/Spec.lean:225`. The declaration is at
   **`:219`**; line 225 is inside *`cutoffApprox`*'s docstring
   ("and any nonnegative integer `m`, Leibniz' rule shows"). It has never been at
   :225 in any revision of `Spec.lean` (:203 in draft `278a116`, :219 since the
   reviewed `5882acb`). The same wrong number appears in the
   `verification/contracts.json` `scope` string ("Spec.lean:225") and in
   `research/B01/ATTEMPTS_CONTRACT.md`.
   *Fix:* replace `:225` with `:219` in all three places.

2. **Minor (documentation, replicated into the registry).**
   Same file `:37` cites `cutoffApprox` as `research/B01/Spec.lean:257`. The
   declaration is at **`:234`**; line 257 is inside *`temporalApprox`*'s
   docstring. Also wrong in the `contracts.json` scope string and in
   `ATTEMPTS_CONTRACT.md`.
   *Fix:* replace `:257` with `:234` in all three places.

   (Findings 1 and 2 share one cause: each citation landed one field too late.
   They are the pointers a future reader follows to check *what was left out*,
   which is why they are worth correcting even though no Lean is affected.)

3. **Cosmetic.** `verification/Contracts/V1/BochnerPartial.lean:43` cites
   `SeparatedCompactDense` as `research/B01/Spec.lean:396`. The `def` is at
   **`:405`**; `:396` lands inside its docstring, so the pointer is in the right
   block but not on the declaration. Also `:396` in `ATTEMPTS_CONTRACT.md`.
   *Fix:* `:405`.

4. **Cosmetic.** `verification/Contracts/V1/BochnerPartial.lean:9` gives the
   source structure as `BochnerApproxAPI` (`:191-360`). The structure spans
   **`:191-358`**; `:360` is the `/-! ## 3. Derived statements -/` header.
   *Fix:* `:191-358`.

5. **Cosmetic (research note only, not in any registered artefact).**
   `research/B01/ATTEMPTS_CONTRACT.md` cites `scaledCutoff` at `Spec.lean:130`
   (actual **`:123`**) and `schwartzVector` at `:134` (actual **`:132`**).
   *Fix:* `:123` and `:132`.

No finding touches a Lean statement, a binding assignment, an axiom set, or a
build. None requires a rebuild; all five are text edits.
