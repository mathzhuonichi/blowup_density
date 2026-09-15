# D01 — registering `D01.datum_lemmas` (lane 034)

Record for the contract-registration lane: which theorems of the four merged D01 modules were
bundled into `verification/Contracts/V1/DatumLemmas.lean`, which were deliberately left out and
why, and what did not fit.  Positive and negative results both, per `CLAUDE.md` rule 4.

Files produced: `verification/Contracts/V1/DatumLemmas.lean` (spec, `DatumLemmasAPI`),
`verification/Bindings/DatumLemmas.lean` (23 `rfl` bridges + the instance),
`verification/Tests/DatumLemmas.lean` (`checkedDatumLemmas` + `checkAxioms`), and the
`D01.datum_lemmas` entry of `verification/contracts.json`.  No proof module was touched: this
lane adds no mathematics, and the binding is `:= Upstream.theorem` (or a `fun … =>` argument
permutation) in every field.

## 1. What is bundled — theorem → field

`D` = `NSFormalization.Section4.D01`, `H` = `NSFormalization.Section4.D01.Homogeneous`.
"paper" = the manuscript location the field's docstring cites.

### `SmoothDatum.lean` (lane 020, `REVIEW_L2.md`) — jets ⟹ datum

| theorem (file:line) | field | paper |
|---|---|---|
| `D.exists_isSobolevDatum_of_contDiff_memLp` `SmoothDatum.lean:290` | `smoothJets_exists_datum` | `01-introduction.tex:94`, `02-preliminaries.tex:12` |
| `D.sobolevENorm_ne_top_of_contDiff_memLp` `:315` | `smoothJets_sobolevENorm_ne_top` | `01-introduction.tex:94` |
| `D.exists_isSobolevDatum_fderiv` `:400` | `smoothJets_exists_datum_fderiv` | `appendix-a-local-theory.tex:120-123` (the `‖∇u₂‖_∞` consumer) |
| `D.memHInfty_of_contDiff_memLp` `:299` | the `←` half of `memHInfty_iff_smoothJets` | `02-preliminaries.tex:12` eq:Rinitial |

The real-order form is registered, not the integer-order one: `01-introduction.tex:94` defines
`H^s` at every real `s`, `04-whole-space.tex:8` uses the non-integer `s_q = 2/q - 3/2`, and the
module proves the real-order statement with no extra hypothesis.

### `DatumToJets.lean` (lane 025, `REVIEW_DATUM_TO_JETS.md`) — datum ⟹ jets

| theorem | field | paper |
|---|---|---|
| `D.jetSobolevConst` / `_pos` `:316,318` | `Cjet` / `Cjet_pos` | `appendix-a-local-theory.tex:10` |
| `D.memHInfty_iff_smoothSquareIntegrableJets` `:298` | `memHInfty_iff_smoothJets` | `02-preliminaries.tex:12` |
| `D.memLp_of_isSobolevDatum` `:267` | `memLp_of_isSobolevDatum` | `01-introduction.tex:143` eq:Enorm |
| `D.jetSobolevENorm_le_sobolevENorm` `:343` | `jetSobolevENorm_le_sobolevENorm` | `01-introduction.tex:85-86`, `04-whole-space.tex:53` |
| `D.memHInfty_dirDeriv` `:488` | `memHInfty_partialDeriv` | `appendix-a-local-theory.tex:120-123` |
| `D.memHInfty_jetClasses` `:458` (first conjunct) | `initialClass_smoothJets` | `02-preliminaries.tex:12` |
| `D.smoothSquareIntegrableJets_slice` `:396` | `solution_slice_smoothJets` | `02-preliminaries.tex:29-30` |
| `D.contDiff_pressureGradient_slice` `:504` | `solution_slice_pressureGradient_contDiff` | `02-preliminaries.tex:101` |

`memHInfty_iff_smoothJets` is the single field that discharges every "a consumer holding
`MemHInfty` still needs unit L2" sentence in `Contracts/V1/GradientL6.lean` and
`Contracts/V1/BoundedRepresentative.lean`, and `jetSobolevENorm_le_sobolevENorm` is the clause
`BoundedRepresentative.lean`'s docstring says it deliberately does not state.

### `ForceClass.lean` (lane 028, `REVIEW_FORCECLASS.md`)

| theorem | field | paper |
|---|---|---|
| `D.isSobolevDatum_unique` `ForceClass.lean:286` | `isSobolevDatum_unique` | `Data.lean:145` (unit L1) |
| `D.isSobolevDatum_add` `:261` | `isSobolevDatum_add` | — (`Data.lean:148-155` caveat) |
| `D.isSobolevPath_add` `:320` | `isSobolevPath_add` | `research/R42/COMPARISON.md` §4.3 |
| `D.schwartzPairable_slice_of_memForceR` `:309` | `memForceR_slice_integrable` | `Data.lean:153` |
| `D.memForceR_of_memForceCompact` `:189` | `memForceCompact_memForceR` | `04-whole-space.tex:185,198` |
| `D.memForceR_add` `:330` | `memForceR_add` | `04-whole-space.tex:51` |
| `D.memForceR_add_compact` `:344` | `memForceR_add_compact` | `04-whole-space.tex:51`, `STATEMENTS.md:270` |
| `D.memForceCompact_add` `:358` | `memForceCompact_add` | `04-whole-space.tex:185` |
| `D.memForceCompact_of_smooth_support` `:352` | `memForceCompact_of_smooth_support` | `Correction.lean:426,429,440` |
| `D.memForceR_of_agreesOnFuture` `:380` | `memForceR_of_agreesOnFuture` | `02-preliminaries.tex:24` |
| `D.memForceR_of_compact_difference` `:401` | `memForceR_of_compact_difference` | `04-whole-space.tex:32-33` |
| `D.memForceR_of_force_formula` `:428` | `memForceR_of_force_formula` | `04-whole-space.tex:48,51` |

### `HomogeneousWitness.lean` (lane 024, `REVIEW_HOMOGENEOUS.md`)

| theorem | field | paper |
|---|---|---|
| `H.exists_isHomogeneousSliceDatum` `:473` | `schwartz_exists_homogeneousDatum` | `02-preliminaries.tex:58-69` |
| `H.isHomogeneousSliceDatum_compact` `:519` | `compact_exists_homogeneousDatum` | `04-whole-space.tex:249` |
| `H.isHomogeneousSliceDatum_unique` `:445` | `isHomogeneousSliceDatum_unique` | `02-preliminaries.tex:70` (unit L7) |
| `H.homogeneousENorm_schwartz_ne_top` `:463` | `homogeneousENorm_schwartz_ne_top` | `02-preliminaries.tex:63` |
| `H.isHomogeneousSliceDatum_sub` `:585` | `isHomogeneousSliceDatum_sub` | `research/B02/Spec.lean:470` |
| `H.integrable_schwartz_mul_component` `:597` | `schwartz_integrable_component` | — (discharger) |
| `H.isHomogeneousPath_compact` `:658` | `compact_exists_homogeneousPath` | `04-whole-space.tex:226` |
| `H.bochnerDatumENorm_eq_eLpNorm_slice` `:667` | `bochnerDatumENorm_eq_eLpNorm_slice` | `04-whole-space.tex:212,219,226` |
| `H.eLpNorm_slice_le_forceHomogeneousENorm` `:683` | `eLpNorm_slice_le_forceHomogeneousENorm` | `04-whole-space.tex:219` |

## 2. Left out, and why

### 2.1 Statement names an implementation definition the contract may not import

These could not be stated at all in the contract's vocabulary; restating the definitions in the
spec (the `CLAUDE.md` "逐字重写 + `rfl` 桥" route) would mean copying whole construction
modules — the physical Bessel iterate, the angular datum builder, the I03 path — into a
specification whose purpose is to say what the *paper* asserts.  None of them is a statement
about a manuscript object.

* `SmoothDatum.lean:260,266,278,332,349,391` — `smoothAngularDatum` and everything stated about
  it, including `norm_smoothAngularDatum_le` (bounds the datum norm by
  `frequencyUnit ^ |s| * √(∑ᵢ ‖(iteratedBesselField m (componentField i A)).toLp‖²)`;
  `iteratedBesselField` is `Source.PhysicalBesselSobolev`, `componentField` is
  `Source.PhysicalIntegerSobolev`, neither on `CONTRACT_CANONICAL_MODULES`).
* `SmoothDatum.lean:98-235` — the conjugation / `IsRealField` / `realSymmetry_*` section: internal
  to the construction.
* `DatumToJets.lean:140-236` — `cyclesComponentOfAngular`, `loweredComponent`, `jetOfDatum`,
  `jetDatumConst`: the transport machinery.
* `DatumToJets.lean:306` `exists_smoothL2Field_of_memHInfty` — concludes
  `∃ B : EulerLpTranslation.SmoothL2Field Space, B.field = z`, i.e. the *vendor's* jet carrier.
  `memHInfty_iff_smoothJets` is the same content on the contract's own class, and the carrier is
  an implementation type.
* `ForceClass.lean:107-135` — `contDiff_angularPath` and the transport chain; names
  `I03.angularPath`.
* `HomogeneousWitness.lean:99-224,268-424` — `homogeneousDatum`, `homogeneousProfile`,
  `homogeneousVectorDatum` and their properties.  In particular
  `homogeneousENorm_schwartz` (`:456`), which says `homogeneousENorm s φ = ‖homogeneousDatum hs φ‖ₑ`;
  only its corollary `≠ ⊤` (`:463`) is statable, and that is what is registered.

### 2.2 Statable, but a strict consequence of two registered fields

Registering them would double-count the debt (the `A03.tame_products` precedent,
`TameProduct.lean` §4 note on `memHInfty_component` / `memHInfty_partialDeriv`).

* `DatumToJets.lean:287` `memHInfty_jets` — the `→` half of the registered iff.
* `DatumToJets.lean:130` `smoothJetsUpTo_of_allOrders` — already a registered field of
  `A03.bounded_representative` (`BoundedRepresentativeAPI.smoothJetsUpTo_of_allOrders`).
* `DatumToJets.lean:366,378` `contDiff_slice`, `contDiff_slice_scalar` — the first conjunct of
  `solution_slice_smoothJets`, resp. the input of the registered pressure clause.
* `DatumToJets.lean:411,429,443` `smoothJetsUpTo_slice`, `slice_jets_and_bound`,
  `slice_allOrderJets_and_bound` — conjunctions of `solution_slice_smoothJets` with
  `BoundedRep.smoothJetsUpTo_of_allOrders` resp. `jetSobolevENorm_le_sobolevENorm`.
* `DatumToJets.lean:479` `smoothSquareIntegrableJets_dirDeriv` — lane 019's `A05.SmoothL2.dir`
  verbatim; its datum form `memHInfty_partialDeriv` is registered.
* `DatumToJets.lean:458` `memHInfty_jetClasses` second conjunct — same reason.
* `ForceClass.lean:369,394` `memForceR_congr`, `memForceR_of_eq` — one direction, resp. a special
  case, of the registered `memForceR_of_agreesOnFuture`.
* `HomogeneousWitness.lean:325,437,534,551,566` — the component-level `homogeneousDatum_unique`,
  `isSliceDistribution_unique`, `isHomogeneousDatum_sub`, `isHomogeneousVectorDatum_sub`,
  `isSliceDistribution_sub`: the vector-level versions are registered.
* `HomogeneousWitness.lean:389,418,486` `isHomogeneousSliceDatum_schwartz`,
  `enorm_homogeneousVectorDatum`, `enorm_of_isHomogeneousSliceDatum` — the first two are the two
  conjuncts of the registered `schwartz_exists_homogeneousDatum`; the third follows from it and
  `isHomogeneousSliceDatum_unique` in one step.

### 2.3 Statable only in a weakened form whose binding would need new proof

* `HomogeneousWitness.lean:692` `forceHomogeneousENorm_eq_of_aestronglyMeasurable`.  Its
  hypothesis is `AEStronglyMeasurable (compactHomogeneousPath hs hf hc) forceTimeMeasure` —
  the implementation's own path.  The contract-vocabulary restatement would be
  `(∃ G, IsHomogeneousPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure) →
  forceHomogeneousENorm q s f = eLpNorm (…) q forceTimeMeasure`, and discharging *that* needs a
  three-step `le_antisymm` / `iInf_le_of_le` assembly in the binding, i.e. new mathematics in the
  adapter layer, which the lane brief and `CLAUDE.md` forbid.  **Not registered.**  Its two
  ingredients are: `bochnerDatumENorm_eq_eLpNorm_slice` (every path has the same Bochner norm)
  and `eLpNorm_slice_le_forceHomogeneousENorm` (the unconditional lower bound), both registered,
  so a consumer that produces a measurable path gets the equality in two lines.  The missing
  measurability is I03's U7c blocker (`REVIEW_HOMOGENEOUS.md`, "What remains").

### 2.4 Finer than the registered clause, at the cost of a second constant family

* `DatumToJets.lean:241,249,276,321` — `memLp_iteratedFDeriv_of_isSobolevDatum`,
  `eLpNorm_iteratedFDeriv_le_of_isSobolevDatum`, `eLpNorm_le_of_isSobolevDatum`,
  `jetSobolevENorm_le_of_isSobolevDatum`.  These are per-jet-order bounds against a *chosen*
  datum, with the two-index constant `jetDatumConst j m`.  The registered
  `jetSobolevENorm_le_sobolevENorm` is the sum over `j ≤ m` against the *infimum* over data — the
  form `research/A03/REVIEW_CONTRACT.md` §6(3) asks for and the only form a consumer uses — and
  it dominates each of them up to the constant.  Registering the per-order family would add a
  `ℕ → ℕ → ℝ` constant field to the record for no consumer.  `memLp_of_isSobolevDatum` *is*
  registered separately, because it needs a single order where the iff needs all of them.

## 3. Things that did not fit, and notes for the lead

1. **`-3/2` must be spelled `-3 / 2`.**  The proof modules write the hypothesis as `-3 / 2 < s`,
   which elaborates to `(-3) / 2`, not `-(3 / 2)`; the two are not definitionally equal over `ℝ`,
   so the contract copies the module spelling exactly.  Writing `-(3/2 : ℝ) < s` in the spec makes
   every homogeneous binding fail to unify.
2. **`Data.lean` now understates what is proved, in two places.**  `Data.lean:318-321` predicts
   `-3/2 < s` as a hypothesis of unit L7; `isHomogeneousSliceDatum_unique` needs no constraint on
   `s` at all (`REVIEW_HOMOGENEOUS.md` ruling (b)).  And the `Data.IsHomogeneousDatum` docstring's
   `s < 3/2` is only a sufficient Cauchy-Schwarz route, not a hypothesis of anything registered.
   `Contracts/V1/Data.lean` is frozen, so both are recorded in `DatumLemmas.lean`'s docstring
   instead; a V2 of `Data.lean`, if one is ever cut, should fix the two sentences.
3. **`g ∈ F_R` is not projectable from any contract.**  `memForceR_of_compact_difference` and
   `memForceR_of_force_formula` both take `MemForceR g` as a hypothesis, because
   `Data.ClassicalSolutionR` has no force-class field and neither does `InsertionFamilyAPI`
   (`REVIEW_FORCECLASS.md` issue 1).  R42 must carry it.
4. **Route 2 of the inserted force is registered but not yet dischargeable.**
   `memForceR_of_force_formula` needs `MemForceCompact (ScalingAPI.F ε)`, and nothing transports
   `PacketAPI.force_smooth` / `force_support` through `dilateField` (`REVIEW_FORCECLASS.md` issue 2).
   It is registered anyway because it is the manuscript's own display
   (`04-whole-space.tex:48,51`); route 1 (`memForceR_of_compact_difference`) is the one R42 can
   use today, and the field docstring says so.
5. **Two mechanical failures, both in the spec file, both fixed.**
   (a) `/-! ### … -/` section-doc comments **cannot** appear inside a `structure` body: the
   parser closes the structure and then reports `unexpected identifier; expected 'lemma'` once per
   remaining field (31 errors from four comments).  The four group headers are ordinary `--` line
   comments instead.  `Contracts/V1/TameProduct.lean` uses `/-! … -/` only between top-level
   declarations, which is why the pattern does not show the problem.
   (b) `RealVectorSobolev` is **not** in scope from `open BlowupDensity.Contracts.V1.Data`:
   `Data.lean`'s `open NSFormalization.Paper3` (`Data.lean:88`) does not leak past its own
   namespace.  With `autoImplicit` on, the first symptom is the unhelpful
   `Function expected at RealVectorSobolev … but this term has type ?m.5`.  The fix is
   `open NSFormalization.Paper3 (RealVectorSobolev)` in the spec — an `open`, not an `import`, so
   `check_contracts.py`'s direct-import rule is untouched (the spec's only three imports are
   `Contracts.V1.Data`, `Contracts.V1.GradientL6`, `Contracts.V1.BoundedRepresentative`).
6. **Name resolution was checked, not assumed.**  `#check` on four field projections confirms that
   the unqualified `SmoothSquareIntegrableJets` in the spec is `Contracts.V1`'s (the A05/GradientL6
   class, not `BoundedRep`'s identically-spelled copy), `partialDeriv` is `Contracts.V1.partialDeriv`
   (GradientL6), `jetSobolevENorm` is `BoundedRep`'s, and every remaining name is `Data`'s.
7. **No `maxHeartbeats` bump was needed** anywhere: the contract, the binding and the test all
   elaborate at the default budget.  The binding's 23 `rfl` bridges are all definitional unfoldings
   at default transparency.
8. **The closure grows by essentially nothing.**  `check_contracts.py` reports 1126 modules in the
   `D01.datum_lemmas` closure against 1120 for `A03.tame_products`, which was already registered,
   so `make test` compiles no meaningful new surface.
9. **The bridges were the reviewers' top follow-up.**  All four reviews
   (`REVIEW_L2.md` §7, `REVIEW_DATUM_TO_JETS.md` §6(1), `REVIEW_HOMOGENEOUS.md` issue 2,
   `REVIEW_FORCECLASS.md`) record that the definitional agreements between the restated
   `Data.lean` declarations and the contracts lived only in deleted scratch files.
   `Bindings/DatumLemmas.lean` §1 commits 23 of them, so CI now fails if either side drifts.

## 4. Gates

All run in the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| command | result |
|---|---|
| `cd verification && lake build Contracts.V1.DatumLemmas Bindings.DatumLemmas Tests.DatumLemmas` | **exit 0**, `Build completed successfully (9890 jobs)`; **zero** diagnostics mentioning any of the three new files apart from the acceptance `info` |
| `make check` | **exit 0** — plan check, `check_contracts` (10 contracts), `test_contract_policy` (13 tests), `check_work_queue` (30 items) |
| `make test` | **exit 0**, 9951 jobs; `Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only` |
| `make test-mutations` | **exit 0** — `implementation_refactor: accepted`, `admitted_proof` / `extra_axiom` / `weakened_hypothesis` all `rejected as required` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | **exit 0**, `base_compatibility_checked: true`, `registered_contracts: 10`, `D01.datum_lemmas` closure 1126 modules |
| `#print axioms` (scratch, deleted) | `'BlowupDensity.Tests.checkedDatumLemmas' depends on axioms: [propext, Classical.choice, Quot.sound]`; same for `BlowupDensity.Bindings.datumLemmas` |

Warnings seen during the build all come from *replayed* dependencies and are the same set the four
D01 reviews recorded: `Source/RealSobolev`, `Source/PhysicalBesselSobolev:134` (an `info`, the
`ring`/`ring_nf` hint), `Source/ViscosityPacket:34`, `Paper3/SpatiallyCompactTime`,
`Paper3/RealPositiveDensity`, `Paper3/RealVectorPositiveDensity:29`,
`Paper3/SobolevDirectionalDerivative:103`.  None originates in a file this lane adds.

## 5. Review fixes (lane 034, after `research/D01/REVIEW_CONTRACT.md`, verdict ACCEPT-WITH-NOTES)

The review found no mathematical defect: 33/33 bindings are `:= Upstream.theorem` or an argument
permutation, all 31 upstream `Section4/D01/*.lean:NNN` cites are exact, and both statements it
stress-tested (`isHomogeneousSliceDatum_unique` unconditional in `s`,
`memHInfty_iff_smoothJets` on the same jet class the A05/A03 contracts use) hold.  All notes were
documentation-level plus one optional bridge.  Applied:

| note | change |
|---|---|
| **1** (LOW) | `Contracts/V1/DatumLemmas.lean`, `## Conventions` → "The homogeneous range": the `s < 3/2` **upper** bound is `Data.lean:307-317` (the Cauchy-Schwarz passage, "finite at the origin exactly when `2s < 3`"), not `:318-321`, which is the **lower**-bound/unit-L7 passage.  Re-cited.  The two *correct* uses of `318-321` — the module docstring's unit-L7 sentence and the `isHomogeneousSliceDatum_unique` field docstring — were left alone. |
| **2** (LOW) | Paper cites bumped: `04-whole-space.tex:48` → `:49` (the `g_ε = g + H_ε + F_ε` display; three occurrences — `## Consumers`, `memForceCompact_add`, `memForceR_of_force_formula`), `:33` → `:32` ("there are `g_ε ∈ F_R`"; `memForceR_of_compact_difference`), `:198` → `:194` (`cor:Rclasses`; `memForceCompact_memForceR`).  Each verified by reading the `.tex`. |
| **3** (LOW) | Sibling-contract cites bumped to the `def`/field lines: `GradientL6.lean:104` → `:106` (`SmoothSquareIntegrableJets`, in the binding), `GradientL6.lean:88` → `:83` (`partialDeriv`, in both the contract and the binding), `Data.lean:654` → `:647` (`ClassicalSolutionR.pressure_gradient`, twice in the contract). |
| **4** (LOW) | The module docstring's `forceHomogeneousENorm` bullet said the conditional equality "cannot be stated without the implementation's own path", contradicting §2.3 above.  Rewritten to §2.3's reason: the *upstream theorem*'s hypothesis names `compactHomogeneousPath`, and the contract-vocabulary form is statable but would need a proof in the binding, which the binding rule forbids. |
| **5** (INFO) | §3 item 7 said "21 `rfl` bridges"; now 23 (the count is 23 after note 8, and the header and item 9 agree). |
| **8** (INFO) | Added the 23rd bridge, `datumLemmas_tameProduct_smoothJets_eq`, identifying the local jet class with `Contracts.V1.TameProduct.SmoothJets` (`TameProduct.lean:207`) — the fourth same-body copy, used by `A03.tame_products`.  It carries no `DatumLemmasAPI` field (this contract feeds `tame_products` nothing and disclaims every Lemma A.1 estimate); it exists to complete the anti-drift net.  Cost: `import Contracts.V1.TameProduct` in the **binding** (a `Bindings.*` import, so the contract's three-import discipline is untouched), and the `D01.datum_lemmas` closure grows by exactly one module, 1126 → 1127, all of it `Contracts.*`. |

Not applied, and why:

* **6** (INFO) — `PLAN.md` has no row for lane 034.  `PLAN.md`'s progress table is the unique
  lane-number allocation point and is the lead's at merge time (`CLAUDE.md` 编号规则); this lane
  does not edit it.
* **7** (INFO) — no action requested: `test_contract_mutations.py` builds its four mutants against
  `Contracts.V1.Thresholds` only, so it is a harness check and not a `DatumLemmasAPI`-specific
  one.  Recorded here so the gate is not over-read; the D01-specific guarantee is the
  `Tests/DatumLemmas.lean:14` `checkAxioms` line.
* The two stale-docstring notes the review adds in passing — `TameProduct.lean:203-205` ("the
  converse is open", now closed by `memHInfty_iff_smoothJets`) and the two `Data.lean`
  understatements of §3 item 2 — are **not** edits: both files are frozen V1 specifications, and
  `check_contracts.py`'s `check_compatibility` rejects any byte change to them.  The
  `TameProduct` one is now recorded in the new bridge's docstring, where a reader of either file
  will meet it.

### Gates after the fixes

| command | result |
|---|---|
| `cd verification && lake build Contracts.V1.DatumLemmas Bindings.DatumLemmas Tests.DatumLemmas` | **exit 0**, `Build completed successfully (9891 jobs)` (9890 before; `Contracts.V1.TameProduct` is the one new job).  The only log line naming a file of this lane is the acceptance `info`. |
| `make check` | **exit 0** — 10 contracts, 13 policy tests, 30 work items.  `D01.datum_lemmas` closure 1127. |
| `make test` | **exit 0**; `Tests/DatumLemmas.lean:14:0: Contract BlowupDensity.Tests.checkedDatumLemmas: checked; standard logical axioms only` |
| `#print axioms` (scratch, deleted) | `checkedDatumLemmas`, `Bindings.datumLemmas` and the new `datumLemmas_tameProduct_smoothJets_eq` each `[propext, Classical.choice, Quot.sound]` |
