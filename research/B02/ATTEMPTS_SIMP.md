# B02 simplifier + tester pass (lane 090, SIMP-B02)

Follow-up lane over the seven merged B02 modules
`Section4/B02/{LowFrequency,Annular,LowHigh,Cutoff,LebesgueDatum,AnnularSchwartz,
AnnularReal}.lean` (Proposition 4.6 homogeneous clause, `04-whole-space.tex:241-249`
eq:Rnegative-cutoff / eq:homogeneous-realization), per the "After ACCEPT: simplifier
and tester" section of `.claude/skills/lane-review/SKILL.md`, imitating
`research/A04/ATTEMPTS_SIMP.md` (086), `research/C01/ATTEMPTS_SIMP.md` (077) and
`research/A02/ATTEMPTS_SIMP.md` (040).

**No new mathematics.**  Every *public statement* is byte-identical to the merged
version — confirmed by `git diff` restricted to declaration-signature lines: the only
added/removed `theorem`/`def`/`abbrev`/`lemma` signature line in the seven modules is
the one new dedup helper `realSobolevHilbert_conj_reflection_ae`; all other `+`/`-`
code lines are `open`/`open scoped` edits, the two dedup call-sites, or docstring
comments.  All seven modules still `lake build` and elaborate silently under
`lake env lean`, and all seven `research/B02/axioms_*.lean` files
(`u1, u2, u2_sl3, u34, u6, u7, u8`) elaborate with only
`[propext, Classical.choice, Quot.sound]` and every conformance `example` accepted.

Worktree `.claude/worktrees/090-SIMP-B02`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `LowFrequency.lean` | 196 | 195 | −1 unused `open Set`; removed whole unused `open scoped RealInnerProductSpace ENNReal` line |
| `Annular.lean` | 404 | 434 | −1 unused `open Set`; +dedup helper; −dedup at one call-site; +8 docstrings on spec-fields/infra |
| `LowHigh.lean` | 331 | 332 | −1 unused scoped `RealInnerProductSpace`; +1 docstring |
| `Cutoff.lean` | 476 | 480 | −1 unused `open Set`, −1 scoped `BigOperators`; +4 infra docstrings |
| `LebesgueDatum.lean` | 489 | 498 | −1 unused scoped `RealInnerProductSpace`; +4 docstrings |
| `AnnularSchwartz.lean` | 117 | 116 | removed whole unused `open MeasureTheory Set Filter` line |
| `AnnularReal.lean` | 238 | 231 | −`Set`,`Filter`,scoped `Topology`,`FourierTransform`; −dedup at one call-site |
| **total** | **2251** | **2286** | **+35** |

Net lines rose because the substantive additions are docstrings (comment lines) and
the extracted dedup helper, while the removals are unused `open` tokens (a few tokens
per line).  As in lanes 077/086, these modules were already reviewed and build
**warning-free**, so there were no dead `have`s, unused binders, `maxHeartbeats` or
`set_option` to remove (`grep -n maxHeartbeats` / `set_option` over all seven: none).
The value of this pass is the dead-`open` removal, the one dedup the reviewers flagged,
the docstrings, and the tester half (which surfaced the stale `axioms_u8` example, a
real finding).

## Method for the open removals

Every `open`/`open scoped` token was decided empirically (`/tmp/b02simp/prune.py`,
one probe per token): a scratch copy with exactly one token — or one whole line —
removed was re-elaborated with `lake env lean`; a removal was accepted **only** if the
file re-elaborated with zero output (exit 0).  Imports were probed the same way but
kept under the 086 semantic-home rule (see "Not simplified").  After applying all
accepted removals the whole closure was rebuilt (`Build completed successfully (8822
jobs)`), each module re-checked silent, and all axioms files re-run standard-clean.

## Simplified

* **Dead `open`/`open scoped` tokens dropped (task 1)**, each verified by silent
  re-elaboration after removal:
  - `LowFrequency`: `open Set` dropped (`Iio`/`Ioo`/`Ioi`/`indicator`/`mem_Iio` are all
    written fully qualified); whole `open scoped RealInnerProductSpace ENNReal` line
    removed (no `⟪·,·⟫`, no `ℝ≥0∞`/`⊤` token in code — `inner ℝ _ _` is fully applied).
  - `Annular`: `open Set` dropped (`open MeasureTheory Set Filter` → `open MeasureTheory
    Filter`); the four scoped opens `ENNReal ContDiff ComplexConjugate Topology` all kept
    (each notation used: `ℝ≥0∞`, `ContDiff ℝ ∞`, `conj`, `𝓝`).
  - `LowHigh`: scoped `RealInnerProductSpace` dropped (uses `innerₗ`/`continuous_inner`/
    `real_inner_comm`, never the `⟪·,·⟫` notation).
  - `Cutoff`: `open Set` dropped; scoped `BigOperators` dropped (`∑` needs no scoped open
    in this Mathlib).
  - `LebesgueDatum`: scoped `RealInnerProductSpace` dropped (uses `innerₗ`/`continuous_inner`
    fully applied).
  - `AnnularSchwartz`: whole `open MeasureTheory Set Filter` line removed (no
    `MeasureTheory`/`Set`/`Filter` identifier occurs — `HasCompactSupport`/`tsupport` are
    root, `Metric.*` qualified, `𝓝` comes from scoped `Topology`).
  - `AnnularReal`: `open MeasureTheory Set Filter` → `open MeasureTheory` (`Set`,`Filter`
    unused); scoped `Topology`,`FourierTransform` dropped (no `𝓝`, no bare `𝓕` in the
    SL3 a.e. proofs — only `angularFourier`/lemma names occur).
* **Dedup of the a.e. conjugate-reflection pattern (task 3a).**  The
  `mem_realSubspace_iff` + `realSymmetry_ae` derivation of the Hermitian symmetry
  `(X ξ) = conj (X (-ξ))` a.e. for an element `X : RealSobolevHilbert s` was written
  **verbatim** (an 8-line `have hA … have hSym …` block) in two places:
  `Annular.annularTruncLp_mem` and `AnnularReal.angularFourier_realPart_ae`.  Extracted
  to a single helper `Annular.realSobolevHilbert_conj_reflection_ae`
  (`Annular.lean:136`), which `AnnularReal` sees transitively; both call-sites are now
  the single line `have hSym := realSobolevHilbert_conj_reflection_ae _`.  The two public
  theorem statements are byte-identical; the negative check on `angularFourier_realPart_ae`
  (below) confirms `hae` is still load-bearing through the helper.  `AnnularReal`'s
  module-docstring reference `(pattern of Annular.lean:200-207)` was updated to name the
  helper.  (The other `realSymmetry_ae` uses — `Annular:annularTruncLp_mem` outer indicator
  combine, `Annular:annularSmoothing` `realProjection` plumbing, `LebesgueDatum:
  realSymmetry_lebesgueDatum` on `homogeneousProfile` — are *different* statements, not the
  same copy, so they are not deduped.)
* **Docstrings naming the location (task 2), copied not invented.**  Added a `/--` to
  each public declaration that lacked one: the two spec-field theorems `annularRestriction`
  (`Spec.lean:302-304`, `04-whole-space.tex:241`) and `annularSmoothing`
  (`Spec.lean:314-318`, `:241`) — locations copied from the Annular module header /
  `axioms_u1.lean`; the new helper; and the elementary infra lemmas
  (`measurableSet_frequencyAnnulus`, `isClosed_closedFrequencyAnnulus`,
  `neg_mem_frequencyAnnulus`, `annularTruncLp_ae`, the `annularCutoff_*` family;
  `finrank_space_eq_three`; `scaledCutoff_baseCutoff`, `schwartzVector_apply/_contDiff/
  _memLp`; `lebesgueDatum_ae`, `mem_realSubspace_lebesgueDatum`, `lebesgueVectorDatum_coe`,
  `isHomogeneousSliceDatum_sub_of_integrable`) with a one-line factual description and
  **no invented paper location**.

## Not simplified, and why

* **No import removed.**  Every import that probed REMOVABLE (transitively available
  through a sibling import) is the *direct home* of a lemma/def the module references by
  name, so all were **kept** under the 086 build-hygiene rule.  Concretely:
  `LowFrequency` keeps `Paper3.SobolevWeights` (`homogeneous_low_frequency_integrable`),
  `VolumeOfBalls` (`EuclideanSpace.volume_ball_fin_three`), `HaarToSphere`
  (`integral_fun_norm_addHaar`), `Bochner.ContinuousLinearMap`
  (`ContinuousLinearMap.integral_comp_comm`); `Annular` keeps `Source.RealSobolev`,
  `ComparisonCutoffs` (`cutoff*`), `Normed.Lp.SmoothApprox`
  (`MemLp.exist_eLpNorm_sub_le`), `Lebesgue.DominatedConvergence`
  (`tendsto_lintegral_of_dominated_convergence'`); `LowHigh` keeps `Fourier.LpSpace`
  (`Lp.fourier_toTemperedDistribution_eq`, `Lp.norm_fourier_eq`),
  `AEEqOfIntegralContDiff` (`ae_eq_of_integral_contDiff_smul_eq`); `Cutoff` keeps
  `Source.FourierConvention` (`angularFourier`), `SchwartzCompactApproximation`
  (`truncate`, `seminorm_truncate_sub_le`); `AnnularSchwartz` keeps `CompactSchwartz`
  (`ofCompactSupport`), `SchwartzSpace.Fourier` (`𝓕⁻`, `fourier_fourierInv_eq`);
  `AnnularReal` keeps `Cutoff` (semantic home of `schwartzVector`, `IsSliceDistribution`,
  `IsHomogeneousSliceDatum`, `SplitRange`, `SpatialField`, even though transitively
  available via `LebesgueDatum`).
* **No proof body shortened.**  All seven modules were reviewed
  (`REVIEW_U1/U2/U2_SL3/U34/U6/U7/U8.md`) and build **warning-free**: `lake env lean` on
  each is silent, so the default `unusedVariables` linter finds no dead `have`s or unused
  binders.  The remaining multi-step proofs are load-bearing (the dominated-convergence
  tail in `tendsto_eLpNorm_annulus_compl`, the vector-triangle `L¹→L∞` bound in
  `fourierSupBound`, the `l2_fourier_pairing`/`angular_plancherel` Plancherel chain, the
  low/high split arithmetic).  Collapsing any into `simp`/`positivity`/`gcongr` would risk
  the transitive axioms or a byte-identical statement for no verified gain (same finding as
  077/086), so none was attempted.
* **The `§0` restatements were not deduped against a canonical module (task 3).**
  `Annular.lean §0` restates the spec predicates `frequencyAnnulus`,
  `closedFrequencyAnnulus`, `IsAnnularDatum`, `IsAnnularRestriction`, `IsAnnularSupported`
  (`Spec.lean:155-192`), and `Cutoff.lean §4` restates the `Data.lean` chain
  (`SpatialField`, `VectorDistribution`, `IsSliceDistribution`, `IsHomogeneousDatum`,
  `IsHomogeneousVectorDatum`, `IsHomogeneousSliceDatum`, `homogeneousFourierENorm`) plus
  the `Spec.lean` objects `scaledCutoff`, `schwartzVector`, `SplitRange`,
  `lowHighConstant`.  Neither `research/B02/Spec.lean` nor `Contracts/V1/Data.lean` is an
  importable canonical module for `formalization/` (repo rule), so these are the
  deliberate verbatim fidelity anchors the conformance files discharge by defeq — nothing
  to replace.

## For the MAINT lane (do NOT do here — changes namespaces)

Reviewer flags (b) and (c): both are namespace moves, out of scope for a simplifier lane.

| item | current location | proper home | note |
|---|---|---|---|
| `angularFourier_conj` | `Section4/B02/AnnularReal.lean:54` | `Source/FourierConvention.lean` (next to `angularFourier`) | generalizes `Section4/D01/HomogeneousWitness.lean:190 angularFourier_conj_neg` (the real-`f` special case, same simp set); `HomogeneousWitness.lean:212` should then call it |
| `angular_plancherel` (+ its supports `fourier_mul_formula`, `l2_fourier_pairing`, `coeFn_l2Fourier_ae`, `eLpNorm_fourierIntegral_eq`, `angular_lintegral_eq_cycles`) | `Section4/B02/LowHigh.lean:186` | `Paper3` | Paper3-level `L¹∩L²` angular Plancherel, not B02-specific |
| angular-dilation coefficient bridge | `Section4/D01/Transverse.lean:66 angularFrequencyDilation_coeFn` | `Paper3` | Paper3-level fact, reused by B02; listed only, not moved |

(3a, the `realSobolevHilbert_conj_reflection_ae` dedup, WAS done this lane because it is
an in-B02 extraction with no namespace move — `Annular.lean:136`.)

## Negative-check results (task B.2; edits done only in `/tmp/b02simp` scratch copies —
the modules were never touched)

Method (`/tmp/b02simp/neg.py`): each scratch is a whole-module copy with
`set_option autoImplicit false in` inserted immediately before the target theorem, and
(for the removal run) exactly one hypothesis binder of that theorem deleted.  The
**control** run (autoImplicit-scoped, hypothesis kept) elaborated **silently for all
seven modules** (exit 0, 0 output lines) — so `autoImplicit false` does not distort the
targets and the removed hypothesis names do not reappear in the statement type (the
077 vacuous-pass trap does not apply).  Then the removal run:

| module | main theorem | hypothesis dropped | result (removal run) |
|---|---|---|---|
| `LowFrequency` | `fourierSupBound` | `hk : MemLp k 1 volume` | exit 1, `128:67 Unknown identifier hk` (the `(memLp_one_iff_integrable).mp hk`) |
| `Annular` | `annularSmoothing` | `hZ : IsAnnularSupported δ R Z` | exit 1, `413:36 Unknown identifier hZ` (the `hZ i` support step) |
| `LowHigh` | `lowHighSplit` | `hs0 : s ≤ 0` | exit 1, `308:61 linarith failed` (the high-freq bound `‖ξ‖^{2s} ≤ 1` needs `2s ≤ 0`) |
| `Cutoff` | `spatialApproxHomogeneous_of` | `hLowHighSplit : …` | exit 1, `432:17 Unknown identifier hLowHighSplit` |
| `LebesgueDatum` | `lebesgueHomogeneousDatum` | `hk1 : MemLp k 1 volume` | exit 1, `420:33 Unknown identifier hk1.of_le` (the L¹ integrability of each component) |
| `AnnularSchwartz` | `exists_schwartz_angularFourier_eq` | `hc : HasCompactSupport f` | exit 1, `112:42 error` (the `ofCompactSupport f hf hc` call loses its compact-support arg) |
| `AnnularReal` | `angularFourier_realPart_ae` | `hae : (W i) =ᵐ[volume] g` | exit 1, `116:56 Unknown identifier hae` (via the dedup'd `hSym`, the `hgconj` step) |

Every hypothesis is load-bearing.  The `AnnularReal` break additionally confirms the
`realSobolevHilbert_conj_reflection_ae` dedup did not weaken `angularFourier_realPart_ae`.

## Conformance (task B.1)

Every B02 spec field the ATTEMPTS files claim as proved has a spec-typed `example`
discharged by the theorem, with no extra hypotheses:

| spec field (`research/B02/Spec.lean`) | conformance `example` | discharging theorem |
|---|---|---|
| `annularRestriction` (`:302-304`) | `axioms_u1.lean:58` | `Section4.B02.annularRestriction` |
| `annularSmoothing` (`:314-318`) | `axioms_u1.lean:65` | `annularSmoothing` |
| `annularSchwartz` (`:362-364`) | `axioms_u2_sl3.lean:23` | `annularSchwartz` |
| `spatialApproxHomogeneous` (`:539-543`) | `axioms_u2_sl3.lean:30` **(added this lane)** | `spatialApproxHomogeneous` (unconditional) |
| `lowFrequencyIntegrable` (`:370`) | `axioms_u34.lean:19` | `lowFrequencyIntegrable` |
| `lowFrequencyIntegral` (`:379`) | `axioms_u34.lean:24` | `lowFrequencyIntegral` |
| `fourierSupBound` (`:397`) | `axioms_u34.lean:29` | `fourierSupBound` |
| `lowHighSplit` (`:421-425`) | `axioms_u7.lean:37` | `lowHighSplit` |
| `lebesgueHomogeneousDatum` (`:454-458`) | `axioms_u6.lean:29` | `lebesgueHomogeneousDatum` |
| `homogeneousDatumSub` (`:490-496`, integrability-carrying) | `axioms_u6.lean:44` | `isHomogeneousSliceDatum_sub_of_integrable` |
| `cutoffLebesgue` (`:513-521`) | `axioms_u8.lean:74` | `cutoffLebesgue` |
| units 2/6/7 → `spatialApproxHomogeneous` (composed, conditional) | `axioms_u8.lean:96` **(fixed this lane)** | `spatialApproxHomogeneous_of` |

Added this lane: the verbatim `spatialApproxHomogeneous` `example` in `axioms_u2_sl3`
(previously only `#print axioms`ed) — task B.1 flagged it explicitly for lane 084.  Each
example is discharged with the theorem applied to exactly the field's own hypotheses, so
no extra hypothesis is smuggled in.

### Finding: `axioms_u8`'s composed example was STALE (pre-existing, at `HEAD`)

At `HEAD` (before this lane) `research/B02/axioms_u8.lean` **failed to elaborate**: its
second `example` (the four-antecedent arrow) stated `homogeneousDatumSub` in the
historical **hypothesis-free** shape, but `spatialApproxHomogeneous_of`'s third
hypothesis had been rewired (lane 068) to carry the two physical-pairing `Integrable`
side conditions, so the bare term `spatialApproxHomogeneous_of` no longer had the
example's type — a `Type mismatch` error at `axioms_u8.lean:107`.  `axioms_u8` was last
edited at lane 060 (commit `35f1fa1`), *before* the lane-068 rewiring, and was never
updated.  This lane brought it back into line with the **current** Spec field
`homogeneousDatumSub` (`Spec.lean:490`, itself the corrected integrability-carrying form —
the hypothesis-free version is *false*, `REVIEW_U6.md` §4) by adding the two integrability
antecedents, so the composed example again matches the current spec fields verbatim and
`axioms_u8` elaborates cleanly (both `example`s accepted, both `#print axioms` standard).
The docstrings/header of `axioms_u8` were corrected accordingly.

### B02 spec fields that remain UNPROVED (input for the B02 contract lane)

The seven modules discharge the **homogeneous spatial clause + cutoff + diagonal**.  The
following `HomogeneousApproxAPI` fields are NOT discharged by these modules:

* `homogeneousDatumSub` in its **hypothesis-free** form is **false** and cannot be
  proved (`REVIEW_U6.md` §4).  Only the current integrability-carrying Spec field
  (`Spec.lean:490`) is proved.  The contract must register the integrability-carrying
  form (as `axioms_u6` does), never the historical shape.
* `chi_smooth` (`:280`), `chi_one` (`:282`), `chi_vanishes` (`:285`), `chi_range` (`:287`)
  — the fixed cutoff `χ` properties.  These modules use the vendor `baseCutoff`/`cutoff`
  and its estimates but expose **no** B02 theorem/conformance `example` for the `χ_*`
  fields; they are dischargeable from the vendor `baseCutoff_smooth/_eq_one/_eq_zero/
  _nonneg/_le_one` (the B01 contract already binds them that way) but are not yet given a
  B02 example.
* `annularPathApprox` (`:337`) — the `L^q`-path-level annular approximation.  Not in
  these modules.
* `temporalApprox` (`:563`), `separatedAssembly` (`:582`) — the shared Bochner step and
  finite-separated-sum assembly; these are B01's fields (proved in `Section4/B01/*`), not
  B02 module deliverables.
* `approxCompactHomogeneous` (`:607`) — the final compact-smooth homogeneous density
  conclusion; needs the temporal + spatial inputs assembled, not in these modules.

## CI closure (task B.3)

`grep -rn "Section4.B02" verification/{Bindings,Tests,Contracts}` returns **nothing**, so
the seven modules are **not** in a registered-contract Tests closure — same status as
A02 (040), C01 (077), A04 (086).  `verification/contracts.json` records that the D01
contract explicitly does **not** assert "the L¹∩L² homogeneous class of B02", and the
B01 contract references B02 only for the shared `temporalApprox`; there is no B02 contract
yet.  All seven modules are under `formalization/`, and `experiments/build_changed_lean.py`
maps every changed `formalization/*.lean` to its module and `lake build`s it, so CI's
changed-module step rebuilds all seven whenever this lane changes them.  *For the next
contract bundle:* fold the seven B02 modules into the Tests closure when the B02
(`HomogeneousApproxAPI`) contract is registered.

## Commands run (all `lake` from `WT/verification`, one process at a time)

| command | result |
|---|---|
| `lake build …B02.{LowFrequency,Annular,LowHigh,Cutoff,LebesgueDatum,AnnularSchwartz,AnnularReal}` (pre- and post-edit) | `Build completed successfully (8822 jobs)` both times; only warnings are from dependency `Source.*`/`Paper3.*` modules, none on B02 lines |
| `lake env lean` on each of the 7 modules (pre- and post-edit) | each silent, exit 0 (0 output lines) |
| `lake env lean ../research/B02/axioms_u1.lean` | 2 decls standard; both `annularRestriction`/`annularSmoothing` examples accepted |
| `lake env lean ../research/B02/axioms_u2.lean` | 3 decls (SL1/SL2/right-inv) standard |
| `lake env lean ../research/B02/axioms_u2_sl3.lean` | 11 decls standard; `annularSchwartz` + new `spatialApproxHomogeneous` examples accepted |
| `lake env lean ../research/B02/axioms_u34.lean` | 3 decls standard; all 3 examples accepted |
| `lake env lean ../research/B02/axioms_u6.lean` | 7 decls standard; `lebesgueHomogeneousDatum` + integrability-carrying `homogeneousDatumSub` examples accepted |
| `lake env lean ../research/B02/axioms_u7.lean` | `lowHighSplit` standard; example accepted |
| `lake env lean ../research/B02/axioms_u8.lean` | **was `Type mismatch` error at `HEAD`**; after this lane's fix: `cutoffLebesgue`/`spatialApproxHomogeneous_of` standard, both examples accepted, exit 0 |
| prune probes (`/tmp/b02simp/prune.py`, per import/open token) | as tabled in "Simplified"/"Not simplified" |
| negative checks (7 `/tmp/b02simp` scratches) | all controls silent (exit 0); all removals break as tabled |
| `make check` | see final report — architecture checks pass (`test_contract_policy` 13 OK, `check_work_queue` consistent) |
