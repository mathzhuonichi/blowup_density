# D01 simplifier + tester pass (lane 104, SIMP-D01)

Follow-up lane over the **eight earlier-merged** D01 modules
`Section4/D01/{ForceClass,SmoothDatum,DatumToJets,HalfOrder,Pressure,HomogeneousWitness,OrderZeroDatum,LeraySymbol}.lean`,
per the "After ACCEPT: simplifier and tester" section of
`.claude/skills/lane-review/SKILL.md`, imitating `research/A02/ATTEMPTS_SIMP.md`
(040), `research/A04/ATTEMPTS_SIMP.md` (086), `research/B02/ATTEMPTS_SIMP.md`
(090) and `research/C01/ATTEMPTS_SIMP.md` (077).  **No new mathematics**; every
public statement is **byte-identical** to the merged version — verified by a full
`git diff` restricted to signature lines (every `+`/`-` line is an `open scoped`
line; no `theorem`/`lemma`/`def`/`abbrev` signature and no proof-body line
changed).  The seven newer P2-route D01 modules (`DerivativeDatum`,
`DivergenceTime`, `Transverse`, `Longitudinal`, `LerayMultiplier`, `LerayDatum`,
`LerayLowering`) were **not touched** (other lanes are active on them).

Worktree `.claude/worktrees/104-SIMP-D01`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `ForceClass.lean` | 435 | 435 | −2 unused scoped opens (`ENNReal`, `SchwartzMap`); token edit on one line |
| `SmoothDatum.lean` | 406 | 406 | −1 unused scoped open (`SchwartzMap`); token edit on one line |
| `DatumToJets.lean` | 514 | 514 | −1 unused scoped open (`SchwartzMap`); token edit on one line |
| `HalfOrder.lean` | 187 | 187 | −1 unused scoped open (`SchwartzMap`); token edit on one line |
| `Pressure.lean` | 383 | 383 | untouched (no unused open; already tight, all docstrings) |
| `HomogeneousWitness.lean` | 700 | 700 | untouched (all four scoped opens used) |
| `OrderZeroDatum.lean` | 123 | 122 | whole `open scoped ENNReal SchwartzMap ComplexConjugate` line deleted (all three unused) |
| `LeraySymbol.lean` | 161 | 160 | whole `open scoped RealInnerProductSpace` line deleted (unused; code uses `inner ℝ`, never `⟪⟫`) |
| **total** | **2909** | **2907** | −2 |

As with C01 (077, also a set of warning-free reviewed modules) the value of this
pass is **not** a line-count reduction: these eight modules were already
warning-free, `maxHeartbeats`-free, and carried a paper-located docstring on
every substantive public theorem before the lane began.  The substantive output
is (a) the verified removal of six modules' unused scoped opens, and (b) the
tester half below (eight negative checks, the full conformance table, the
unproved-obligation and MAINT ledgers, and the CI-closure statement).

## Simplified

* **Unused scoped `open`s dropped (task 1), each verified empirically** — after
  removal `lake env lean <file>` is silent, exit 0 (the C01 methodology):
  - `ForceClass`: `open scoped ContDiff ENNReal SchwartzMap` → `open scoped ContDiff`.
    No `ℝ≥0∞`/`⊤`/`‖·‖ₑ`/`eLpNorm` token and no `𝓢`/`𝓢'` token occurs in code
    (`SchwartzMap Space ℂ` is the bare `def` name, which needs no notation);
    `ContDiff` kept for `ContDiff ℝ ∞`/`ContDiffOn ℝ ∞` (e.g. lines 108, 302).
  - `SmoothDatum`: dropped `SchwartzMap` (no `𝓢` token; `IsSobolevDatum` writes
    `SchwartzMap Space ℂ` bare).  Kept `ContDiff`, `ENNReal` (`ℝ≥0∞`, `‖·‖ₑ`),
    `ComplexConjugate` (`conj`, 6 uses) and `LineDeriv` (`∂_{v}`, 4 uses).
  - `DatumToJets`: dropped `SchwartzMap`; kept `ContDiff`, `ENNReal`.
  - `HalfOrder`: dropped `SchwartzMap`; kept `ContDiff`, `ENNReal`.
  - `OrderZeroDatum`: the whole `open scoped ENNReal SchwartzMap ComplexConjugate`
    line removed — none is used (`𝓕` comes from the non-scoped `open …
    FourierTransform`; `Complex.conj_ofReal` is a lemma, not the `conj` notation;
    no `ℝ≥0∞`/`𝓢`).
  - `LeraySymbol`: `open scoped RealInnerProductSpace` removed — the file writes
    `inner ℝ ξ v` and `real_inner_smul_left` throughout, never the `⟪·,·⟫`
    notation that open provides.
* **`Pressure` and `HomogeneousWitness` left untouched.**  `Pressure`'s
  `open scoped ContDiff ENNReal` are both used (8 `ℝ≥0∞`/`ENNReal.*` uses, plus
  `ContDiff ℝ ∞`).  `HomogeneousWitness`'s `open scoped ContDiff ENNReal
  SchwartzMap ComplexConjugate` are all used (`𝓢'(Space,ℂ)` 10×, `conj` 12×,
  `ℝ≥0∞`/`‖·‖ₑ`/`eLpNorm` 21×, `ContDiff ℝ ∞`).
* **No `set_option`/`maxHeartbeats` existed** in any of the eight (grep; the one
  `maxHeartbeats` hit is prose in `OrderZeroDatum.lean:49`'s docstring) — nothing
  to remove.

## Not simplified, and why

* **No proof body was shortened (task 1).**  All eight modules already build
  warning-free: `lake env lean` on each is silent both before and after the
  lane, so the default `unusedVariables`/`unnecessarySeqFocus`/… linters (which
  do fire in dependency modules such as `Paper3.RealPositiveDensity`) find **no
  dead `have`, unused binder or collapsible tactic** on any own line.  Every step
  is load-bearing (the eight negative checks confirm the main-theorem hypotheses
  are all used).  Collapsing a multi-step block to `simp`/`positivity` would risk
  the transitive axioms or a byte-identical statement for no verified gain, so
  none was attempted — same finding as C01/077.
* **No docstrings added (task 2).**  Every *substantive* public theorem already
  carries a paper-located docstring copied from the module header / ATTEMPTS /
  REVIEW / `Data.lean` (verified by reading all eight).  The public declarations
  that lack a docstring are, without exception, internal infrastructure or
  normal-form helpers with **no paper location to copy**: the `@[simp]` `rfl`
  lemmas (`schwartzAngularFourier_apply`, `homogeneousVectorDatum_coe`,
  `compactSchwartzComponents_apply`, `lowerDatumL_apply`, `lowerVectorL_apply`),
  the `IsRealField.{add,sum,scale,laplacian,bessel,iteratedBessel}` closure
  algebra and the `realSymmetry_*`/`norm_*`/`enorm_*`/`measurable_*`/
  `contDiff_component`/`isHomogeneousDatum_sub`/`isSliceDistribution_unique`
  /`componentLp_ae`/… measurability–linearity–norm helpers.  The task's rule is
  "copy locations only … never invent"; fabricating prose docstrings for ~30
  such helpers is over-engineering (硬规矩 #1) and would churn frozen files, so
  none was added.  The one C01 precedent for adding a docstring was a single
  missing case; here the substantive surface is fully documented already.
* **No internal duplication deduped inside the eight (task 3).**  The flagged
  candidates were checked:
  - `contDiff_slice`/`contDiff_slice_scalar` are defined **once** (DatumToJets
    lines 366/378); no copy exists in the other seven of the eight (grep).  The
    `R42`/`A04` copies are outside the eight → MAINT list.
  - the a.e.-conjugation lemmas (`conjugation_ae`, `conjugation_toLp`,
    `fourier_conjugation`, `conjugation_toLp_of_isRealField` in `SmoothDatum`;
    `conjugation_componentLp` in `OrderZeroDatum`) are **distinct** statements;
    `OrderZeroDatum` already *reuses* `SmoothDatum.conjugation_ae` and
    `fourier_conjugation` by import, so there is no copy to remove.
  - the `SmoothL2Field` wrappers (`SmoothDatum.IsRealField.*`) have no duplicate.
  - `ForceClass.cyclesComponent` (:221) has a body byte-identical to
    `DatumToJets.cyclesComponentOfAngular` (:140), and `ForceClass` §4 as a whole
    reconstructs at order 0 what `DatumToJets` proves generally — its own
    docstring says "When DatumToJets lands, §4 can be deleted in favour of its
    `memLp_of_isSobolevDatum`".  This dedup is **not** byte-identical-preserving
    (it needs `ForceClass` to import `DatumToJets` — adding that analytic closure
    to `ForceClass`'s build — plus rewiring `schwartzPairable_slice_of_memForceR`
    from the per-component `Continuous`-only `memLp_component_of_isSobolevDatum`
    to the whole-field `ContDiff`-only `DatumToJets.memLp_of_isSobolevDatum`
    composed with a projection, plus removing/renaming the public §4 helpers).
    Per the task ("replace only if `rfl`-transparent **and** statements stay
    byte-identical; otherwise record") it is **recorded** (MAINT list) not done.

## Negative-check results (task/Part B item 2; edits done only in `/tmp/d01neg/`
scratch copies — the modules were never touched)

For the main theorem of each of the eight modules, one hypothesis was removed in
a scratch under `set_option autoImplicit false in` (so a hypothesis appearing in
the type cannot be silently re-bound — the C01 autoImplicit finding), and the
proof was confirmed to break.  The control is the module itself, which builds
(`lake build`, above).

| module | main theorem | hypothesis removed | break |
|---|---|---|---|
| `ForceClass` | `memForceR_add` | `hg : MemForceR g` | `error: Unknown identifier 'hg'` (`neg_forceclass.lean:9,11`) — the second addend's smoothness/data are unavailable |
| `SmoothDatum` | `exists_isSobolevDatum_of_contDiff_memLp` | `hL2 : ∀ n, MemLp (iteratedFDeriv ℝ n z) 2 volume` | `error: Unknown identifier 'hL2'` (`neg_smoothdatum.lean:10,11`) — the `SmoothL2Field` witness `⟨z, hz, hL2⟩` cannot be formed |
| `DatumToJets` | `memLp_iteratedFDeriv_of_isSobolevDatum` | `hj : j ≤ m` | `error: Unknown identifier 'hj'` (`neg_datumtojets.lean:11`) — `jetOfDatum_ae hj …` has no order bound |
| `HalfOrder` | `forceSobolevENorm_ne_top` | `hf : MemForceR f` | `error: Unknown identifier 'hf'` (`neg_halforder.lean:11`) — no integer-order datum path to lower |
| `Pressure` | `pressureGradient_slice_smoothL2_iff_temporalDerivative` | `hf : MemForceR f` | `error: Unknown identifier 'hf'` (`neg_pressure.lean:13`) — the force slice is not known `H^∞` |
| `HomogeneousWitness` | `homogeneousDatum_unique` | `hG' : IsHomogeneousDatum s G' u` | `error: Unknown identifier 'hG''` (`neg_homogeneous.lean:15`) — the second datum's realization is missing |
| `OrderZeroDatum` | `isSobolevDatum_orderZeroDatum` | `hz : MemLp z 2 volume` | `error: Unknown identifier 'hz'` (`neg_orderzerodatum.lean:9`) — `orderZeroDatum hz` in the conclusion cannot be formed |
| `LeraySymbol` | `complementSymbol_smul` | `hc : c ≠ 0` | `error: unsolved goals` (`neg_leraysymbol.lean:15`) — `field_simp` cannot clear `c` from the rescaling coefficient, so the `hcoeff` step fails; `c = 0` genuinely breaks 0-homogeneity |

All eight hypotheses are load-bearing.

## Conformance (Part B item 1; every claimed-proved field has a discharging
theorem plus a machine check)

There is **no `research/D01/Spec.lean`**; the D01 obligations are recorded in the
unit ledgers `research/D01/*.md` and in the registered contracts.  Conformance is
established two ways: the four **datum** modules through the registered contract
`D01.datum_lemmas`(+`_v2`) — every field of `DatumLemmasAPI`/`DatumLemmasV2API`
is discharged and machine-checked by `Tests.DatumLemmas`/`Tests.DatumLemmasV2`
(`make test`, "checked; standard logical axioms only") via the `rfl` bridges in
`Bindings/DatumLemmas.lean` and `Bindings/DatumLemmasV2.lean`; the other four are
audited by their conformance files.  Field → discharging theorem:

**`Contracts.V1.DatumLemmas.DatumLemmasAPI` (Bindings/DatumLemmas.lean):**

| contract field | discharging theorem (`NSFormalization.Section4.D01.`…) |
|---|---|
| `Cjet`, `Cjet_pos` | `DatumToJets.jetSobolevConst`, `…_pos` |
| `smoothJets_exists_datum` | `SmoothDatum.exists_isSobolevDatum_of_contDiff_memLp` |
| `smoothJets_sobolevENorm_ne_top` | `SmoothDatum.sobolevENorm_ne_top_of_contDiff_memLp` |
| `smoothJets_exists_datum_fderiv` | `SmoothDatum.exists_isSobolevDatum_fderiv` |
| `memHInfty_iff_smoothJets` | `DatumToJets.memHInfty_iff_smoothSquareIntegrableJets` |
| `memLp_of_isSobolevDatum` | `DatumToJets.memLp_of_isSobolevDatum` |
| `jetSobolevENorm_le_sobolevENorm` | `DatumToJets.jetSobolevENorm_le_sobolevENorm` |
| `memHInfty_partialDeriv` | `DatumToJets.memHInfty_dirDeriv` |
| `initialClass_smoothJets` | `DatumToJets.memHInfty_jetClasses` (`.1`) |
| `solution_slice_smoothJets` | `DatumToJets.smoothSquareIntegrableJets_slice` |
| `solution_slice_pressureGradient_contDiff` | `DatumToJets.contDiff_pressureGradient_slice` |
| `isSobolevDatum_unique` | `ForceClass.isSobolevDatum_unique` |
| `isSobolevDatum_add` | `ForceClass.isSobolevDatum_add` |
| `isSobolevPath_add` | `ForceClass.isSobolevPath_add` |
| `memForceR_slice_integrable` | `ForceClass.schwartzPairable_slice_of_memForceR` |
| `memForceCompact_memForceR` | `ForceClass.memForceR_of_memForceCompact` |
| `memForceR_add` | `ForceClass.memForceR_add` |
| `memForceR_add_compact` | `ForceClass.memForceR_add_compact` |
| `memForceCompact_add` | `ForceClass.memForceCompact_add` |
| `memForceCompact_of_smooth_support` | `ForceClass.memForceCompact_of_smooth_support` |
| `memForceR_of_agreesOnFuture` | `ForceClass.memForceR_of_agreesOnFuture` |
| `memForceR_of_compact_difference` | `ForceClass.memForceR_of_compact_difference` |
| `memForceR_of_force_formula` | `ForceClass.memForceR_of_force_formula` |
| `schwartz_exists_homogeneousDatum` | `Homogeneous.exists_isHomogeneousSliceDatum` |
| `compact_exists_homogeneousDatum` | `Homogeneous.isHomogeneousSliceDatum_compact` |
| `isHomogeneousSliceDatum_unique` | `Homogeneous.isHomogeneousSliceDatum_unique` |
| `homogeneousENorm_schwartz_ne_top` | `Homogeneous.homogeneousENorm_schwartz_ne_top` |
| `isHomogeneousSliceDatum_sub` | `Homogeneous.isHomogeneousSliceDatum_sub` |
| `schwartz_integrable_component` | `Homogeneous.integrable_schwartz_mul_component` |
| `compact_exists_homogeneousPath` | `Homogeneous.isHomogeneousPath_compact` |
| `bochnerDatumENorm_eq_eLpNorm_slice` | `Homogeneous.bochnerDatumENorm_eq_eLpNorm_slice` |
| `eLpNorm_slice_le_forceHomogeneousENorm` | `Homogeneous.eLpNorm_slice_le_forceHomogeneousENorm` |

**`Contracts.V2.DatumLemmas` new fields (Bindings/DatumLemmasV2.lean → HalfOrder):**

| contract field | discharging theorem | axioms-file `example`/`#print axioms` |
|---|---|---|
| `forceSobolevENorm_ne_top` | `HalfOrder.forceSobolevENorm_ne_top` | `axioms_halforder.lean` (general `example` + `#print axioms`) |
| `forceSobolevENormL1_half_ne_top` | `HalfOrder.forceSobolevENormL1_half_ne_top` | `axioms_halforder.lean` (`example` + `#print axioms`) |
| `forceSobolevENormL2_half_ne_top` | `HalfOrder.forceSobolevENormL2_half_ne_top` | `axioms_halforder.lean` (`example` + `#print axioms`) |

**Modules not in the registered contract, audited by their conformance files
(all elaborate exit 0, standard axioms only, all `example`s accepted):**

| module | conformance file | audited deliverables / examples |
|---|---|---|
| `LeraySymbol` (P2 · d) | `axioms_p2.lean` | 14 `#print axioms` (`complementSymbol_apply`, `_idempotent`, `norm_…_le`, `_opNorm_le_one`, `_neg`, `leraySymbol_add_…`, `…_eq_sub`, `_apply_mem`, `_fixed_of_mem`, `_self`, `_eq_zero_of_inner_eq_zero`, `_smul_self`, `_smul`) |
| `Pressure` (L9c-partial) | `axioms_l9c.lean` | 11 `#print axioms` (`pressureGradient_slice_eq`, `temporalDerivative_slice_eq`, four `*_slice_smoothL2`, `forceSlice_smoothL2_of_memForceR`, `pressureGradient_slice_smoothL2_of`, `temporalDerivative_slice_smoothL2_of`, the `Iff`, the forward corollary) + defeq `example : SmoothSquareIntegrableJets v ↔ A05.SmoothL2 v := Iff.rfl` |
| `OrderZeroDatum` (SL7a) | `axioms_sl7a.lean` | 3 `#print axioms` + 2 conformance `example`s (`IsSobolevDatum 0 z (orderZeroDatum hz)`; `∃ A, IsSobolevDatum 0 z A`) in `Contracts.V1.Data` vocabulary |

No missing conformance `example` was found, so none was added: every theorem the
ATTEMPTS files claim proved is either a registered-contract field (checked by
`make test`) or has a `#print axioms`/`example` in its conformance file.

## D01 obligations still unproved (from the module gap sections / ATTEMPTS)

These are recorded gaps, not regressions — copied here for the ledger:

1. **G2 + homogeneous half of G3** (`HalfOrder`, `ATTEMPTS_HALFORDER.md`):
   `Data.forceHomogeneousENorm 1 (1/2) f ≠ ⊤` and the path monotonicity
   `forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f`.  Needs the
   homogeneous-datum `L²`-multiplier `ξ ↦ |ξ|^{1/2}(1+‖ξ‖²)^{-1/4}` for a general
   `H^∞` slice — genuinely new Fourier analysis beyond order monotonicity.  Only
   the inhomogeneous half `forceSobolevENorm q s f ≠ ⊤` is proved.
2. **L9(c) proper** (`Pressure`, `ATTEMPTS_L9C.md`): eq:Rpressure
   `∇p = (I−P)(f − ∇·(u⊗u))` and the unconditional
   `SmoothSquareIntegrableJets (∇p(t,·))`.  Needs the whole-space angular
   Leray/Helmholtz projection: (i) the `L²` Helmholtz decomposition + `P`; (ii)
   the closed solenoidal subspace membership of `∂ₜu(t,·)` (D01 unit L3, open);
   (iii) `div ∂ₜu = ∂ₜ div u`; (iv) `(I−P)` bounded on every `H^m`.  Only the
   conditional `Iff`, the three `H^∞`-slice lemmas and the spatial smoothness of
   `∇p` are proved.
3. **`forceHomogeneousENorm` finiteness / I03 U7c** (`HomogeneousWitness`,
   `ATTEMPTS_HOMOGENEOUS.md` §4(a)1): `forceHomogeneousENorm q s f ≠ ⊤` needs an
   `AEStronglyMeasurable` homogeneous datum path over `forceTimeMeasure`.  Only
   the unconditional lower bound `eLpNorm_slice_le_forceHomogeneousENorm` and the
   conditional equality `forceHomogeneousENorm_eq_of_aestronglyMeasurable` are
   proved.
4. **Order-0 Plancherel norm identity** (`OrderZeroDatum` docstring §Scope):
   `‖orderZeroDatum hz‖ = ‖z‖_{L²}` is deliberately deferred to `Paper3` (needs an
   order-0 vector isometry `cyclesToAngularRealVector_symm_norm_le` and the
   Euclidean-valued Pythagorean `L²` identity).  Only the *realization*
   (`IsSobolevDatum`) is proved here; `orderZeroDatum` is exposed as a `def` so
   the identity can be stated against it later.

## MAINT list (promotions/dedups recorded, not done in this SIMP lane)

* `angularFrequencyDilation_coeFn` in `Transverse.lean` → promote to `Paper3`
  (flagged by reviewers; `Transverse` is one of the seven newer modules, outside
  this lane).
* `angularFourier_conj_neg` (`HomogeneousWitness.lean:190`) is generalized by
  B02's `angularFourier_conj`; a B02↔D01 MAINT lane should replace it.  It is a
  public theorem, so it cannot be removed here without breaking the byte-identical
  constraint, and B02's generalization is not imported by `HomogeneousWitness`.
* The `R42`/`A04` copies of `contDiff_slice` should be consolidated onto the
  canonical `DatumToJets.contDiff_slice` (both outside the eight).
* **New this lane:** `ForceClass` §4 (`cyclesComponent`,
  `compactRep_cyclesComponent`, `memLp_component_of_isSobolevDatum`,
  `schwartzPairable_of_isSobolevDatum`) reconstructs order-0 what `DatumToJets`
  proves generally; `ForceClass`'s docstring itself flags "§4 can be deleted in
  favour of `DatumToJets.memLp_of_isSobolevDatum`".  Deferred here because the
  dedup is not byte-identical-preserving (needs a new `ForceClass → DatumToJets`
  import + proof rewiring + removal of public helpers).

## CI closure (Part B item 3)

* **In a registered-contract Tests closure** (`make test` compiles them via
  `Bindings.DatumLemmas` / `Bindings.DatumLemmasV2` — which `import` them — and
  their `Tests.*`): **`ForceClass`, `SmoothDatum`, `DatumToJets`, `HalfOrder`,
  `HomogeneousWitness`** (5 of 8).  `ForceClass` is additionally in the B01/B02
  closure via `Bindings.BochnerPartial`.
* **Not in any registered-contract Tests closure:** **`Pressure`,
  `OrderZeroDatum`, `LeraySymbol`** (3 of 8) — no `verification/{Bindings,Tests,
  Contracts}` module imports them (grep).  They are covered by (a) their
  conformance files `axioms_l9c` / `axioms_sl7a` / `axioms_p2` (run manually,
  above), and (b) CI's changed-module step
  `experiments/build_changed_lean.py --base-ref …` which `lake build`s every
  changed `formalization/` module (it reported "none" here only because the edits
  are still uncommitted; it diffs committed refs `base..HEAD`).  *For the next
  contract bundle:* fold `Pressure` (L9c), `OrderZeroDatum` (SL7a) and
  `LeraySymbol` (P2·d) into a registered Tests closure when the P2 / L9(c)
  contracts are registered.

## Commands run (all `lake` from `WT/verification`, one at a time)

| command | result |
|---|---|
| `lake build` of the eight modules (baseline, then after edits) | `Build completed successfully (9892 jobs)`; only dependency-module warnings (`Paper3.*`, `vendor/HeliCorgi`), none on any D01 own line |
| `lake env lean` on each of the eight (before + after) | each silent, exit 0 (zero own-line diagnostics) |
| `lake env lean ../research/D01/axioms_halforder.lean` | exit 0, 3 deliverables + 2 rfl bridges + 3 conformance `example`s, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/D01/axioms_l9c.lean` | exit 0, 11 `#print axioms` all standard, defeq `example` accepted |
| `lake env lean ../research/D01/axioms_p2.lean` | exit 0, 14 `#print axioms` all standard |
| `lake env lean ../research/D01/axioms_sl7a.lean` | exit 0, 3 `#print axioms` + 2 conformance `example`s, all standard |
| `lake env lean` on `axioms_{sl3,sl4a,transverse,longitudinal,leray_datum,leray_lowering}` (downstream, newer modules that transitively import the eight) | all exit 0, standard axioms only — confirms the byte-identical edits are downstream-safe |
| 8 negative checks (`/tmp/d01neg/neg_*.lean`) | all break as tabled above (controls = the built modules) |
| `git diff` (signatures) | every changed line is an `open scoped` line; no signature or proof line changed |
| `make check` | exit 0 (architecture; contract-policy 13 tests; work-queue 30 items consistent) |
| `make test` | **18/18** contracts "checked; standard logical axioms only" (incl. `checkedDatumLemmas`, `checkedDatumLemmasV2`, which rebuild the edited modules) |
