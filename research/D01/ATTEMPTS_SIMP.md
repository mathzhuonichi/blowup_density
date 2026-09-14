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

---

# Lane 129 — P2 chain (SIMP-D01-orderzero)

Follow-up SIMP + tester lane over the **five newer P2-route** D01 modules that lane 104 did **not**
touch: `Section4/D01/{OrderZeroSymbol,OrderZeroCurl,OrderZeroAlgebra,MomentumSlice,PressureJets}.lean`
(lanes 094/108/111/117).  **No new mathematics.**  Every exported statement is byte-identical to the
merged version — verified by `git diff` restricted to declaration lines: **no `theorem`/`lemma`/`def`/
`abbrev`/`structure`/`instance` signature line was added or removed** (the only `+`/`-` lines are
`open`/`open scoped` lines, one docstring line-number cite, and one proof body — see below).  A
`#check` of the three frozen-consumed `PressureJets` exports
(`pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`,
`temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`,
`exists_isSobolevDatum_pressureGradient_slice`) is character-identical to REVIEW_SL8_ASSEMBLY §2(a).

Worktree `.claude/worktrees/129-SIMP-D01-orderzero`, base `origin/erenup/integration`.

## Line counts (before → after)

| module | before | after | Δ | what changed |
|---|---|---|---|---|
| `OrderZeroSymbol.lean` | 494 | 491 | −3 | line-42 `open scoped` dropped `ENNReal` (0 `ℝ≥0∞`/`eLpNorm`/`‖·‖ₑ` tokens); deleted line `open …RealSobolev (FourierData)` (redundant with the full `open …RealSobolev` on the next line); deleted `open …Source (frequencyUnit frequencyUnit_pos)` (unused — `frequencyUnit` occurs only in that open line); deleted `open scoped SchwartzMap LineDeriv Real ENNReal RealInnerProductSpace` (SchwartzMap/LineDeriv already file-wide from line 42, `Real`/`ENNReal`/`RealInnerProductSpace` all unused — 0 `⟪⟫`/bare-`π`/`ℝ≥0∞`) |
| `OrderZeroCurl.lean` | 517 | 506 | −11 | deleted redundant `open …RealSobolev (FourierData)` (next line opens the whole ns); deleted `open scoped SchwartzMap LineDeriv Real ENNReal RealInnerProductSpace` (dups of line 51 + `Real`/`RealInnerProductSpace` unused; `ℝ≥0∞`@450 covered by line 51); deleted the two `Leray`-block opens `(FourierData)`/`(RealVectorSobolev)` (unused in that block); **proof-body dedup**: `fourier_antisym`'s two byte-identical `rw [show … from by …]` blocks (differing only in the `p↔q` swap) factored into one local `have hpull : ∀ d c, …` (−6 lines) |
| `OrderZeroAlgebra.lean` | 112 | 112 | 0 | `open NSFormalization.Source NSFormalization.Source.RealSobolev` → `open NSFormalization.Source.RealSobolev` (parent `Source` contributes nothing used — `SchwartzPairable`/`schwartzPairable_of_memLp` are `D01.ForceClass`, in the enclosing namespace). Dependency removed, no line change. |
| `MomentumSlice.lean` | 201 | 201 | 0 | **untouched.** All opens genuinely used: `A03 (partialDeriv)` (5 bare `partialDeriv` uses, e.g. `:119`), `scoped ContDiff` (`ContDiff ℝ ∞` throughout), `A02 (ClassicalSolutionR …)`. |
| `PressureJets.lean` | 156 | 154 | −2 | deleted `open …A03 (partialDeriv)` (0 bare `partialDeriv`; only theorem *names* `sum_partialDeriv_…`/`partialDeriv_pressureGradient_symm` appear) and `open scoped ContDiff` (0 `ContDiff`/`∞`/`⊤` outside docstring prose); **docstring-only** cite fix `02-preliminaries.tex:76-81` → `:89-94` (`\label{eq:Rpressure}` is at `:90`, block spans 89–94; re-checked with `grep`, LESSONS 2026-09-14) |
| **total** | **1480** | **1464** | **−16** | + one dependency (`Source`) removed from `OrderZeroAlgebra` with no line delta |

Every removal was verified empirically: after each edit `lake env lean <file>` is **silent, exit 0**
(0 bytes of output), and the full `lake build` of the five + `A04.PressureDrop` + `Tests.DatumLemmasV3`
is green with **no own-line warning** on any D01 module.

## Simplified — details / negative (failed) simplification attempts

* **Unused/redundant `open`s (verified each empirically).**  The `open …RealSobolev (FourierData)`
  lines in `OrderZeroSymbol`/`OrderZeroCurl` are strictly redundant because the *very next* line is
  the whole-namespace `open …RealSobolev`.  The `open scoped … Real ENNReal RealInnerProductSpace`
  second-namespace lines are redundant (`SchwartzMap`/`LineDeriv`/`ENNReal` already opened file-wide
  at the top) and partly unused (`Real`: 0 bare `π`; `RealInnerProductSpace`: 0 `⟪⟫`, the code writes
  `inner ℝ ξ v` — the same finding lane 104 recorded for `LeraySymbol`).  `frequencyUnit` in
  `OrderZeroSymbol` occurs **only** inside its own `open` line ⇒ unused (contrast `OrderZeroCurl`,
  where `frequencyUnit`/`frequencyUnit_pos` are used at `:449` — that open was **kept**).
* **`fourier_antisym` dedup (the only proof-body change).**  Two adjacent `rw [show (∫ … p … q …) =
  … from by apply integral_congr_ae; …]` blocks were byte-identical up to the `p↔q` swap; factored
  into one `have hpull : ∀ d c : Fin 3, …` and finished with `rw [integral_sub …, hpull p q,
  hpull q p, hpp, sub_self]`.  Statement unchanged; `#print axioms fourier_antisym` still
  `[propext, Classical.choice, Quot.sound]`; downstream `orderZeroDatum_longitudinal_of_curl_free`
  and `Leray.lerayComplement_zero_orderZeroDatum_eq_self` rebuild green.
* **NEGATIVE simplification (recorded, reverted).**  I did **not** trim the `open A02
  (ClassicalSolutionR MemForceR)` lines in `MomentumSlice`/`PressureJets` even though `MemForceR`
  there resolves to `D01.MemForceR` (the enclosing namespace wins; A02's copy is shadowed, `rfl`-equal
  — REVIEW_SL8_PREP F-5).  Removing the shadowed `MemForceR` from the open list is a legal dependency
  trim, but it changes nothing exported, saves no line, and both modules are consumed by the frozen
  `Bindings.DatumLemmasV3` / `A04.PressureDrop`; the reviews already flagged it "harmless".  Left
  as-is to avoid churn on statement-adjacent frozen-consumed files.  Recorded as an observation, not a
  change.
* **No proof body was shortened in `OrderZeroSymbol`/`OrderZeroAlgebra`/`MomentumSlice`/`PressureJets`.**
  The reviews (108 §3, 111 §3, 117 §4) found these tight and dead-`have`-free; `lake env lean` is
  silent (no `unusedVariables`/`unnecessarySeqFocus` hits) before and after.  The four duplicated
  `OrderZeroCurl` units (`fderiv_zc_eq'`, `cs_ibp`, the cutoff/DCT machine, the transports) duplicate
  094/089 **across modules** — that is MAINT (must not move code across modules per the brief), listed
  below; the only *within-module* duplication that shortened was `fourier_antisym`'s pair.

## Tester — (a) builds / (b) axioms

| check | result |
|---|---|
| `lake build` of the 5 + `A04.PressureDrop` + `Tests.DatumLemmasV3` | `Build completed successfully`; **0** own-line warnings on any D01 module (only pre-existing `Source.*`/`Paper3.*`/`vendor/HeliCorgi` deps) |
| `Tests.DatumLemmasV3` | `Contract …checkedDatumLemmasV3: checked; standard logical axioms only` |
| `lake env lean` on each of the 5 | each silent, exit 0 (0 bytes) — before and after |
| `axioms_order_zero.lean` | exit 0, **21** decls, each `[propext, Classical.choice, Quot.sound]` |
| `axioms_order_zero_curl.lean` | exit 0, **14** decls, each `[propext, Classical.choice, Quot.sound]` (incl. the re-proved `fourier_antisym`) |
| `axioms_sl8_prep.lean` | exit 0, **13** decls (incl. dead-code `lerayComplement_orderZeroDatum_add/_sub`), each standard |
| `axioms_sl8_assembly.lean` | exit 0, **6** decls each standard + the `Contracts.V1`-vocabulary `example` elaborates silently |
| `make check` | exit 0 (contract policy 13/13; 30 work items consistent) |
| `cd verification && make test` | exit 0, **22** contracts "checked; standard logical axioms only" (incl. `checkedDatumLemmasV3`, which rebuilds `PressureJets`) |

## Tester — (c) negative checks (real, drop-one-hypothesis)

Two research files (kept, not `/tmp` per LESSONS 2026-09-14):

* **`research/D01/negative_simp_p2.lean` — MUST COMPILE (exit 0; 13 `#print axioms`, all standard —
  incl. the machine-checked counterexample `transverse_without_hdiv_is_false`, §5).**
* **`research/D01/negative_simp_p2_fail.lean` — MUST FAIL (exit 1; 5 blocks, 8 error messages: 3
  `Type mismatch` + 3 `Unknown identifier hw` + 2 `Unknown identifier hf`).**

For five of the six main exports one load-bearing hypothesis is dropped under
`set_option autoImplicit false in` (so a hypothesis appearing in the statement type cannot be silently
re-bound as implicit — LESSONS 2026-09-14); the sixth (`P2_drop_hf`) was deleted (below).  Three
dependency strengths, **labelled honestly**:

**STRUCTURAL** (the dropped hypothesis / its data appears in the *conclusion*, so the statement is not
even well-formed without it — a genuine necessity, not a signature artefact):

| export | dropped | pasted error (`negative_simp_p2_fail.lean`) |
|---|---|---|
| `orderZeroDatum_add` | `hw` | `65:27 … 65:68 … 66:33: error: Unknown identifier 'hw'` — the conclusion `orderZeroDatum (hz.add hw) = … + orderZeroDatum hw` names `hw` |
| `orderZeroDatum_pressureGradient_eq` | `hf` | `75:61 … 76:48: error: Unknown identifier 'hf'` — the RHS names `smoothL2_momentumResidual_slice u hf ht` |

**FALSIFIED** (the drop-one-hypothesis statement is provably FALSE — the strongest kind, corrected
after the lane-129 review, which showed my earlier "not feasible in a SIMP lane" claim was wrong):

| export | dropped | evidence |
|---|---|---|
| `orderZeroDatum_transverse_of_divergence_free` | `hdiv` | `transverse_without_hdiv_is_false : ¬ TransverseNoDiv` in `negative_simp_p2.lean` §5 (lifted verbatim from REVIEW_SIMP_P2.md §6, opus reviewer; standard axioms).  Applied to the nonzero curl-free `∇bump`, the `hdiv`-free statement collapses `orderZeroDatum gradBump = 0` (`lerayComplement_eq_zero_of_transverse` + lane-108 `lerayComplement_zero_orderZeroDatum_eq_self`), giving `∫ (∂ᵢbump)² = 0` via `isSobolevDatum_orderZeroDatum` against `∇bump`'s own (Schwartz) components — i.e. `∇bump ≡ 0`, contradicting `gradBump_ne_zero`.  The fail-file `transverse_drop_hdiv` (`43:5: Type mismatch`) is now a *secondary* witness of the same necessity. |

**ROUTE** (the hypothesis is consumed inside the proof; the established proof no longer typechecks —
these are *not* full falsifications, honestly labelled):

| export | dropped | pasted error |
|---|---|---|
| `orderZeroDatum_longitudinal_of_curl_free` | `hcurl` | `52:5: error: Type mismatch — … has type (∀ i j x, (partialDeriv i z x).ofLp j = (partialDeriv j z x).ofLp i) → ∀ᵐ ξ, … but is expected to have type ∀ᵐ ξ, …` |
| `lerayComplement_zero_orderZeroDatum_eq_self` | `hcurl` | `59:5: error: Type mismatch` (same shape, conclusion `lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz`) |

**`P2_drop_hf` DELETED (review finding 3).**  Dropping `hf` from
`pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` leaves a *complete, well-formed*
statement (`hf` occurs nowhere in the conclusion), so the drop-one-arg check produced only
`Unknown identifier 'hf'` inside the **proof term** — an empty check (any undefined name yields it),
the exact anti-pattern of LESSONS 2026-09-14.  It was removed; a comment in `negative_simp_p2_fail.lean`
records why.  `hf`'s necessity for P2 is genuine but is known only from the paper-level counterexample
`D01/Pressure.lean:62-66` (a smooth divergence-free `u` with `∇p ∈ L² \ H¹`, whose `f` is defined by
the momentum equation and is **not** in `F_R`), which was **not** formalized here.  The STRUCTURAL
`pressureGradient_eq_drop_hf` already exhibits a genuine statement-level `hf`-dependence of the order-0
identity.

**Follow-up recorded, NOT done (review finding 4).**  The two `hcurl` ROUTE rows are *also* falsifiable
by the same route once a nonzero divergence-free compactly-supported witness exists:
`w := curl(bump·e₀) = (0, ∂₂φ, −∂₁φ)`, divergence-free by Clairaut (`partialDeriv_gradient_eq_sndFDeriv`
+ `ContDiffAt.isSymmSndFDerivAt`, exactly as `gradBump_curl`), `w ≠ 0` because `∂₁φ ≡ 0` would force
`φ(0) = φ(3·e₁)` i.e. `1 = 0`; then transverse (proved) + longitudinal (the `hcurl`-free claim) ⇒
`lerayComplement 0 = 0` and `= self` ⇒ datum `= 0` ⇒ `w = 0`.  Estimated 40–60 lines; left for a
follow-up (out of this lane's time-box).

## Tester — (d) non-vacuity witnesses (all machine-checked, standard axioms)

In `research/D01/negative_simp_p2.lean`:

* **`ClassicalSolutionR` exports — the zero solution** (`zeroSol : ClassicalSolutionR ν 0 0 1`,
  `memForceR_zero`, reconstructed verbatim from REVIEW_SL8_ASSEMBLY appendix A).  A nonzero classical
  solution is out of reach, so per the brief `zeroSol` is the witness.  Instantiated:
  `orderZeroDatum_pressureGradient_eq`, `pressureGradient_slice_…_of_memForceR`,
  `temporalDerivative_…_of_memForceR`, `exists_isSobolevDatum_pressureGradient_slice` (all elaborate,
  standard axioms).  `memForceR_zero` genuinely forces the datum path to be the zero path
  (`forceTimeMeasure` is infinite ⇒ `memLp_const_iff` rules out a nonzero constant), so it is not a
  loophole.
* **The conclusion has content** — `const_not_jets {c ≠ 0}`: a nonzero constant field is `C^∞` but
  **not** `SmoothSquareIntegrableJets` (`memLp_const_iff` + `volume (univ : Space) = ⊤`).  So P2's
  target is not vacuously true of every smooth field.
* **Order-0 / algebra exports — the zero field** satisfies every hypothesis (div-free and curl-free
  trivially), inhabiting `orderZeroDatum_transverse_of_divergence_free`,
  `orderZeroDatum_longitudinal_of_curl_free`, `lerayComplement_zero_orderZeroDatum_eq_self`,
  `orderZeroDatum_add`.
* **A NONZERO curl-free witness `∇(bump)`** (reconstructs lane-108 reviewer `nonvac.lean`).
  `gradBump := fun y => pressureGradient (fun q => bump q.2) 0 y` is proved: `ContDiff ℝ ∞`
  (`gradBump_smooth`), `MemLp _ 2` (`gradBump_mem`, via `HasCompactSupport` — bump's gradient vanishes
  for `‖x‖ > 2`), curl-free (`gradBump_curl`, via the module's own `partialDeriv_gradient_eq_sndFDeriv`
  + `ContDiffAt.isSymmSndFDerivAt`), and **`gradBump ≠ 0`** (`gradBump_ne_zero`: if `∇bump ≡ 0` then
  every coordinate derivative of `bump` vanishes ⇒ `fderiv bump ≡ 0` (basis reconstruction
  `euclid_recon` + `clm`-on-basis) ⇒ `is_const_of_fderiv_eq_zero` ⇒ `bump 0 = bump (3·e₀)`, i.e.
  `1 = 0`).  Then `nonvac_longitudinal_nonzero` and `nonvac_leray_nonzero` package
  `gradBump ≠ 0 ∧ <the export applied to gradBump>`, showing the curl-free hypothesis class of both
  order-0 curl lemmas is **not** forced to `z = 0`.  (A nonzero divergence-free `L²` witness for the
  *transverse* lemma would need a compactly-supported `curl(A)` — not constructed; the zero field is
  the machine-checked inhabitant there, and `∇bump` is the machine-checked non-div-free member of the
  same ambient smooth-`L²` class showing `hdiv` is a genuine restriction.)

## Tester — (e) gates

`make check` exit 0; `cd verification && make test` exit 0 (22 contracts standard).  The tester brief
lists only `make check` + `make test`; the lane-129 **reviewer additionally ran `make test-mutations`
and it PASSES** (`implementation_refactor: accepted`; `admitted_proof`/`extra_axiom`/`weakened_hypothesis`
all `rejected as required`; `Mutation suite passed`) — so `scripts/gates.sh` is not an open item.

## MAINT list (recorded, NOT done — cross-module moves are MAINT, statements frozen)

1. **Dedup `OrderZeroCurl`'s 094/089-duplicating units — but NOT all to `Paper3` (amended per review
   finding 5: the original destination would create an import cycle).**  `Paper3/AngularFourierDilation.lean`
   imports only `Paper3.*` + Mathlib, and `Section4.D01.*` imports `Paper3`; so anything that mentions
   `Section4` symbols cannot move to `Paper3` (would make `Paper3 → Section4 → Paper3`).
   - **Only `longitudinal_of_longitudinal_symm` (:435)** is Paper3-level (stated purely for
     `g : Fin 3 → FourierData`) and can join `transverse_of_transverse_symm` (already at
     `Paper3/AngularFourierDilation.lean:297`) — **using lane-109's alias pattern verbatim**
     (`OrderZeroSymbol.lean:476-480`: `alias … := NSFormalization.Paper3.…`; the enclosing-namespace
     alias wins over the file's `open NSFormalization.Paper3`, which is why 109 compiles).  A half-move
     (Paper3 copy, no alias, both namespaces `open`ed) is what produced 109's `Ambiguous term`.
   - `fderiv_zc_eq'` (:59), `cs_ibp` (:67), `physical_weighted_pairing_zero` (:148, re-derive 094's
     `physical_pairing_zero` at `w=δ`, ~90 lines) and `fourier_lineDeriv_apply` (:330) all mention
     `Cut.zc`/`Cut.Pj`/`A03.partialDeriv`/`D01.componentLp` (all `Section4`), so they must go to a
     **new module under `Section4/D01/`**, not `Paper3`.  Then rewrite 079/089/094/108 to consume them.
   Cannot be done in this lane (moves code across modules + edits frozen 094/089).
2. **111 dead code:** `OrderZeroAlgebra.lerayComplement_orderZeroDatum_add`/`_sub` (:97,:106) are now
   only referenced by `research/D01/axioms_sl8_prep.lean:10-11` (`PressureJets:86` uses `map_sub` on
   the CLM directly).  **Kept** (statements frozen for conformance); note for a future contract-cleanup
   lane that they are convenience wrappers, not load-bearing.
3. **`pressureGradient_apply` duplicate:** `MomentumSlice.pressureGradient_apply` (:127) is
   statement-identical (bound var aside) to `A01/PressureGauge.pressureGradient_apply` (106).  Different
   namespaces, no clash; consolidate in a MAINT lane (keep 106's, per REVIEW_SL8_PREP §3). **Not
   changed** (per the brief).
4. **`isSobolevDatum_zero`-style / `datum_zero` helper written by ≥3 lanes:** the "zero field is an
   order-0 datum" helper is re-proved in each reviewer's non-vacuity file (108/111/117) and again here
   (`negative_simp_p2.lean:datum_zero`).  A shared witness lemma in a test-support module would retire
   the duplication (research-file only, low priority).
5. **Transverse-argument duplication `PressureJets.lean:71-77,97-112` vs
   `A04/PressureDrop.velocity_datum_lerayComplement_eq_zero`:** both apply the order-0 transverse fibre
   fact (`orderZeroDatum_transverse_of_divergence_free` + `lerayComplement_eq_zero_of_transverse`) to a
   divergence-free slice; a shared `transverse-of-divergence-free ⇒ lerayComplement 0 = 0` corollary
   would dedup them.  Cross-module ⇒ MAINT.
6. **`open A02 (… MemForceR)` shadowing** in `MomentumSlice`/`PressureJets` (REVIEW_SL8_PREP F-5): the
   `MemForceR` in the open list is shadowed by `D01.MemForceR`; removable but left (see NEGATIVE note
   above).

## Commands run (all `lake` from `WT/verification`, `LEAN_NUM_THREADS=6`, one at a time)

| command | result |
|---|---|
| baseline `lake build` of the 5 + `A04.PressureDrop` (+ `Tests.DatumLemmasV3`) | green, 0 D01 own-line warnings |
| `lake env lean` on each of the 5 (after every edit + final) | silent, exit 0 (0 bytes) |
| `lake build` of the 5 + `A04.PressureDrop` + `Tests.DatumLemmasV3` (after edits) | `Build completed successfully`; `checkedDatumLemmasV3: checked; standard logical axioms only` |
| `lake env lean` on `axioms_{order_zero,order_zero_curl,sl8_prep,sl8_assembly}.lean` | exit 0; 21 / 14 / 13 / 6 decls each `[propext, Classical.choice, Quot.sound]`; sl8_assembly `example` silent |
| `lake env lean ../research/D01/negative_simp_p2.lean` | **exit 0**, 13 `#print axioms` all standard (incl. `gradBump_ne_zero`, `nonvac_longitudinal_nonzero`, `nonvac_leray_nonzero`, and the counterexample `transverse_without_hdiv_is_false`) |
| `lake env lean ../research/D01/negative_simp_p2_fail.lean` | **exit 1** (as required); 5 blocks, **8 error messages**: 3 `Type mismatch` + 3 `Unknown identifier hw` + 2 `Unknown identifier hf` (Lean emits one message per occurrence, not per block) |
| `git diff` (declaration lines) | every `+`/`-` line is an `open`/`open scoped` line, one docstring cite, or the `fourier_antisym` body; no signature line changed |
| `make check` | exit 0 (contract policy 13/13; 30 work items consistent) |
| `cd verification && make test` | exit 0, 22 contracts "checked; standard logical axioms only" |
