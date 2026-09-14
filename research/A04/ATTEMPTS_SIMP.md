# A04 simplifier + tester pass (lane 086, SIMP-A04)

Follow-up lane over the eight earlier-merged A04 modules
`Section4/A04/{Forcing,Continuity,Gronwall,Regularized,DerivNorm,HighEnergy,
TimeDerivative,MomentumDatum}.lean` (eq:Rhigh / Theorem 4.3 high-energy identity:
units F1, N1, G3, Z1, D1, G1, SL1/D2, SL2), per the "After ACCEPT: simplifier and
tester" section of `.claude/skills/lane-review/SKILL.md`, imitating
`research/C01/ATTEMPTS_SIMP.md` (lane 077) and `research/A02/ATTEMPTS_SIMP.md`
(lane 040).  **No new mathematics**; every public statement is byte-identical to
the merged version — verified by a full `git diff` in which every `+`/`-` line is
an `import` or `open`/`open scoped` line (confirmed with a grep that no changed
line contains `theorem`/`lemma`/`def`/`abbrev`/`:=`/`by`/`exact`/`refine`/`rw [`/
`intro`/`obtain`/`have`/`calc`/`nlinarith`/`linarith`).  All 8 modules still
elaborate silently under `lake env lean`, and all six axioms files still report
only `[propext, Classical.choice, Quot.sound]` with every conformance `example`
accepted.

The three SL3-route modules `LaplacianDatum.lean`, `LaplacianPairing.lean`,
`RealPairing.lean` were **not touched** (active lanes), and neither were their
axioms files `axioms_sl3.lean` / `axioms_sl3_pairing.lean`.

Worktree `.claude/worktrees/086-SIMP-A04`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `Forcing.lean` | 175 | 175 | dropped unused `ContDiff` from `open scoped` (token, not a line) |
| `Continuity.lean` | 154 | 153 | removed dead `open scoped ContDiff ENNReal` line |
| `Gronwall.lean` | 216 | 216 | untouched (imports already minimal, lane 041 fix 3; no dead open) |
| `Regularized.lean` | 231 | 228 | removed 3 unused imports (`DominatedConvergence`, `Tactic.Linarith`, `Tactic.Ring`) |
| `DerivNorm.lean` | 157 | 157 | dropped unused `Topology` from `open scoped` (token, not a line) |
| `HighEnergy.lean` | 196 | 195 | removed dead `open Set MeasureTheory` line; dropped unused `ENNReal` |
| `TimeDerivative.lean` | 238 | 237 | removed unused `import Mathlib.Analysis.Calculus.Deriv.Prod`; dropped unused `ENNReal` |
| `MomentumDatum.lean` | 219 | 219 | dropped unused `ENNReal`, `Topology` from `open scoped` (tokens, not lines) |
| **total** | **1586** | **1580** | **−6** |

Net change is small because these modules were already reviewed
(ACCEPT-WITH-NOTES) and build **warning-free**, so there were no dead `have`s,
unused binders, `maxHeartbeats`, or missing docstrings to fix (see "Not
simplified" below).  The value of this pass is the dead-`open`/import removal and
the tester half.

## Method for the open/import removals

Every candidate was decided empirically, not by eye: a scratch copy of the module
with exactly one `open`/`open scoped` target — or one `import` line — removed was
re-elaborated with `lake env lean`; a removal was accepted **only** if the file
still elaborated with zero output (`/tmp/prune_test.py`, one probe per token,
8 modules).  After applying the accepted removals the whole closure was rebuilt
(`Build completed successfully (9896 jobs)`), each of the 8 modules re-checked
silent, and all six axioms files re-run standard-axiom-clean.

## Simplified

* **Dead `open scoped`/`open` targets dropped (task 1).**  Each verified by
  re-elaboration after removal (silent, exit 0), and the combined post-edit build
  re-verified:
  - `Forcing`: `open scoped ContDiff ENNReal` → `open scoped ENNReal`
    (`ContDiff`'s `∞` notation is never typed in code; `ENNReal` kept for the
    `def` types `ℝ≥0∞` / `⊤`).
  - `Continuity`: whole `open scoped ContDiff ENNReal` line removed (neither `∞`
    nor `ℝ≥0∞` is typed in this module's own code — the `ℝ≥0∞` objects come from
    the imported `Forcing` defs; `⊤` is core notation, not from `ENNReal`).
  - `DerivNorm`: `open scoped ContDiff RealInnerProductSpace Topology`
    → `open scoped ContDiff RealInnerProductSpace` (the `𝓝` notation `Topology`
    provided is no longer typed — lane 053's review-fix switch to `Ico_mem_nhds` /
    `Ioo_mem_nhds` lemma applications removed the last literal `𝓝`, but the open
    was left; `ContDiff` kept for `ContDiffOn ℝ ∞`, `RealInnerProductSpace` for
    `⟪·,·⟫`).
  - `HighEnergy`: whole `open Set MeasureTheory` line removed (no `Set`/
    `MeasureTheory` identifier is typed — `Icc`/`Ioo`/`volume`/`eLpNorm` do not
    occur; the tame-transport lemmas use fully-qualified `ENNReal.*` and the A03/
    D01 opens), and `open scoped ENNReal RealInnerProductSpace`
    → `open scoped RealInnerProductSpace` (`ℝ≥0∞` never typed; `ENNReal.*` are
    fully qualified; `RealInnerProductSpace` kept for `⟪·,·⟫`).
  - `TimeDerivative`: `open scoped ContDiff ENNReal Topology`
    → `open scoped ContDiff Topology` (`ℝ≥0∞` never typed; `ContDiff` kept for
    `ContDiffOn ℝ ∞`, `Topology` kept for `𝓝`).
  - `MomentumDatum`: `open scoped ContDiff ENNReal Topology` → `open scoped ContDiff`
    (`ℝ≥0∞` and `𝓝` never typed; `ContDiff` kept for `ContDiffOn ℝ ∞`).
* **Unused imports dropped (task 1).**  Each verified individually and then
  jointly by the post-edit rebuild:
  - `Regularized`: `Mathlib.MeasureTheory.Integral.DominatedConvergence` (no
    dominated/monotone-convergence lemma is used — the `δ↓0` step is
    `le_of_forall_pos_le_add`, not a convergence theorem, so the import was dead
    weight from an earlier draft), `Mathlib.Tactic.Linarith` and
    `Mathlib.Tactic.Ring`.  `linarith`/`nlinarith` are used but reach the file
    transitively through `Mathlib.Analysis.Calculus.Deriv.MeanValue` (the sister
    module `Gronwall.lean` imports neither tactic explicitly and uses both), and
    `ring` is not used at all in `Regularized` (grep: only `linarith`/`nlinarith`
    occur).
  - `TimeDerivative`: `Mathlib.Analysis.Calculus.Deriv.Prod` — no `Deriv.Prod`
    lemma is referenced (the only product used is `contDiff_id.prodMk contDiff_const`,
    which is `ContDiff.prodMk`, from the `ContDiff` files, not `Deriv.Prod`).
* **No `set_option`/`maxHeartbeats` existed in any module** (task 1) — kept that
  way.

## Not simplified, and why

* **No proof body was shortened.**  All eight modules were already reviewed
  (`REVIEW_{F1N1,D1,G1,G3,Z1,SL2}.md`, ACCEPT-WITH-NOTES) with their review fixes
  applied, and build **warning-free**: `lake env lean` on each is silent, so the
  default `unusedVariables` linter finds no dead `have`s or unused binders.  The
  review fixes already removed the shortenable dead steps (e.g. DerivNorm review
  fix 3 deleted a dead `Nat.cast_ofNat` step; F1N1 review fix 3 removed a dead
  `simp only [Nat.cast_ofNat]`; Gronwall's imports were already narrowed by
  lane 041 fix 3).  The remaining multi-step proofs are load-bearing: Gronwall's
  integrating-factor antitone argument, Regularized's `√(E+δ²)` antitone +
  `δ↓0`, TimeDerivative's bounded-representative plumbing, and MomentumDatum's
  datum-linearity chain all have every step used.  Collapsing any into
  `simp`/`positivity`/`gcongr` would risk changing the transitive axioms or
  breaking a byte-identical statement for no verified gain, so none was attempted
  (same finding as lane 077 on C01).
* **Docstrings (task 2): every public theorem/def already carries one naming its
  paper/Spec location.**  Enumerated all 5+7+3+5+5+4+5+5 public declarations; each
  has a `/-- … -/` with a location (`research/A04/Spec.lean:<line>`,
  `paper/sections/appendix-a-local-theory.tex:<line>`, `02-preliminaries.tex`,
  `04-whole-space.tex`, or `research/A04/COMPARISON.md`).  Nothing added or
  changed — inventing or moving a location would violate the "copy locations only
  from ATTEMPTS/REVIEW/existing docstrings" rule, and none was missing.
* **The `research/A04/Spec.lean` restatements were NOT deduped against a canonical
  module (task 3).**  `Forcing.lean §0` restates `sobolevNormAt`,
  `bochnerDatumENorm`, `forceSobolevENorm`, `forceSobolevENormL1`, `MemL1Hm`,
  `BoundedIntoHOne`, and `DerivNorm.lean §0` restates `HasSmoothSobolevPath`, all
  from `research/A04/Spec.lean` / `Contracts/V1/Data.lean`.  Neither source is an
  importable canonical module: `research/A04/Spec.lean` is a draft in `research/`,
  and `formalization/` **cannot** import `Contracts.*` (repo rule).  These are the
  deliberate verbatim fidelity anchors that the conformance files discharge by
  defeq; `bochnerDatumENorm` already carries the `rfl` bridge
  `bochnerDatumENorm_eq_homogeneous` to the in-package D01 copy with a docstring
  explaining it is kept local token-for-token against `Data.lean`.  Same status
  as the C01 §0 restatements (lane 077) — no importable canonical target exists,
  so there is nothing to replace.
* **Removable-but-kept imports (semantic home / hygiene).**  Four imports tested
  REMOVABLE (elaborate silently without them, because a sibling import provides
  them transitively) but were **kept** because each is the direct home of a lemma/
  def the file references by name; importing a lemma's home module directly, even
  when transitively available, is correct build hygiene (as opposed to tactic
  imports and truly-unreferenced imports, which were removed above):
  - `DerivNorm`: `Mathlib.Analysis.InnerProductSpace.Calculus` — home of
    `HasDerivAt.norm_sq` (the D1 core).
  - `HighEnergy`: `Mathlib.Analysis.InnerProductSpace.Basic` — home of
    `real_inner_le_norm`, `inner_add_right`, `inner_sub_right`,
    `real_inner_smul_right`.
  - `TimeDerivative`: `NSFormalization.Section4.A03.ScalarTameProduct` — home of
    `IsScalarSobolevDatum`, `representative_ae`, `locallyIntegrable_ofReal`
    (opened at line 79; defined in `ScalarTameProduct.lean:71,146,156`), and
    `NSFormalization.Paper3.AngularTameProduct` — home of
    `angularBoundedRepresentative`, `angularRealization_boundedRepresentative`.
  - `MomentumDatum`: `NSFormalization.Section4.A03.VectorTameProduct` — home of
    `isSobolevDatum_add`/`_sub`, `IsSobolevDatum.unique`, `locIntField_of_memLp`
    (redundant only because it also arrives through `TimeDerivative`).

## For the MAINT lane (do NOT do here — changes namespaces)

`NEXT_SESSION.md` records "datum 线性引理搬到 A03" (move the datum-linearity lemmas
from A04 to A03).  Those lemmas, added by lane 065 in the **A04** namespace inside
`Section4/A04/MomentumDatum.lean`, are:

| lemma | line |
|---|---|
| `isScalarSobolevDatum_smul` | `MomentumDatum.lean:116` |
| `isSobolevDatum_smul` | `MomentumDatum.lean:132` |
| `isScalarSobolevDatum_neg` | `MomentumDatum.lean:140` |
| `isSobolevDatum_neg` | `MomentumDatum.lean:146` |

They are the scalar/vector `smul` companions of the existing
`A03.isScalarSobolevDatum_add`/`_sub` and their `c = −1` negations.  Moving them
to `Section4/A03` renames them `A03.*` (a namespace change and an edit to a
frozen-by-convention A03 file), so it is out of scope for this simplifier lane and
left for the MAINT lane; they are **not** touched here.

## Negative-check results (task B.2; edits done only in `/tmp` scratch copies —
the modules were never touched)

Method (`/tmp/neg_check.py`): each scratch is a whole-module copy with
`set_option autoImplicit false` inserted right after the `namespace` line and
exactly one hypothesis of the module's main theorem removed.  A **control** run
(autoImplicit off, hypothesis kept) elaborated **silently for all eight modules**
(exit 0, 0 output lines) — so `autoImplicit false` does not itself distort these
modules, and the removed hypothesis names do not reappear in the statement type
(the lane-077 vacuous-pass trap does not apply here).  Then the removal run:

| module | main theorem | hypothesis dropped | result (removal run) |
|---|---|---|---|
| `Forcing` | `memL1Hm_of_memForceR` | `hf : MemForceR f` | exit 1, `143:37 Unknown identifier hf` (the `hf.2 m` destructure) |
| `Continuity` | `intervalIntegrable_highContinuationIntegrand` | `htT : t < T` | exit 1, `144:94 Unknown identifier htT` (the `hsub` `lt_of_le_of_lt hx.2 htT`) |
| `Gronwall` | `gronwall_integral` | `hcnn : ∀ t ∈ Icc t₀ t₁, 0 ≤ c t` | exit 1, `126:28 Unknown identifier hcnn` (+ `149`, `183`) |
| `Regularized` | `sqrt_le_primitive_linear` | `hdE : ∀ t ∈ Ioo t₀ t₁, HasDerivAt E (E' t) t` | exit 1, `175:8 Unknown identifier hdE` |
| `DerivNorm` | `exists_hasDerivAt_sobolevNormAt_sq` | `h : HasSmoothSobolevPath T u` | exit 1, `149:26 Unknown identifier h` (the `h m` destructure) |
| `HighEnergy` | `inner_energy_assembly` | `hpr : ⟪G, P⟫ = 0` | exit 1, `113:72 Unknown identifier hpr` + `111:59 unsolved goals` (pressure term no longer drops) |
| `TimeDerivative` | `timeDeriv_isSobolevDatum` | `hm : 2 ≤ m` | exit 1, `193:52 Unknown identifier hm` (the `hsR := by exact_mod_cast hm`) |
| `MomentumDatum` | `momentum_datum` | `hP : IsSobolevDatum m (∇p(t,·)) P` | exit 1, `192:41 Unknown identifier hP` + `181:37 unsolved goals` |

Every hypothesis is load-bearing.  Two are additionally interesting:
`inner_energy_assembly`'s `hpr` (`⟪G,P⟫ = 0`, solenoidality) leaves an
`unsolved goals` because without it the momentum expansion keeps a `−⟪G,P⟫` term
and eq:Rhigh's RHS is genuinely unprovable; `momentum_datum`'s `hP` is the D01 P2
(Leray-regularity L9(c)) obligation, and its removal leaves the datum-linearity
`sub` step and the uniqueness closer unsolvable.

## Conformance (task B.1; every spec field the lane claims fully/partially
discharged has an `example` discharged by the theorem, no extra hypotheses)

| spec field (`research/A04/Spec.lean`) | conformance `example` | discharging theorem |
|---|---|---|
| `MemL1Hm` free from `MemForceR` (unit F1a; `Spec.lean:268`) | `axioms_f1n1.lean:75` `f1a_memL1Hm_of_memForceR` | `Forcing.memL1Hm_of_memForceR` |
| `BoundedIntoHOne` free from `MemForceR` (unit F1b; `Spec.lean:286`) | `axioms_f1n1.lean:80` `f1b_exists_boundedIntoHOne_of_memForceR` | `Forcing.exists_boundedIntoHOne_of_memForceR` |
| `highContinuationIntegral` `IntervalIntegrable` conjunct (unit N1; `Spec.lean:499-504`) | `axioms_f1n1.lean:118` `n1_intervalIntegrable_highContinuationIntegrand` | `Continuity.intervalIntegrable_highContinuationIntegrand` |
| `energyIdentityHigh` LHS `∃ d, HasDerivAt (‖u‖²_{H^m}) d t` conjunct (unit D1; `Spec.lean:429`) | `axioms_d1.lean:81` `d1_energyIdentityHigh_lhs` (+ `:63` `d1_exists_hasDerivAt_sobolevNormAt_sq`) | `DerivNorm.exists_hasDerivAt_sobolevNormAt_sq` |
| SL2 `hmom` feeding `inner_energy_assembly` (G1 assembly interface, `Spec.lean:424-434`) | `axioms_sl2.lean:36` composed `example` | `MomentumDatum.momentum_datum` + `HighEnergy.inner_energy_assembly` |

Supporting N1 finiteness/continuity examples (spec vocabulary, no extra
hypotheses): `axioms_f1n1.lean:88` `n1_sobolevENorm_velocity_ne_top`, `:96`
`n1_sobolevENorm_force_ne_top`, `:102` `n1_continuousOn_sobolevNormAt_velocity`,
`:110` `n1_continuousOn_sobolevNormAt_force`.  Each existing example is discharged
with the theorem applied to exactly the spec field's own hypotheses — e.g.
`d1_energyIdentityHigh_lhs` carries the field's `3 ≤ m`, the F1 examples carry
only `MemForceR`, the N1 example carries the field's `0 ≤ t₀ → t₀ ≤ t → t < T` —
so **no extra hypothesis is smuggled in and no claimed field is weakened**.  No
missing example was found, so none was added.

The remaining units are **not** full spec-field discharges and correctly have no
conformance `example`, only a `#print axioms` audit (matching the C01 precedent
that infrastructure/sub-lemmas need no `example`):

* **G1** (`HighEnergy.inner_energy_assembly`/`inner_energy_Rhigh`,
  `outerSobolevNormAt_le`/`outerNormAt_le`) is rated **L**; only its **S**
  sub-steps are proved, so `energyIdentityHigh` as a whole is not discharged.
  Audited by `axioms_g1.lean`.
* **SL1/D2** (`TimeDerivative.d2_scalar`, `timeDeriv_isSobolevDatum`) is a G1
  sub-lemma; audited by `axioms_g1.lean` and consumed by the `axioms_sl2.lean`
  composed `example`.
* **G3** (`Gronwall.gronwall_integral`/`_deriv`/`_integral_mul`) is a pure
  real-analysis tool for the Grönwall consequence fields; audited by
  `axioms_g3.lean`.
* **Z1** (`Regularized.*`) is the ζ-device building block for
  `regularizedNormDerivative` / `highContinuationIntegral`; audited by
  `axioms_z1.lean`.  (`regularizedNormDerivative` itself also needs the D1
  `HasDerivAt` and the L-blocked eq:Rhigh bound, so Z1 alone does not discharge
  it — the ATTEMPTS_Z1 record does not claim it does.)

## CI closure (task B.3)

`grep` confirms **no** `verification/{Bindings,Tests,Contracts}` module imports
`NSFormalization.Section4.A04.*`, so the eight modules are **not** in a
registered-contract Tests closure — same status as A02 (lane 040) and C01
(lane 077).  `experiments/build_changed_lean.py --base-ref <ref>` maps every
changed `.lean` under `formalization/` to its module name and runs `lake build`
on it, so CI's changed-module step rebuilds all eight whenever this lane changes
them (all eight are under `formalization/`).  *For the next contract bundle:* fold
the eight A04 modules into the Tests closure when the A04 (`ContinuationAPI`)
contract is registered.

## Commands run (all `lake` from `WT/verification`, one at a time)

| command | result |
|---|---|
| `lake build …A04.{MomentumDatum,HighEnergy,DerivNorm,Gronwall,Regularized}` (pre-edit baseline, then again post-edit) | `Build completed successfully (9896 jobs)` both times; the only warnings are from dependency `Source.*`/`Paper3.*` modules, none on A04 lines |
| `lake env lean` on each of the 8 modules (pre- and post-edit) | each silent, exit 0 (0 output lines) |
| `lake env lean ../research/A04/axioms_d1.lean` | 7 declarations, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A04/axioms_f1n1.lean` | 10 declarations, all standard; all conformance examples accepted |
| `lake env lean ../research/A04/axioms_g1.lean` | 6 declarations (inner_energy_assembly/Rhigh, outerSobolevNormAt_le/outerNormAt_le, d2_scalar, timeDeriv_isSobolevDatum), all standard |
| `lake env lean ../research/A04/axioms_g3.lean` | 3 declarations, all standard |
| `lake env lean ../research/A04/axioms_sl2.lean` | 5 declarations standard + the composed `example` (SL2 → `inner_energy_assembly`) type-checks |
| `lake env lean ../research/A04/axioms_z1.lean` | 5 declarations, all standard |
| `git diff` (signatures) | every changed line is an `import`/`open`/`open scoped`; no signature or proof line changed |
| negative checks (8 `/tmp` scratches) | all controls silent (exit 0); all removals break as tabled above |
| `make check` | see final report |

---

# Lane 115 — SL3 cluster

Simplifier + tester pass over the four SL3-route modules
`Section4/A04/{LaplacianDatum,LaplacianPairing,RealPairing,LaplacianAssembly}.lean`
(units SL3 step 1/2/3a/3b: the dissipation identity `hlap` on the datum carrier).
These are exactly the modules lane 086 left untouched ("active lanes"); lane 086's eight
modules are **not** revisited here.  Base `erenup/integration`; worktree
`.claude/worktrees/115-SIMP-A04`.

**No new mathematics; every exported statement is byte-for-byte identical to the merged
version.**  Verified by full `git diff`: every changed `+`/`-` line is an `open`/`open scoped`
line (a grep for `theorem`/`lemma`/`def`/`abbrev`/`:=`/`by`/`exact`/`refine`/`rw`/`intro`/
`have`/`calc`/`linarith`/`ring`/`import` on the changed lines returns nothing but the four
`open`/`open scoped` edits).  All four modules still elaborate silently under `lake env lean`,
and all four SL3 axioms files still report only `[propext, Classical.choice, Quot.sound]`.

## Line counts (before → after)

| module | before | after | what was removed |
|---|---|---|---|
| `LaplacianDatum.lean` | 138 | 137 | dropped dead `open Set`, `open MeasureTheory`, whole `open scoped ENNReal` line (−1 line), and dead `columnsSobolevENorm` from the A03 open-list |
| `LaplacianPairing.lean` | 199 | 199 | dropped dead `ComplexConjugate`, `ENNReal` from `open scoped` (tokens, not lines) |
| `RealPairing.lean` | 225 | 225 | dropped dead `ENNReal` from `open scoped` (token, not a line) |
| `LaplacianAssembly.lean` | 370 | 369 | dropped dead `open Set`, and whole dead `open scoped ENNReal InnerProductSpace ComplexConjugate` line (−1 line) |
| **total** | **932** | **930** | **−2 lines, 11 dead open/scoped-open tokens removed** |

Net line change is small (these modules were reviewed ACCEPT-WITH-NOTES and already build
warning-free — no dead `have`s, unused binders, `maxHeartbeats`, or missing docstrings), so the
value is the dead-`open` removal and the tester half.  Same shape as lane 086's finding on the
other eight A04 modules.

## Method for the open removals

Every candidate was decided empirically, not by eye (`/tmp/prune_probe.py`, one scratch per
`open`/`open scoped`/`import` token): a copy of the module with exactly one token removed was
re-elaborated with `lake env lean`, and a removal was accepted **only** if the file still
elaborated with exit 0 and **zero output**.  After applying the accepted removals the whole
closure was rebuilt (`Build completed successfully (9897 jobs)` — identical job count to the
pre-edit baseline, confirming the closure is unchanged: every removed open was already available
transitively) and each of the four modules re-checked silent.

## Simplified (all four dead-open removals verified individually then jointly)

* `LaplacianDatum`: `open Set MeasureTheory NavierStokes.ProblemStatement` → `open
  NavierStokes.ProblemStatement` (`Set`/`MeasureTheory` identifiers are never typed here — no
  `Icc`/`Ioo`/`volume`/`eLpNorm`; `ProblemStatement` kept for `Space`); whole `open scoped
  ENNReal` line deleted (`ℝ≥0∞` is never typed and the `⊤` in `≠ ⊤` is core `Top.top`, not from
  the `ENNReal` scope); `columnsSobolevENorm` dropped from the A03 open-list (used only fully
  qualified, as `A03.columnsSobolevENorm_toReal_sq_eq_sum` at `:101`).
* `LaplacianPairing`: `open scoped InnerProductSpace ComplexConjugate ENNReal` → `open scoped
  InnerProductSpace` (`conj` and `ℝ≥0∞` never typed — the module uses `⟪·,·⟫_ℂ` and
  `map_mul`/`mid_symbol_imaginary`; `InnerProductSpace` kept for the `⟪·,·⟫` notation).
* `RealPairing`: `open scoped InnerProductSpace ComplexConjugate ENNReal` → `open scoped
  InnerProductSpace ComplexConjugate` (`ℝ≥0∞` never typed; `ComplexConjugate` kept — `conj`
  is used 8×; `InnerProductSpace` kept for `⟪·,·⟫`).
* `LaplacianAssembly`: `open Set MeasureTheory NavierStokes.ProblemStatement` → `open
  MeasureTheory NavierStokes.ProblemStatement` (`Set` never typed); whole `open scoped ENNReal
  InnerProductSpace ComplexConjugate` line deleted — this module writes `inner ℝ …` explicitly
  (5×) and never types `⟪·,·⟫`, `conj`, or `ℝ≥0∞`, so all three scoped notations are dead.

## Not simplified, and why

* **No proof body was shortened, and no import was removed.**  Findings 1–2 of `REVIEW_SL3.md`
  (the avoidable `maxHeartbeats 400000` at the old `LaplacianDatum.lean:106` and the redundant
  `hfin` hypothesis) were **applied in lane 066 itself, in response to that review, before merge**
  (`REVIEW_SL3.md` reviewed the pre-merge commit `e779166`; the merged 066 commit `8e4450e`
  already has no `set_option` in `LaplacianDatum.lean` and already derives `hfin` internally) — no
  later lane was involved.  Lane 109 (`38585d4`) only re-pointed
  `gradientSobolevENorm_toReal_sq_eq_sum` at the promoted `A03.columnsSobolevENorm_toReal_sq_eq_sum`.
  In the current file `gradientSobolevENorm_toReal_sq_eq_datum_sum` derives its `hfin` internally
  (`:128`).  The remaining proofs (the calc transports across the unitary `U`,
  the three-way symbol `ring`s, the datum order-cast bookkeeping) are load-bearing and reviewed;
  collapsing any risks the transitive axioms or a byte-identical statement, so none was attempted
  (same conclusion as lane 086 / lane 077).
* **Removable-but-kept imports (semantic home / hygiene, matching lane 086).**  Several `import`s
  probed REMOVABLE (they arrive transitively through `import …RealPairing`, whose chain
  `RealPairing → LaplacianPairing → LaplacianDatum → {HighEnergy, DerivativeDatum} → A03/…`
  already pulls the whole closure — hence the unchanged 9897-job count), but each is the **direct
  home of a declaration the file references by name**, so it is kept as build hygiene, exactly as
  lane 086 kept its four semantic-home imports:
  - `RealPairing`: `D01.DerivativeDatum` — home of `angularDirectionalDerivativeReal`
    (`DerivativeDatum.lean:134`) and `angularDirectionalDerivativeReal_coe` (`:141`), both used.
  - `LaplacianAssembly`: `A04.LaplacianDatum` (home of `gradientSobolevENorm_toReal_sq_eq_datum_sum`,
    `gradientSobolevNormAt`, used `:338`/`:362`/`:366`), `D01.DerivativeDatum` (home of
    `isSobolevDatum_partialDeriv`), `A03.VectorTameProduct` (home of `isSobolevDatum_iff`),
    `A03.ScalarTameProduct` (home of `IsScalarSobolevDatum(.lower)`), `A03.RealAngularProduct`
    (home of `coe_lowerDatum`), `A05.SmoothJets` (home of `SmoothL2`, `SmoothJets.lean:44`).
    `import …LaplacianDatum` and `import …HalfOrder` are additionally *not* removable
    (`HalfOrder` is the only source of `lowerVectorL`; `import …RealPairing` is required for the
    operators).
  Removing any of these would not shrink the build closure (all stay in it via `RealPairing`),
  only delete a redundant edge that documents a genuine semantic dependency, so keeping is the
  cleaner engineering choice.
* **No `alias` statements exist in these four modules.**  Lane 109's "aliases" for the promoted
  Paper3-level facts are the *delegating* theorems (`gradientSobolevENorm_toReal_sq_eq_sum` at
  `LaplacianDatum.lean:95` forwarding to `A03.columnsSobolevENorm_toReal_sq_eq_sum`); these are
  exported statements kept byte-identical, not touched.

## Negative-check results (task 2c) — REVISED after `REVIEW_SIMP_SL3.md` (Findings 3–4)

The reviewer's ruling: the original single-file, seven-block check was **weak evidence**.  N1–N4
dropped a binder but left the proof term citing it, so they failed with `Unknown identifier` — the
"you can't name a hypothesis you didn't assume" failure mode, which a purely-decorative hypothesis
would produce identically; N5–N7 weakened the conclusion but still cited the real theorem, so they
failed with a `Type mismatch` that only pins the exported *shape*, not the *truth* of the
weakening.  Neither shows a hypothesis is load-bearing.  The conclusions are nonetheless true, and
the reviewer proved them **by collapse**; that evidence is now transcribed, and the file is **split
into two** (mirroring lane 113's repair):

* **`research/A04/negative_simp_sl3.lean` — MUST COMPILE SILENTLY** (the genuine load-bearing
  evidence).  For each weakened claim, a closed `Prop` `Weakened*` and a *proved* theorem that it
  entails something manifestly false:
  - `WeakenedNoHL` (`inner_datum_laplacian_le'` minus `hL`) ⇒ `datum_zero_of_weakenedNoHL` /
    `physical_pairing_zero_of_weakenedNoHL`: every smooth `L²` field vanishes distributionally
    (take `L := G`, so `‖G‖² ≤ -‖∇u‖² ≤ 0`).  **`hL` load-bearing.**
  - `WeakenedPairing` (`real_inner_angularDirectionalDerivative` minus the minus) ⇒
    `deriv_eq_zero_of_weakenedPairing` / `distributional_deriv_zero_of_weakenedPairing`:
    `angularDirectionalDerivative s a = 0` at every order/direction.  **The sign is load-bearing**
    (same argument for the ℂ export `inner_angularDirectionalDerivative_right`, of which the real
    one is the real part — so N7's export is covered too).
  - `WeakenedN1` (`gradientSobolevENorm_toReal_sq_eq_datum_sum` minus `hA`) ⇒
    `gradient_zero_of_weakenedN1` (`A := 0`): `‖∇Z‖_{H^m} = 0` for every smooth `L²` field.
    **`hA` load-bearing.**
  - §4 **fidelity** examples: each `Weakened*` is exactly the named export with the one
    hypothesis (or the sign) restored — proved by `exact <real export>` — so the collapse premises
    are faithful weakenings, not strawmen.
  - `#print axioms` on all five collapse theorems (and `unitBall_ne_zero`) →
    `[propext, Classical.choice, Quot.sound]`.
* **`research/A04/negative_simp_sl3_fail.lean` — MUST FAIL** (weaker checks, labelled as such).
  N1–N7 are the original signature/drift checks (kept because they still guard the exported
  statement against silent drift), plus the reviewer's two **controls** C1/C2: the collapse
  *conclusions* (`datum = 0`, `D_a f = 0`) stated WITHOUT the weakened hypothesis — `simp` / `aesop`
  cannot prove them, which is why the collapse proofs genuinely use `H`.  Errors, verbatim:

  | block | export / control | failure |
  |---|---|---|
  | N1 | `gradientSobolevENorm_toReal_sq_eq_datum_sum` (drop `hA`) | `:57:48: error(lean.unknownIdentifier): Unknown identifier hA` |
  | N2 | `inner_datum_laplacian` (drop `hA`) | `:66:33: … Unknown identifier hA` |
  | N3 | `inner_datum_laplacian_le'` (drop `hL`) | `:78:44: … Unknown identifier hL` |
  | N4 | `isSobolevDatum_laplacian` (drop `hA`) | `:84:29: … Unknown identifier hA` |
  | N5 | `real_inner_lowering_pairing` (drop `^2`) | `:92:2: error: Type mismatch … ‖…‖ ^ 2 vs ‖…‖` |
  | N6 | `real_inner_angularDirectionalDerivative` (drop `-`) | `:99:2: error: Type mismatch … -⟪…⟫_ℝ vs ⟪…⟫_ℝ` |
  | N7 | `inner_angularDirectionalDerivative_right` (drop `-`) | `:105:2: error: Type mismatch … -⟪…⟫_ℂ vs ⟪…⟫_ℂ` |
  | C1 | control: `datum = 0` without `WeakenedNoHL` | `:113:2: error: simp made no progress` |
  | C2 | control: `D_a f = 0` without `WeakenedPairing` | `:119:2: warning: aesop: failed to prove the goal after exhaustive search`; `:118:46: error: unsolved goals` |

**Technique note (reviewer + a `LESSONS.md` candidate):** `exact?` is **not** usable on this
cluster — it hits `(deterministic) timeout at whnf, 1000000 heartbeats` on `WeakenedNoHL`
(`/tmp/rev115/p1_assembly_nohL.lean`).  Refutation-by-collapse, not `exact?`, is the right
technique here.  The N1 collapse additionally needed a repair the reviewer left open (`p5`): the
`A := 0` datum-sum term is elaborated at `RealSobolevHilbert (↑m+1-1)`, defeq to `↑m` only at
`default` transparency, so `WithLp.toLp_zero` will not fire; routing the norm through the in-module
`derivDatumStep` / `norm_sq_derivDatumStep` (which passes through `angularDirectionalDerivative` on
`Lp`, where no order cast appears) closes it — `gradient_zero_of_weakenedN1` above.
`autoImplicit false` on every block still guards the 077 silent-rebind trap.

## Non-vacuity (task 2d) — strengthened per `REVIEW_SIMP_SL3.md` Finding 5

Finding 5: the original `V0/V2/V3/V4` were witnessed by *trivial* objects (zero field, `0 : Lp`,
`s=r=t=0`), which show the classes non-empty but never exercise the identities on anything where
they say more than `0 = 0`.  `V1` was already strong.  The must-compile file
`research/A04/negative_simp_sl3.lean` §5 now carries the reviewer's non-degenerate witnesses
(`/tmp/rev115/p4_nonvacuity.lean`, verbatim):

* `V0` — `Nonempty (SmoothL2Field Space)` (zero field) — kept purely to show `V1`'s `∀ Z` is not
  over an empty class.
* `V1` (strong) — for **any** `Z : SmoothL2Field Space` and any `m`, the three datum hypotheses of
  `inner_datum_laplacian(_le)` / `gradientSobolevENorm_toReal_sq_eq_datum_sum` /
  `isSobolevDatum_laplacian` hold *simultaneously* at orders `m`, `m+1`, `m+2`
  (`D01.smoothAngularDatum_isSobolevDatum`).
* `unitBall := indicatorConstLp 2 (ball 0 1) 1`, with `unitBall_ne_zero` proved (via
  `norm_indicatorConstLp` + `measure_ball_pos`, standard axioms) — a genuinely **nonzero** `L²`
  carrier element.
* strict pairwise-distinct orders `∃ s r t, r < s ∧ t < s ∧ (r+t)/2 < s ∧ r ≠ t` (`1, 0, -1`).
* both pairing exports run **on `unitBall` at strict, unequal orders `s=1, r=0, t=-1`** and a
  **nonzero direction `coordinateVector 0`**: `real_inner_lowering_pairing 1 0 (-1) … unitBall` and
  `real_inner_angularDirectionalDerivative 1 (coordinateVector 0) unitBall unitBall` both
  type-check — the identities hold on a non-degenerate input, not just on `0`.

Verified: `lake env lean ../research/A04/negative_simp_sl3.lean` → **exit 0, output is only the six
`#print axioms` lines** (all `[propext, Classical.choice, Quot.sound]`), i.e. every collapse
theorem, fidelity example and non-vacuity witness elaborates cleanly.

## Conformance (task 2b) re-run after the edits

| axioms file | result |
|---|---|
| `axioms_sl3.lean` | 21 declarations, each exactly `[propext, Classical.choice, Quot.sound]` |
| `axioms_sl3_pairing.lean` | 10 declarations, all standard |
| `axioms_sl3_real.lean` | 11 declarations, all standard |
| `axioms_sl3_assembly.lean` | 20 declarations, all standard |

## For the MAINT lane (do NOT do here — changes namespaces / files)

Paper3-/D01-level facts still living in these `Section4/A04/` files that a later MAINT lane could
promote (name — current `file:line` — suggested home):

| declaration | file:line | note / suggested home |
|---|---|---|
| the whole `LaplacianPairing.lean` body | namespace `NSFormalization.Paper3`, `:46`–`:199` | 10 Paper3-namespace angular-operator (skew/self-)adjointness facts living in an `A04` file — a MAINT lane could move to a `Paper3/` module (near `AngularFourierDilation`/`SobolevDirectionalDerivative`) |
| the whole `RealPairing.lean` body | namespace `NSFormalization.Paper3`, `:56`–`:225` | 11 Paper3-namespace real-inner-product operator facts in an `A04` file — same MAINT home |
| `real_inner_eq_re_complex` | `RealPairing.lean:66` | a general `Lp ℂ 2 volume` real↔complex inner-product bridge (not SL3-specific) — belongs in a general real-inner-product Sobolev module |
| `realSobolev_inner_eq_ambient` | `RealPairing.lean:77` | general `RealSobolevHilbert`↔ambient inner bridge (`rfl`) — general Source.RealSobolev / A03 fact |
| `isSobolevDatum_castOrder`, `castOrder`, `castOrder_coe` | `LaplacianAssembly.lean:80,86,232` | generic order-transport of a Sobolev datum — D01-datum-level fact, could go to `D01` |
| `isSobolevDatum_lowerVectorL`, `coe_lowerVectorL` | `LaplacianAssembly.lean:218,226` | the file's own docstring says to replace `isSobolevDatum_lowerVectorL` with the merged `D01.isSobolevDatum_lower` (lane 085, `D01/LerayLowering.lean`) once it lands; both are D01 `lowerVectorL` (HalfOrder) facts |
| `angularMid_comm`, `directionalDerivative_orderLowering_comm` | `LaplacianAssembly.lean:184,201` | Paper3-level operator-commutation facts (`D_j ∘ Λ = Λ ∘ D_j`) — could go to `Paper3/` next to the middle-operator machinery |

**Reviewer's MAINT finding (`REVIEW_SIMP_SL3.md` Finding 6 — the `LaplacianPairing`/`RealPairing`
move is stronger than this lane reported):**

1. **There is already a back-edge from D01 into A04.**  `Section4/D01/LerayLowering.lean` (lane
   085, commit `3c0c132`) has `import NSFormalization.Section4.A04.LaplacianPairing` and
   `import NSFormalization.Section4.A04.RealPairing`, and consumes
   `angularOrderLowering_eq_dilation_mid`, `angularOrderLoweringMid_coeFn`, `lowering_mid_symbol_eq`
   and `angularOrderLowering_self` (`LerayLowering.lean:105–135`).  D01 is the *root* of the
   critical chain (D01 → A01 → A02 → A04), so this is a genuine inverted module edge, not a
   cosmetic namespace mismatch.
2. **Neither file actually depends on A04.**  `grep -n 'Section4.A04' LaplacianPairing.lean
   RealPairing.lean` returns only the `import` lines and two docstring mentions — no `Section4.A04`
   declaration is used; `LaplacianPairing`'s sole import (`A04.LaplacianDatum`) is pure transport
   of the Paper3/Source closure.  So the MAINT move is clean: re-point the two imports at the real
   `Paper3/`/`Source/` modules and the bodies relocate with no mathematical change.
3. **No name collisions.**  All 21 `NSFormalization.Paper3` declarations introduced in these two
   A04 files were checked against every other `def`/`theorem`/`lemma`/`abbrev` in
   `formalization/NSFormalization`: zero duplicates; nothing under `Paper3/`/`Source/` imports
   `Section4.*`, so the target layer stays acyclic.  **Recommended MAINT scope:** move the two
   bodies to `Paper3/` (near `AngularFourierDilation` / `SobolevDirectionalDerivative`), re-point
   `D01/LerayLowering.lean`, `A04/LaplacianAssembly.lean`, `A04/NonlinearPairing.lean`, and re-run
   `axioms_sl3_pairing.lean` / `axioms_sl3_real.lean` (they cite these names unqualified — the
   namespace is unchanged, so they keep working).

None of these are moved here (namespace/file changes are out of scope for a simplifier lane).

## Commands run (all `lake` from `WT/verification`, one at a time; env sourced first)

| command | result |
|---|---|
| `lake build …A04.{LaplacianDatum,LaplacianPairing,RealPairing,LaplacianAssembly,NonlinearColumns,NonlinearPairing}` (pre- and post-edit) | `Build completed successfully (9897 jobs)` both times |
| `lake env lean` on each of the four modules (post-edit) | each silent, exit 0 (0 output lines) |
| `lake env lean ../research/A04/axioms_sl3.lean` | 21 decls, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A04/axioms_sl3_pairing.lean` | 10 decls, all standard |
| `lake env lean ../research/A04/axioms_sl3_real.lean` | 11 decls, all standard |
| `lake env lean ../research/A04/axioms_sl3_assembly.lean` | 20 decls, all standard |
| `lake env lean ../research/A04/negative_simp_sl3.lean` (must-compile) | exit 0; output is only the six `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/A04/negative_simp_sl3_fail.lean` (must-fail) | exit 1; one error per block: N1–N4 `Unknown identifier` at `:57/:66/:78/:84`, N5–N7 `Type mismatch` at `:92/:99/:105`, controls C1/C2 at `:113/:118` (`simp made no progress`; `aesop failed`) |
| `git diff` (four modules) | every changed line is an `open`/`open scoped` line; no signature/proof line changed |
| `make check` | exit 0 (plan, contracts, contract policy 13/13, work queue: "30 work items … consistent") |
| `make test` (`lake -d verification test`, from repo root) | exit 0; all 19 registered `Tests.*` contracts (incl. `Tests.EnergyAbsorptionPartial`) report "checked; standard logical axioms only"; 0 `error:` lines |
