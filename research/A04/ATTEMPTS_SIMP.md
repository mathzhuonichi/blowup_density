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
