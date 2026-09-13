# R42 simplifier + tester pass (lane 107, SIMP-R42)

Follow-up lane over the **seven merged** R42 modules
`Section4/R42/{Assembly,Lifespan,CorrectionPath,PressureGradient,BlowupEssSup,SolutionOnShorter,FullHorizon}.lean`
(lanes 073/072/075/083/080/087/098), per the "After ACCEPT: simplifier and
tester" section of `.claude/skills/lane-review/SKILL.md`, imitating
`research/D01/ATTEMPTS_SIMP.md` (104), `research/B02/ATTEMPTS_SIMP.md` (090) and
`research/A04/ATTEMPTS_SIMP.md` (086).  **No new mathematics**; every public
statement is **byte-identical** to the merged version — verified by a full
`git diff` restricted to signature lines (every `+`/`-` line is an `open` /
`open scoped` line; no `theorem`/`def`/`lemma` signature line and no proof-body
line changed) and by re-running all seven conformance/axioms files (standard
three axioms only, all decls) plus the 18/18 `make test`.

Worktree `.claude/worktrees/107-SIMP-R42`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `Assembly.lean` | 193 | 192 | −1 unused `open` line (`NSFormalization.Source.LocalizedInsertion`); dropped `MeasureTheory` from the prelude line |
| `Lifespan.lean` | 225 | 225 | dropped `Set`, `Topology` from the prelude line (token edit) |
| `CorrectionPath.lean` | 206 | 206 | dropped `MeasureTheory`, `Filter` (prelude), `ENNReal`, `SchwartzMap` (scoped) |
| `PressureGradient.lean` | 188 | 187 | −1 unused `open` line (`NSFormalization.Section4.A02`); dropped `Filter` (prelude), `ENNReal` (scoped) |
| `BlowupEssSup.lean` | 155 | 155 | dropped `Topology` (prelude), `ENNReal` (scoped) |
| `SolutionOnShorter.lean` | 161 | 161 | dropped `MeasureTheory`, `Filter`, `Topology` (prelude), `ENNReal`, `SchwartzMap` (scoped) |
| `FullHorizon.lean` | 180 | 180 | dropped `MeasureTheory`, `Filter` (prelude), `ENNReal`, `SchwartzMap` (scoped) |
| **total** | **1308** | **1306** | **−2** |

As with the D01/B02/A04 precedents (all sets of already-reviewed,
warning-free modules), the value of this pass is **not** a line-count reduction:
these seven modules were already warning-free (`lake env lean` silent on each),
`maxHeartbeats`/`set_option`-free (grep: none), and carried a paper-located
docstring on every public theorem before the lane began.  The substantive output
is (a) the verified removal of the unused `open`s tabled below, and (b) the
tester half (seven negative checks, the conformance and split-obligation tables,
the open-exports list, the MAINT ledger and the CI-closure statement).

## Simplified (task 1) — unused `open`s dropped, each verified empirically

Every removal was chosen empirically: a per-token probe removed one open token at
a time and re-elaborated with `lake env lean` (kept only if the file stayed
error-free), then the **combined** removal per module was re-verified (full
`lake build`, `lake env lean` silent + exit 0, and the axioms file unchanged), so
no "mutual-alias" combination slipped through.  Removed:

* **Unused scoped notation opens** — the notation each provides has **zero** code
  occurrences (grep; the only `𝓝`/`ℝ≥0∞` hits in the affected files are inside
  docstrings/comments):
  - `open scoped SchwartzMap` (provides `𝓢`, `𝓢'`): removed from
    `CorrectionPath`, `SolutionOnShorter`, `FullHorizon` (`𝓢` count 0 in each;
    `D01.SchwartzPairable` is a *def name*, needs no notation).
  - `open scoped ENNReal` (provides `ℝ≥0∞`): removed from `CorrectionPath`,
    `PressureGradient`, `BlowupEssSup`, `SolutionOnShorter`, `FullHorizon`.  In
    `BlowupEssSup` the `⊤` (14×) is the core `OrderTop` notation, **not**
    ENNReal-scoped; in `PressureGradient` the `2` of `MemLp _ 2 volume` is a bare
    `OfNat` literal, not ENNReal notation.  Kept in `Lifespan` (`ℝ≥0∞` used 3× in
    signatures).
* **Unused prelude/namespace opens**:
  - `Assembly`: `MeasureTheory` (no measure name used; `HasCompactSupport`,
    `tsupport` are root, `isBounded`/`exists_pos_norm_le` are Bornology/Metric)
    and `NSFormalization.Source.LocalizedInsertion` (`exact_insertion` lives in
    `Source.Insertion` and resolves through the kept `open NSFormalization.Source`;
    the `import` stays — it is what pulls `exact_insertion` into the closure).
  - `Lifespan`: `Set`, `Topology` (no `Set.*`/`𝓝` in code).
  - `CorrectionPath`: `MeasureTheory`, `Filter` (`filter_upwards` is a tactic,
    `congr_of_eventuallyEq` is dot-method — neither needs the open).
  - `PressureGradient`: `Filter`, and `NSFormalization.Section4.A02` (its theorems
    are about raw `ℝ × Space → ℝ` fields; `pressureGradient`/`Space` come from
    `NavierStokes.ProblemStatement`; the `A02.SolutionClass` *import* stays for
    that transitive vocabulary).
  - `BlowupEssSup`: `Topology` (uses `nhdsWithin`/`Iio` by name, not `𝓝`;
    `A02.limsupLeft`/`A02.speedENorm` resolve through the enclosing
    `NSFormalization.Section4` scope, no open needed).
  - `SolutionOnShorter`: `MeasureTheory`, `Filter`, `Topology`.
  - `FullHorizon`: `MeasureTheory`, `Filter` (kept `Topology`: `𝓝[...]`/
    `mem_nhdsWithin` used in code).

No `import` was removed (each is load-bearing: `Assembly`←`I02.Support`
(`I02.inv_sq_inv`); `Lifespan`←`D01.ForceClass`,`A02.Order`;
`CorrectionPath`←`D01.ForceClass`,`A02.SolutionClass`;
`PressureGradient`←`A02.SolutionClass`; `BlowupEssSup`←`A02.Patch`;
`SolutionOnShorter`←`CorrectionPath`,`PressureGradient`,`D01.DatumToJets`;
`FullHorizon`←`SolutionOnShorter`).

## Not simplified, and why

* **No proof body shortened (task 1).**  All seven modules build warning-free
  before and after (`lake env lean` silent on each), so the default
  `unusedVariables`/`unnecessarySeqFocus`/`unusedSimpArgs` linters find **no** dead
  `have`, unused binder or collapsible tactic on any own line.  The seven negative
  checks confirm each main theorem's tested hypothesis is load-bearing.  Collapsing
  a step to `simp`/`positivity` would risk the transitive axioms or a
  byte-identical statement for no verified gain, so none was attempted — same
  finding as D01/104, B02/090, A04/086.
* **No docstrings added (task 2).**  Every one of the 24 public theorems already
  carries a docstring, and the paper location is named — per theorem where it
  exists (all of `Assembly`; `Lifespan`'s `limsup_eq_top_of_le_add_const`,
  `limsup_eLpNormTop_add_eq_top`, `hasCompactSupport_of_tsupport_subset_ball`,
  `exists_isSobolevDatum_of_contDiff_hasCompactSupport`, `memForceR_insertedForce`,
  `lt_maximalLifespanR_of_regularThrough`; `BlowupEssSup.limsupLeft_speedENorm_eq_top`;
  `FullHorizon.classicalSolutionR_of_inserted_fullHorizon`), and via the
  **module header** (which cites `04-whole-space.tex` with explicit lines) for the
  handful of infrastructure lemmas whose own docstring names the split item they
  feed rather than repeating a `tex` line
  (`Lifespan.eLpNormTop_le_ofReal`/`eLpNormTop_le_add`; `CorrectionPath`'s two;
  `PressureGradient`'s `memLp_*`; `BlowupEssSup.ofReal_le_eLpNormTop_of_continuous`;
  `FullHorizon.exists_datumPath_of_forall_shorter`).  The task's rule is "copy
  locations only … never invent"; fabricating fresh `tex` lines for these
  helpers is over-engineering (硬规矩 #1) and would churn reviewed files, so none
  was added.
* **`PressureGradient.contDiff_slice_pressure` NOT deduped (task 3).**  It is a
  byte-identical rename of `D01.contDiff_slice_scalar` (`DatumToJets.lean:377`).
  Deduping requires `PressureGradient` to `import NSFormalization.Section4.D01.DatumToJets`,
  which enlarges its **local-module** import closure from **51** (via
  `A02.SolutionClass`) to **1114** (measured by BFS over `import` lines;
  +1063 local modules — `D01.DatumToJets` transitively reaches the whole
  `A05`/`Paper3`/vendor-`Euler` stack).  Lane 083's reviewer measured **+548**
  `lake build` jobs for the same change.  Either way the cost is large, so the
  inline copy is **kept** and recorded on the MAINT list — matching the task's
  own steer ("+548 for that module, so likely keep and record").
* **`Lifespan`'s two `A02`-vocabulary restatements kept (task 3).**
  `memForceR_insertedForce` and `lt_maximalLifespanR_of_regularThrough` are
  deliberately **not imported** by `Bindings/InsertionLifespan.lean`, which takes
  the same two steps directly through the registered `Data`-vocabulary fields
  `datumLemmas.memForceR_of_compact_difference` and
  `maximalPartial.regularThrough_iff` (needing no `A02`↔`Data` bridge).  They are
  public theorems (byte-identical constraint forbids removal here) and are the
  S-level statements `research/R42/LIFESPAN_SPLIT.md` #3/#6 record as proved;
  kept, and noted on the MAINT list.
* **`SolutionOnShorter` copy of `contDiff_slice` — already gone.**  Confirmed
  (grep): the module uses `D01.contDiff_slice` directly (lines 120, 122); the copy
  the reviewers flagged was removed in review.  Nothing to do.

## Negative-check results (Part B item 2; edits done only in `/tmp/r42neg/`
scratch copies — the modules were never touched)

For the main theorem of each of the seven modules, one hypothesis was removed in a
scratch that imports the module and redeclares the theorem (renamed `_neg`) under
`set_option autoImplicit false in`, and the proof was confirmed to break.  The
control is the module itself, which builds (`lake build`, above).

| module | main theorem | hypothesis removed | break |
|---|---|---|---|
| `Assembly` | `inserted_equation_slab` | `hbg : ∀ t ∈ Ioo 0 T, ∀ x, residual ν (v+w) p t x = g` | `error: Unknown identifier 'hbg'` (`Assembly_neg.lean:48,20`) — the background residual feeding `exact_insertion` is gone |
| `Lifespan` | `limsup_eq_top_of_le_add_const` | `hC : C ≠ ⊤` | `error: Unknown identifier 'hC'` (`Lifespan_neg.lean:21,43`) — `ENNReal.add_ne_top.mpr ⟨_, hC⟩` cannot rule out `b + C = ⊤` |
| `CorrectionPath` | `exists_datumPath_of_localized` | `hhist : ∀ t, 0 ≤ t → t ≤ t₁ → ∀ x, d(t,x)=0` | `error: Unknown identifier 'hhist'` (`CorrectionPath_neg.lean:54,30`) — the `t ≤ t₁` history that makes `F` smooth across `t=0` is missing |
| `PressureGradient` | `memLp_pressureGradient_of_difference_support` | `h1 : MemLp (pressureGradient π t ·) 2 volume` | `error: Unknown identifier 'h1'` (`PressureGradient_neg.lean:19,54`) — the reference's own `∇π ∈ L²` addend is gone |
| `BlowupEssSup` | `limsupLeft_speedENorm_eq_top` | `hblow : SpeedUnboundedAt T u` | `error: Unknown identifier 'hblow'` (`BlowupEssSup_neg.lean:23,6`) — no pointwise blow-up to feed the frequently-characterisation |
| `SolutionOnShorter` | `classicalSolutionR_of_inserted` | `hmom : ∀ t ∈ Ioo 0 T, ∀ x, navierStokesResidual ν u p t x = gε` | `error: Unknown identifier 'hmom'` (`SolutionOnShorter_neg.lean:72,32`) — the `momentum` field cannot be built |
| `FullHorizon` | `classicalSolutionR_of_inserted_fullHorizon` | `hT : 0 < T` | `error: Unknown identifier 'hT'` (`FullHorizon_neg.lean:32,21`) — both `horizon_pos := hT` and `exists_datumPath_of_forall_shorter hT` fail |

All seven tested hypotheses are load-bearing.

## Conformance + split-obligation table (Part B item 1)

The R42 obligations are the fields of the two **registered** contracts, both
checked green by `make test` (`checkedInsertionFamily`, `checkedInsertionLifespan`,
"checked; standard logical axioms only"):

* `R42.insertion_family` — inhabited by `Bindings/InsertionFamily.lean`
  (`insertionFamily`), which imports `Section4/R42/Assembly.lean`.  Every
  `InsertionFamilyAPI` field is discharged there; `Assembly` supplies the
  reference-slab identities `inserted_equation_slab` (momentum, `04-whole-space.tex:50-51`)
  and `inserted_divergence_slab` (incompressibility, `04-whole-space.tex:37-38`)
  plus the three geometry lemmas `scaledSupport_subset_ball`,
  `exists_spatial_radius`, `parabolicForce_ball` (the `K→K_*` enlargement /
  ball-localization, `03-torus.tex:101-105`) and the rescaling smoothness
  `dilate_smoothOn_target`.
* `R42.insertion_lifespan` — inhabited by `Bindings/InsertionLifespan.lean`
  (`insertionLifespanAPI`), which imports `SolutionOnShorter`, `BlowupEssSup`,
  `FullHorizon`.

`research/R42/LIFESPAN_SPLIT.md` rows and sub-items, and where each is discharged:

| split item | discharged by | status |
|---|---|---|
| **1** `sol_on_shorter` | `SolutionOnShorter.classicalSolutionR_of_inserted` (full-horizon variant `FullHorizon.classicalSolutionR_of_inserted_fullHorizon`); consumed by `Bindings.InsertionLifespan.sol_on_shorter`/`sol_fullHorizon` | proved |
| **2** `blowup_essSup` | `BlowupEssSup.limsupLeft_speedENorm_eq_top`; consumed in `Bindings.InsertionLifespan.lifespan_upper` | proved |
| **3** `memForceR_gε` | `Lifespan.memForceR_insertedForce` (A02-vocab); Bindings takes it via `datumLemmas.memForceR_of_compact_difference` → `Bindings.InsertionLifespan.memForceR_force` | proved |
| **4** `upper` | `Bindings.InsertionLifespan.lifespan_upper` (registered `A02.lifespan_le_of_unbounded`) | proved |
| **5** `lower` | `Bindings.InsertionLifespan.lifespan_lower` (registered `A02.lifespan_ge_of_forall_shorter`) | proved |
| **6** `reference` | `Lifespan.lt_maximalLifespanR_of_regularThrough` (A02-vocab); Bindings takes it via `maximalPartial.regularThrough_iff` → `Bindings.InsertionLifespan.referenceLifespan` | proved (given the `RegularThrough` field) |
| **1a** `sobolev` clause | `CorrectionPath.sobolev_add_of_localized` ∘ `exists_datumPath_of_localized`, glued across `[0,T)` by `FullHorizon.exists_datumPath_of_forall_shorter` | proved |
| **1b** compact spatial support of `u_ε−v` | `Lifespan.hasCompactSupport_of_tsupport_subset_ball` | proved |
| **1c** datum at each order/time | `Lifespan.exists_isSobolevDatum_of_contDiff_hasCompactSupport` (via `D01.exists_isSobolevDatum_of_contDiff_memLp`) | proved |
| **1d** reference datum path `G_v` | the reference's own `ClassicalSolutionR.sobolev` (not an R42 lemma) | available |
| **1e-i** time-continuity of correction datum path | `CorrectionPath.exists_datumPath_of_localized` (`D01.contDiff_angularPath` after a time cutoff) | proved |
| **1e-ii** datum additivity | registered `D01.isSobolevDatum_add`/`isSobolevPath_add`, used by `CorrectionPath.sobolev_add_of_localized` | proved (registered D01) |
| **1f** `pressure_gradient` clause | `PressureGradient.memLp_pressureGradient_of_difference_support` (∘ `_of_compact`, `_add`) | proved |
| **2a** pointwise ⟹ essSup lower bound | `BlowupEssSup.ofReal_le_eLpNormTop_of_continuous` (+ `continuous_slice_of_velocity_smooth` for the `hcont` input) | proved |
| **4a** `a ∈ X_R` | `Bindings.InsertionLifespan.initialClassR_a` (derived from `reference` at `t=0`; not an R42 formalization-module lemma) | proved |

No missing conformance `example` was found, so none was added; every theorem the
ATTEMPTS files claim proved is either a registered-contract field (checked by
`make test`) or has a `#print axioms` in its `axioms_*.lean` file (all seven run
above, all `[propext, Classical.choice, Quot.sound]`).

## R42 exports still owed to R46/R47 (open, not regressions)

Recorded from `contracts.json` (`R42.insertion_lifespan`, "NOT asserted") and the
split's residuals:

1. **The `sobolev` / `pressure_gradient` export for `u_ε`.**  These `ClassicalSolutionR`
   fields are *built* inside `sol_on_shorter`/`classicalSolutionR_of_inserted` (and
   the whole object on `[0,T)` by `FullHorizon.classicalSolutionR_of_inserted_fullHorizon`,
   surfaced as `Bindings.InsertionLifespan.sol_fullHorizon`), but the registered
   contract asserts neither as a standalone field.  A later lane (R46/R47) that
   needs `∇p_ε ∈ L²` or the datum path as a *contract* obligation must register it.
2. **The displayed limsup of the spatial sup norm.**  The blow-up is registered
   only in the pointwise `SpeedUnboundedAt` form; the essential-supremum form
   `MaximalPartial.limsupLeft T (speedENorm ∘ slice) = ⊤` is **proved**
   (`BlowupEssSup.limsupLeft_speedENorm_eq_top`) and consumed inside
   `lifespan_upper`, but is not exported as a contract field.

## MAINT list (recorded, not done in this SIMP lane)

* **`PressureGradient.contDiff_slice_pressure` → `D01.contDiff_slice_scalar`
  (`DatumToJets.lean:377`).**  Byte-identical rename; consolidation blocked by the
  large import-closure cost (+1063 local modules / lane-083's +548 build jobs, see
  above).  Fold onto the canonical `D01` lemma only when `PressureGradient` (or a
  successor) already sits in a closure that includes `D01.DatumToJets`.  Not
  `rfl`-transparent to change here (needs a new import + closure).
* **`Lifespan.{memForceR_insertedForce, lt_maximalLifespanR_of_regularThrough}`.**
  A02/Data-vocabulary restatements bypassed by `Bindings/InsertionLifespan.lean`.
  Keep (public + byte-identical constraint; the S-level statements of
  `LIFESPAN_SPLIT.md` #3/#6).  If an R42-V2 that carries the `memF` / `RegularThrough`
  hypotheses is introduced, it can consume these directly and fold `Lifespan.lean`
  into a registered Tests closure.

## CI closure (Part B item 3)

* **In a registered-contract Tests closure** (`make test` compiles them via the two
  Bindings and their `Tests.*`): **6 of 7** —
  - `Assembly` via `Bindings.InsertionFamily` → `Tests.InsertionFamily`
    (contract `R42.insertion_family`);
  - `SolutionOnShorter`, `BlowupEssSup`, `FullHorizon` directly imported by
    `Bindings.InsertionLifespan`, and `CorrectionPath`, `PressureGradient`
    transitively (through `SolutionOnShorter`) → `Tests.InsertionLifespan`
    (contract `R42.insertion_lifespan`).
* **Not in any registered-contract Tests closure:** **`Lifespan`** (1 of 7).
  Nothing in `verification/{Bindings,Tests,Contracts}` imports it (grep confirmed);
  `Bindings/InsertionLifespan.lean` deliberately bypasses its two A02-vocab lemmas.
  It is covered by (a) its conformance file `research/R42/axioms_lifespan.lean` (run
  manually, above; all eight decls standard-3-axioms) and (b) CI's changed-module
  step `experiments/build_changed_lean.py`, which `lake build`s every changed
  `formalization/` module.  *For the next contract bundle:* fold `Lifespan` into a
  registered closure when an R42-V2 consumes its restatements (MAINT).

## Commands run (all `lake` from `WT/verification`, one process at a time)

| command | result |
|---|---|
| `lake build` of the seven modules + `Bindings.InsertionLifespan` (baseline, then after edits) | `Build completed successfully (9974 jobs)`; warnings only in dependency modules (`Paper3.*`, `Source.*`), none on any R42 own line |
| `lake env lean` on each of the seven (before + after) | each silent, exit 0 (zero own-line diagnostics) |
| per-token `open` removability probe (35 `lake env lean` runs) + combined-removal re-check | guided the removals; combined per-module state re-verified silent |
| `lake env lean ../research/R42/axioms_{lifespan,correction,pressure,blowup,sol_shorter,full_horizon,binding}.lean` | all exit 0; every decl `[propext, Classical.choice, Quot.sound]` |
| 7 negative checks (`/tmp/r42neg/*_neg.lean`, `autoImplicit false`) | all break as tabled (controls = the built modules) |
| `git diff` (signatures) | every changed line is an `open`/`open scoped` line; no signature or proof line changed |
| `make check` | exit 0 (architecture; contract-policy 13 tests; work-queue 30 items consistent) |
| `make test` | **18/18** contracts "checked; standard logical axioms only" (incl. `checkedInsertionFamily`, `checkedInsertionLifespan`, which rebuild the edited modules) |
