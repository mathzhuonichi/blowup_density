# C01 simplifier + tester pass (lane 077, SIMP-C01)

Follow-up lane over the four merged C01 modules
`Section4/C01/{ForceSlices,Trilinear,VelocityJets,Evolution}.lean`, per the
"After ACCEPT" section of `.claude/skills/lane-review/SKILL.md`, imitating
`research/A02/ATTEMPTS_SIMP.md` (lane 040).  **No new mathematics**; every public
statement is byte-identical to the merged version (verified by a full `git diff`:
every `+`/`-` line is an `open`, a docstring, or a comment — no `theorem`/`lemma`/
`def` signature line and no proof-body line changed).  All 14 audited theorems
still print `[propext, Classical.choice, Quot.sound]`; all conformance `example`s
in `research/C01/axioms_{u1u3,u2,u6}.lean` still elaborate.

Worktree `.claude/worktrees/077-SIMP-C01`, base `erenup/integration`.

## Line counts (before → after)

| module | before | after | note |
|---|---|---|---|
| `ForceSlices.lean` | 178 | 180 | −2 unused scoped opens; +docstring paper-line |
| `Trilinear.lean` | 283 | 286 | −1 unused scoped open; +3 docstring paper-lines |
| `VelocityJets.lean` | 90 | 91 | −3 unused opens (1 whole line); +docstring paper-lines |
| `Evolution.lean` | 178 | 179 | −1 unused open line; +1 missing docstring |
| **total** | **729** | **736** | +7 |

Net lines rose because the substantive change was adding paper-location
docstrings (task 2), while the removals were unused `open`s (a few tokens / two
lines).  There was **no proof body to shorten** (see "not simplified" below), so
this pass does not reduce line count the way lane 040's dedupe did; its value is
in the dead-`open` removal, the docstrings, and the tester half.

## Simplified

* **Unused `open`s dropped (task 1).**  8 unused `open` targets removed across the
  four modules, each verified by re-elaboration (`lake env lean <file>` stays
  silent, exit 0) after removal:
  - `ForceSlices`: `open scoped ContDiff ENNReal SchwartzMap` → `open scoped ContDiff`
    (no `ℝ≥0∞` literal and no `𝓢`/`SchwartzMap` token occurs in code; `ContDiff`
    is kept because `ContDiff ℝ ∞` / `ContDiffOn ℝ ∞` do occur, e.g. lines 113,136,137).
  - `Trilinear`: `open scoped ContDiff ENNReal` → `open scoped ENNReal`
    (no `∞` token in code; `ℝ≥0∞` occurs at lines 75,160 so `ENNReal` is kept).
  - `VelocityJets`: `open Set MeasureTheory` → `open Set` and the whole
    `open scoped ContDiff ENNReal` line removed (no `MeasureTheory` identifier,
    no `∞`, no `ℝ≥0∞` in code; `Set` kept for `Ico`).
  - `Evolution`: the whole `open scoped ContDiff ENNReal` line removed (no `∞`,
    no `ℝ≥0∞` in code; `∞` appears only in a header comment).
* **Docstrings naming the paper location (task 2), copied not invented.**
  - `forceTimeRegularity`: added `paper/sections/02-preliminaries.tex:17-19`
    eq:Rclasses, slicewise form of `04-whole-space.tex:119` eq:RL2 (copied from the
    `Spec.lean` Bridge 2 docstring).
  - `trilinearHolder`: `paper/sections/04-whole-space.tex:108` (module header /
    `Spec.lean` docstring).
  - `trilinearAbsorbed`: `paper/sections/04-whole-space.tex:109-112`.
  - `laplacianSqENorm`: `paper/sections/04-whole-space.tex:109,115` (the `laplacianSq`
    def's paper line).
  - `velocity_slice_memHInfty_and_smoothL2`: `paper/sections/02-preliminaries.tex:12`
    eq:Rinitial, the `H^∞` regularity of the class (module-header line).
  - `Evolution.velocityField_field`: added the one **missing** docstring (it had
    none); it is a `@[simp]` `rfl` normal form, no paper location, so none invented.
* **No `set_option`/`maxHeartbeats` existed in any module** (task 1) — kept that
  way.

## Not simplified, and why

* **No proof body was shortened.**  The four modules were already reviewed
  (`REVIEW_U1U3.md`, `REVIEW_U2.md`, `REVIEW_U6.md`) and build **warning-free**:
  `lake env lean` on each is silent, which means the default `unusedVariables`
  linter (it does fire elsewhere in the tree, e.g. `PhysicalBesselSobolev`) finds
  **no dead `have`s or unused binders** in any C01 module.  Every step in the long
  `Trilinear` proofs (`advection_norm_le`, `lintegral_advection_inner_laplacian_le`,
  the three-factor Hölder reassembly) is load-bearing.  Attempting to collapse a
  multi-step block into `simp`/`positivity`/`gcongr` would risk changing the
  transitive axioms or breaking a byte-identical statement for no verified gain, so
  none was attempted.
* **No duplicated restatement to dedupe against a canonical module (task 3).**  The
  `§0` `def`s (`slice`, `l2Sq`, `l2Norm` in `ForceSlices`; `lift`, `laplacianSq`,
  `criticalL3`, `advectionWork` in `Trilinear`) restate objects of
  `research/C01/Spec.lean`, which is a **draft spec in `research/`, not a canonical
  importable module** (`SolutionClass`/`D01`/`A03` do not define them).  `Trilinear`'s
  `§0` is deliberately written against the A05 objects (`lap`, `gradTensor`) the
  registered contract binds to, and the conformance file `axioms_u6.lean` restates
  the same `def`s in the contract's own vocabulary; the two restatements are the
  point of the fidelity check, not duplication to remove.  So there is nothing to
  replace with an import here.

## Negative-check results (task 6; edits done only in `/tmp` scratch copies —
the modules were never touched)

Each scratch is a whole-module copy under `/tmp/c01neg/` with exactly one
hypothesis of the module's main theorem removed, then `lake env lean`'d.

* **`ForceSlices.forceTimeRegularity`, hypothesis `MemForceR f` removed.**
  `/tmp/c01neg/ForceSlices_neg.lean:162:10: error: Tactic `introN` failed: There
  are no additional binders or `let` bindings in the goal to introduce`
  → `MemForceR f` is load-bearing: without it `intro f hf` has no `hf` to bind and
  there is no datum path to slice.
* **`Trilinear.trilinearHolder`, hypothesis `hz : SmoothL2 z` removed.**
  `/tmp/c01neg/Trilinear_neg.lean:249:49: error: Unknown identifier `hz`` (the call
  `lintegral_advection_inner_laplacian_le z hz`).
  → smoothness is load-bearing: it is what supplies measurability of `z`, `∇z`, `Δz`
  to the `ℝ≥0∞` Hölder bound.
* **`VelocityJets.velocity_slice_memHInfty_and_smoothL2`, hypothesis
  `ht : t ∈ Ico 0 T` removed.**
  `/tmp/c01neg/VelocityJets_neg.lean:72:50: error: Unknown identifier `ht``.
  → `ht` is load-bearing: `D01.smoothSquareIntegrableJets_slice` needs the time inside
  the lifespan.
* **`Evolution` — methodology finding, then clean check.**  First attempt removed
  `hST : S < T` from `velocityField_jetLp_continuous`; the scratch **compiled clean
  (exit 0)**.  Reason: `hST` also occurs in the *statement type*
  (`velocityField u hST t`), and **`autoImplicit` is on in this package**, so it
  silently re-bound the hypothesis as an implicit `{hST : S < T}` — confirmed by
  `#check`, whose signature came back
  `∀ {ν a f S T} {hST : S < T} (u) (n), Continuous …`.  So a negative check must
  target a hypothesis used *only in the proof body*, not one appearing in the type.
  The clean check is on **`Evolution.mem_Ico_of_mem_Icc`** (its `hST` is used only in
  the proof `⟨ht.1, lt_of_le_of_lt ht.2 hST⟩`, not the type): removing `hST` gives
  `/tmp/c01neg/Evolution_neg2.lean:110:29: error: Unknown identifier `hST``.
  → `S < T` is load-bearing: it is exactly what places the compact slab `[0,S]` inside
  the open lifespan `[0,T)`, the containment every `Evolution` theorem routes through.

## Conformance (task 5; every claimed spec field has an `example` discharged
verbatim, no extra hypotheses)

| spec field (`research/C01/Spec.lean`) | conformance `example` | discharging theorem |
|---|---|---|
| `velocityJets` (`:295-300`) | `axioms_u1u3.lean:65-72` | `velocity_slice_memHInfty_and_smoothL2` |
| `forceTimeRegularity` (`:326-329`) | `axioms_u2.lean:37-41` | `forceTimeRegularity` |
| `trilinearHolder` (`:410`) | `axioms_u6.lean:47-50` | `trilinearHolder` |
| `trilinearAbsorbed` (`:435`) | `axioms_u6.lean:53-57` | `trilinearAbsorbed` |
| `laplacianSqENorm` (`:471`) | `axioms_u6.lean:60-62` | `laplacianSqENorm` |
| (review finding 1, not a spec field) certified lintegral bound | `axioms_u6.lean:65-68` | `lintegral_advection_inner_laplacian_le` |
| (review finding 1) certified integrability | `axioms_u6.lean:72-74` | `integrable_advection_inner_laplacian` |

All discharged with the theorem applied to exactly the field's own hypotheses (no
weakening).  **U3 (`Evolution`) has no spec field**: it is infrastructure feeding
U4/U7 (`COMPARISON.md:173`), so the Spec has no `EnergyAbsorptionAPI` clause for it;
its five theorems are audited by `#print axioms` (`axioms_u1u3.lean:81-85`) but need
no conformance `example`, so none is missing.

## CI closure (task 7)

`experiments/build_changed_lean.py` maps every changed `.lean` under
`verification/` / `formalization/` / `vendor/NavierStokesAndEuler/` to a module and
runs `lake build` on it.  The four C01 modules live under `formalization/`, so CI's
changed-module step rebuilds them whenever this lane changes them.  **No
`verification/{Bindings,Tests,Contracts}` module imports `NSFormalization.Section4.C01`**
(`grep` confirmed), so the four are **not** in a registered-contract Tests closure —
same status as A02.  *For the next contract bundle:* fold the four C01 modules into
the Tests closure when the C01 (`EnergyAbsorptionAPI`) contract is registered.

## Commands run (all `lake` from `WT/verification`, one at a time)

| command | result |
|---|---|
| `lake build …C01.{ForceSlices,Trilinear,VelocityJets,Evolution}` | `Build completed successfully (9898 jobs)`; the only warnings are from dependency modules (`Source.*`, `Paper3.*`), none on C01 lines |
| `lake env lean` on each of the four modules | each silent, exit 0 (zero own-line warnings), before and after the edits |
| `lake env lean ../research/C01/axioms_u1u3.lean` | 8 theorems, all `[propext, Classical.choice, Quot.sound]`, conformance example accepted |
| `lake env lean ../research/C01/axioms_u2.lean` | `forceTimeRegularity` `[propext, Classical.choice, Quot.sound]`, conformance accepted |
| `lake env lean ../research/C01/axioms_u6.lean` | 5 theorems, all `[propext, Classical.choice, Quot.sound]`, 5 conformance examples accepted |
| `git diff` (signatures) | every changed line is an `open`/docstring/comment; no signature or proof line changed |
| negative checks (4 `/tmp` scratches) | all break as recorded above (Evolution via `mem_Ico_of_mem_Icc` after the autoImplicit finding) |
| `make check` | exit 0 (plan / contract-policy 13 tests / work-queue 30 items all consistent) |
