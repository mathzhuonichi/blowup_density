# Lane 359-T13-localization-assembly — T13 `localization` (`eq:localization`) assembled from the six proved pieces, then the full `LocalizationAPI` term

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/359-T13-localization-assembly` (git branch `erenup/359-T13-localization-assembly`, based on lane 354's branch merged with
`origin/erenup/integration-section3`: canonical modules `Section3/T13/{Localization,ConstantEndpoints,TorusIdentity,WholeSpaceIdentity,LocalizationKernel,KernelComparison}.lean`
and `Section3/T15/ParsevalZero.lean` (#331: `periodicSobolevENorm_zero_eq`, `periodicSobolevENorm_zero_eq_of_memLp`)). Read `CLAUDE.md`, **`research/T13/REPORT_354.md` §3 and the
consumer `example` in `research/T13/probes/kernel_comparison_closes.lean`** (the assembly sketch, type-checked with a `wholeSpace_identity`-shaped hypothesis that is now a theorem),
`research/T13/REPORT_{344,345,348,353}.md`, `research/T13/COMPARISON.md` (item 8: the physical/coefficient-side `L²` bridge), `research/T13/probes/api_on_canonical.lean` (the target
record `LocalizationAPI` with all six fields verbatim), `paper/sections/03-torus.tex:22-98`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; the
`mul_le_mul_*` renames and the `tsum_subtype` defeq note from lane 354).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** Honest partial with the exact residual statement and error text beats a stub.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T13`, `Section3/T15/ParsevalZero.lean`, `Section3/T10`, `Section3/T12`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal
1. `theorem localization` — verbatim the field of `research/T13/probes/api_on_canonical.lean`:
   `∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ), 0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube → ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) → periodicSobolevENorm s (periodize f) ≤ ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)`.
   Route (the paper's, all pieces proved): `periodicSobolevENorm s (periodize f) ≤ periodicSobolevENorm 0 (periodize f) + periodicHomogeneousENorm s (meanZeroPartT (periodize f))`
   (353, needs `periodize f` smooth periodic: T13 `contDiff_periodize`/vendor + `unitSpatialPeriodsOn_periodize`; check the exact hypotheses); the `L²` term:
   `periodicSobolevENorm 0 (periodize f) = eLpNorm (torusLift (periodize f)) 2 periodicTorusMeasure` (ParsevalZero) `= eLpNorm f 2 volume` (`endpoint_zero`, 344 — match its exact
   spelling; if it is stated with `volume.restrict fundamentalCube` or a `lintegral`, bridge it — this is COMPARISON item 8, do it here); the homogeneous term:
   `periodicHomogeneousENorm s (meanZeroPartT (periodize f)) ^ 2 = ITorus s (periodize f) / cFrac s` (`torus_identity`, 345; `cFrac s > 0`, `< ⊤` from `constant_pos_finite`, 344),
   `ITorus s (periodize f) ≤ IReal s f + 4·tailGeomConst s c r·(eLpNorm f 2 volume)²` (354), `IReal s f = cFrac s · dotHomogeneousENorm s f ^ 2` (348); so
   `periodicHomogeneousENorm … ≤ sqrt(dotHomogeneousENorm s f ^ 2 + (4 tailGeomConst / cFrac s)·‖f‖₂²) ≤ dotHomogeneousENorm s f + sqrt(4 tailGeomConst / cFrac s)·‖f‖₂` (`ENNReal` `sqrt`
   subadditivity: `ENNReal.rpow_add_le_add_rpow`-type or `Real.sqrt_add_le`-type after `toReal` with finiteness from `tailGeomConst_lt_top`, `constant_pos_finite`, `homogeneousFourierENorm_lt_top`);
   collect `C := max 1 (sqrt (4·tailGeomConst/cFrac)).toReal + 1` (any explicit positive constant; document it). Handle the `ENNReal.ofReal`/`toReal` bookkeeping honestly (all quantities are `< ⊤`).
2. `theorem localizationAPI : LocalizationAPI` — the six-field record of `research/T13/probes/api_on_canonical.lean` (restate the structure in the canonical module if it lives only in the
   probe: put `structure LocalizationAPI : Prop` **token-for-token** into `Section3/T13/Assembly.lean`, then `theorem localizationAPI : LocalizationAPI := ⟨constant_pos_finite, wholeSpace_identity, torus_identity, localization, endpoint_zero, endpoint_one⟩`),
   and update the probe so that `api_on_canonical.lean` closes the Spec's `LocalizationAPI` from `localizationAPI` (its restatement must be a copy of `research/T13/Spec.lean`'s structure;
   check what the probe currently does with the six fields and make the whole record close by `exact`).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/Assembly.lean` (namespace `NSFormalization.Section3.T13`) with `localization`, `LocalizationAPI`, `localizationAPI`, and the
   `L²` bridge lemma(s).
2. Probe: update `research/T13/probes/api_on_canonical.lean` (or a new `research/T13/probes/assembly_closes.lean` if the existing probe's structure must stay untouched) so that the Spec's
   `LocalizationAPI` is closed from `localizationAPI`; non-vacuity instance (the lane-344 `ContDiffBump` field at `s = 1/2`).
3. Records: `research/T13/ATTEMPTS_ASSEMBLY.md`, `research/T13/axioms_assembly.lean`, status in `research/T13/COMPARISON.md` ("all six fields closed"), report `research/T13/REPORT_359.md`
   (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.Assembly` (0 errors), `lake env lean` on the module, probe(s) and axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the constant / files / gaps with exact error text / commands and results).
