# Lane 366-T12-U1-haar-cube — T12 U1: Haar ↔ cube ↔ whole-space `L^p` transfer for periodic fields and for fields supported inside the cube (scalar + vector)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/366-T12-U1-haar-cube` (git branch `erenup/366-T12-U1-haar-cube`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T12/T12_SPLIT.md` §0 and unit U1 (and U4/U5 for how it is consumed)**, `Section3/T13/TorusIdentity.lean` (`lintegral_fundamentalCube_ofReal :419`,
`fundamentalCube_ae_eq_halfOpenCube :402`, `torusLift_torusPoint :459`, `torusPoint_sub :456` — Haar on the torus = Lebesgue on the cube, proved there at `p = 2`),
`Section3/T13/ConstantEndpoints.lean` (`endpoint_zero_eq :364`, `interior_fundamentalCube`), `Section3/T10/PeriodicData.lean` (`torusLift`, `periodicTorusMeasure`, `periodicLpENorm`
— the T12 API's `L^p` spelling: check `periodicLpENorm p v` at `Section3/T12/MeanZeroCalculus.lean` and how it relates to `eLpNorm (torusLift v) p periodicTorusMeasure`), and the top 40 lines
of `logs/LESSONS.md`. Note: lane 364 (`Section3/T15/HaarBridge.lean`, in progress) proves the `p = 2` energy identity for `periodize f`; do not duplicate its names — this lane is the
general-`p` transfer for *periodic* `v` and for fields supported in the cube.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T10`, `Section3/T12`, `Section3/T13`. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T12/HaarCube.lean` (namespace `NSFormalization.Section3.T12`):
1. `eLpNorm_torusLift_eq_restrict (v : SpatialField) (hv : IsPeriodicSpatial v) (p : ℝ≥0∞) : eLpNorm (torusLift v) p periodicTorusMeasure = eLpNorm v p (volume.restrict fundamentalCube)`
   (+ the measurability hypothesis the proof needs, stated minimally; for smooth periodic `v` derive the unconditional corollary), and the same for the vector-valued
   `gradientTensor v : Space → WithLp 2 (Fin 3 → Space)` (or whatever carrier `periodicLpENorm p (gradientTensor v)` uses — match the T12 API's spelling exactly) and for scalar fields.
2. `eLpNorm_restrict_eq_of_support (w) (hw : tsupport w ⊆ interior fundamentalCube) (p) : eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume` (scalar, vector).
3. The bridge to the API's norm: `periodicLpENorm p v = eLpNorm (torusLift v) p periodicTorusMeasure` if `periodicLpENorm` is defined differently (or `rfl` if not — say which).
Route: generalize `TorusIdentity.lean`'s `p = 2` argument (`lintegral_fundamentalCube_ofReal` etc.) to `eLpNorm … p` via `eLpNorm_eq_lintegral_rpow_enorm` for `0 < p < ⊤` and the
`essSup` case for `p = ⊤` (`eLpNormEssSup`; the torus `essSup` equals the cube `essSup` by the same measure identity) — handle `p = 0` trivially.

## Deliverables
1. `Section3/T12/HaarCube.lean`; 2. probe `research/T12/probes/haar_cube_closes.lean` (instantiate at `p = 3`, `p = 6` on the two-mode field of `research/T12/probes/tame_product_closes.lean`);
3. `research/T12/ATTEMPTS_HAAR_CUBE.md`, `research/T12/axioms_haar_cube.lean`, status in `research/T12/T12_SPLIT.md` U1, report `research/T12/REPORT_366.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.HaarCube` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T12/REPORT_366.md`.
