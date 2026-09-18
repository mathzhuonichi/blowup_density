# Lane 365-T12-U2-cutoff — T12 U2: the smooth cutoff `χ` (= 1 on the fundamental cube, supported inside a slightly larger cube) with bounded derivatives

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/365-T12-U2-cutoff` (git branch `erenup/365-T12-U2-cutoff`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T12/T12_SPLIT.md` §0 and unit U2 (and U3/U5 to see how `χ` is consumed)**, `Section3/T13/Localization.lean` (`fundamentalCube`),
`Section3/T13/ConstantEndpoints.lean` (`interior_fundamentalCube`, `isClosed_fundamentalCube`, …), `Section3/T16/LocalPotential.lean` (`exists_originCutoff` — a Urysohn cutoff
constructed by lane 347; reuse its technique), Mathlib's `ContDiffBump` / `exists_smooth_tsupport_subset` / `ContDiffBumpBase`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T10`, `Section3/T12`, `Section3/T13`. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T12/Cutoff.lean` (namespace `NSFormalization.Section3.T12`): `def largerCube : Set Space` (e.g. `(−1/4, 5/4)³`, or the
`δ`-enlargement of the cube; document the choice), `def cutoff : Space → ℝ` with theorems `cutoff_contDiff : ContDiff ℝ ∞ cutoff`, `cutoff_eq_one : ∀ x ∈ fundamentalCube, cutoff x = 1`
(better: `EqOn cutoff 1 (closure fundamentalCube)` or on an open neighbourhood of the closed cube — U3 needs `χ = 1` on a neighbourhood of `Q`), `cutoff_range : ∀ x, cutoff x ∈ Icc 0 1`,
`tsupport_cutoff : tsupport cutoff ⊆ interior largerCube`, `hasCompactSupport_cutoff`, and the derivative bounds: `∃ M₁, ∀ x, ‖fderiv ℝ cutoff x‖ ≤ M₁` and `∃ M₂, ∀ x, ‖iteratedFDeriv ℝ 2 cutoff x‖ ≤ M₂`
(continuous compactly supported ⇒ bounded), plus `fderiv cutoff` and `iteratedFDeriv ℝ 2 cutoff` vanish on `fundamentalCube` (where `χ ≡ 1` on a neighbourhood). Then the product
lemmas for a periodic field `v : SpatialField`: `def cutoffMul (v) : SpatialField := fun x => cutoff x • v x`, `contDiff_cutoffMul (hv : ContDiff ℝ ∞ v)`, `hasCompactSupport_cutoffMul`,
`cutoffMul_eq_on_cube`, and `memHInfty_cutoffMul` if `MemHInfty` (Section 4's `Section4/A05`/`D01` spelling used by the registered `A05.velocityCriticalL3` hypothesis — grep
`Bindings/GradientL6V2.lean:44` and `Section4/A05/CriticalL3.lean` for the exact hypothesis name) follows from smooth + compact support (it should: `Section4/D01/DatumToJets.lean`
`exists_smoothL2Field_of_memHInfty` and its converse for `C_c^∞`; grep `memHInfty_of` in `Section4/`).

## Deliverables
1. `Section3/T12/Cutoff.lean`; 2. probe `research/T12/probes/cutoff_closes.lean` (instantiate `cutoffMul` on the two-mode field of `research/T12/probes/tame_product_closes.lean` and check
`cutoffMul v = v` on the cube by `rfl`/`simp`); 3. `research/T12/ATTEMPTS_CUTOFF.md`, `research/T12/axioms_cutoff.lean`, status in `research/T12/T12_SPLIT.md` U2, report `research/T12/REPORT_365.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.Cutoff` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T12/REPORT_365.md`.
