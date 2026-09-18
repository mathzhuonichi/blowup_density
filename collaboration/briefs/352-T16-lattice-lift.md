# Lane 352-T16-lattice-lift — T16 gap 2: the unit-periodic lift of a compactly supported chart correction (the eight `correction_*` fields of `LocalPotentialAPI` as lemmas about the lattice sum)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/352-T16-lattice-lift` (git branch `erenup/352-T16-lattice-lift`, based on lane 347's branch:
it contains `formalization/NSFormalization/Section3/T16/LocalPotential.lean` (canonical T16 module: `latticeVector`, `periodicSet`,
`CutoffData`, `LocalPotentialAPI` with the eight `correction_*` fields, `localPotential_zero`) and `research/T16/{ATTEMPTS.md,SPEC_ISSUES.md,
REPORT_347.md,COMPARISON.md}`). Read `CLAUDE.md` (hard rules), **`research/T16/ATTEMPTS.md` §"Gap 2"** (the lift and its seven open
sub-lemmas — this lane is exactly that gap), `research/T16/Spec.lean` fields `correction_formula … correction_cancels` (`:447-500`) with their
paper lines (`03-torus.tex:181-192,212-215`), the chart-level facts already in the tree (`NSFormalization.Paper1.localCorrection_divergence`,
`localCorrection_eq_neg`, I02 `Reference.lean` `physicalCorrection_congr_slice`, `localCorrection_congr_slice`; grep `physicalCorrection`,
`localCorrection` in `Paper1/`, `Section4/I02/`), the T10 physical bridge (`Section3/T10/PhysicalBridge.lean`: `IsPeriodicOn`, lattice shift
lemmas), T13's `Localization.lean` (`periodize`, `summable_translate`, `periodize_locally_eq_sum`, `contDiff_periodize`,
`periodize_add_lattice`, `unitSpatialPeriodsOn_periodize` — a **spatial-only** periodization of a compactly supported field already exists
there for `SpaceTime → V`; reuse or adapt it rather than re-proving local finiteness), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). Honest partial with exact residual statements and error
  text beats a stub.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T13/Localization.lean`, `Section3/T10/*.lean`, `Section4/I02/*.lean`,
  `Paper1/`. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
Define the lift `latticeLift (w : SpaceTimeField) : SpaceTimeField := fun z => ∑' k : PeriodicFrequency, w (z.1, z.2 − latticeVector k)`
(or reuse T13's `periodize` if it is definitionally this — check and say) and prove, for a chart correction `w` that is smooth on `ℝ × ℝ³`
with `tsupport (fun x => w (t,x)) ⊆ ball x₀ ρ` for every `t`, `0 < ρ`, `ρ < 1/2` (the situation of `physicalCorrection v x₀ T θ η ε` with
`ρ = ε·θRadius < r < 1/2`, cf. `eps_space`), the eight `correction_*` fields of `LocalPotentialAPI` **in their exact canonical spellings**
(`Section3/T16/LocalPotential.lean`) as lemmas about `latticeLift w`:
`correction_formula` (on `ball x₀ r`, `r < 1/2`, the lift equals the `k = 0` term: `tsum_eq_single 0` from disjointness of the translated
balls — `ρ < 1/2` makes `ball (x₀ + n) ρ`, `n ∈ ℤ³`, pairwise disjoint), `correction_smooth` (`ContDiff ℝ ∞` of a locally finite sum:
T13 `contDiff_periodize`-style), `correction_periodic` (`IsPeriodicOn univ`: `k ↦ k + n` reindexing, `Equiv.tsum_eq`), `correction_divergence_free`
(divergence of the lift is the lift of the divergence, zero by `localCorrection_divergence`), `correction_support` / `correction_support_ball`
(support of the lift ⊆ `periodicSet (ball x₀ ρ)` ⊆ `periodicSet (ball x₀ r)`; time support inherited), and `correction_cancels`
(`eq:bgzero`: on the cancellation region the lift equals its `k = 0` term which equals `−v` by `localCorrection_eq_neg` — state this one
exactly as the field does over `periodicScaledPacket`/`correctedBackground`; if it needs the plateau facts `theta_one`/`eta_one`, take them as
the explicit hypotheses the field itself carries via `D`, not as new assumptions). Package the result as
`theorem correction_fields_of_chart … : <conjunction of the eight fields, or a structure with those eight fields>` so lane 353 (assembly) can
fill `LocalPotentialAPI` by projection.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T16/LatticeLift.lean` (namespace `NSFormalization.Section3.T16`).
2. Probe `research/T16/probes/lattice_lift_closes.lean`: `example`s matching each of the eight field types verbatim (copy them from the
   canonical structure) from your lemmas, plus a non-vacuity instance (a nonzero smooth bump `w` supported in a small ball, whose lift is
   nonzero and periodic).
3. Records: `research/T16/ATTEMPTS_LATTICE_LIFT.md`, conformance `research/T16/axioms_lattice_lift.lean`, status line in
   `research/T16/COMPARISON.md`, report `research/T16/REPORT_352.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.LatticeLift` (0 errors), `lake env lean` on the module,
probe and axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
Also write it to `research/T16/REPORT_352.md`.
