# Lane 358-T16-assembly — T16 `lem:potential`: assemble `localPotential : localPotentialStatement` from lanes 347 (cutoffs, threshold, canonical API), 351 (ball potential) and 352 (lattice lift)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/358-T16-assembly` (git branch `erenup/358-T16-assembly`, based on lane 351's branch merged with
lane 352's branch and `origin/erenup/integration-section3`; it contains `formalization/NSFormalization/Section3/T16/{LocalPotential,BallPotential,LatticeLift}.lean`).
Read `CLAUDE.md` (hard rules), **`research/T16/REPORT_347.md`, `REPORT_351.md`, `REPORT_352.md`, `ATTEMPTS.md`, `ATTEMPTS_BALL_POTENTIAL.md`, `ATTEMPTS_LATTICE_LIFT.md`,
`SPEC_ISSUES.md`, `COMPARISON.md`** and the three probes `research/T16/probes/{api_on_canonical,ball_potential_closes,lattice_lift_closes}.lean` (they show exactly how each
field of the canonical `LocalPotentialAPI` is discharged), `research/T16/Spec.lean:320-338` (the statement), `paper/sections/03-torus.tex:176-217`, the chart-level facts in
`formalization/NSFormalization/Paper1/LocalCutoff.lean` (`localCorrection_*`, `exists_local_background_removal`) and `Section4/I02/Reference.lean` (`physicalCorrection`, its
congruence lemmas), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** If one chart-level hypothesis of `correction_fields_of_chart` cannot be discharged for the concrete correction,
  deliver the assembly with every other field closed and state that one residual as a concrete lemma with the exact error text (honest partial); a `def X : Prop := <goal>` or a
  hypothesis equal to the target will be discarded without review.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
`theorem localPotential : localPotentialStatement` (the canonical module's statement, `Section3/T16/LocalPotential.lean`; the Spec's statement then follows through the probe's
`specStatement_of_module`). Construction, following the paper and the three reports: given `v U K x₀ r T δ` with the statement's hypotheses, take `θ, O, θRadius` from
`exists_originCutoff hK`, `η` from `exists_timeCutoff`, `ε₀` from `exists_threshold`, `A := timePotential v x₀` with the three potential fields from `exists_potential_on_ball`
(351), and `correction ε := latticeLift (W ε)` where `W ε` is the chart correction `−∇×(η_ε θ_ε A)` in the exact spelling `correction_formula` expects (check whether the field
is stated through `physicalCorrection v x₀ T θ η ε` of I02 or through an explicit curl; use the same object), so that `correction_fields_of_chart` (352) yields the seven
`correction_*` fields once its chart hypotheses are discharged: smoothness of `W ε` (the product of the smooth scaled cutoffs with `A`, which is smooth on the ball cylinder where
`θ_ε ≠ 0` — use `ε·θRadius < r` from `eps_space` and the time window from `eps_time`), compact support, divergence-freeness (curl of a smooth compactly supported field:
`localCorrection_divergence`), the product support bound, the curl formula, the ball cancellation (`localCorrection_eq_neg` on the plateau where `θ_ε = 1`, `η_ε = 1`, using
`theta_one`/`eta_one`), and the T14 packet-support bound (the statement's hypothesis on `U`). Package as `def localPotentialData … : CutoffData` and
`theorem localPotentialAPI … : LocalPotentialAPI v U K x₀ r T δ (localPotentialData …)`, then `localPotential`.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T16/Assembly.lean` (namespace `NSFormalization.Section3.T16`) with the above.
2. Probe `research/T16/probes/assembly_closes.lean`: `example : localPotentialStatement := localPotential` for the canonical statement **and** for the Spec's copy (via
   `specStatement_of_module`), plus the non-vacuity instance of `api_on_canonical.lean` re-run through the general theorem (`v ≠ 0`, e.g. a constant divergence-free field).
3. Records: `research/T16/ATTEMPTS_ASSEMBLY.md`, conformance `research/T16/axioms_assembly.lean`, status in `research/T16/COMPARISON.md` ("all 26 fields closed" or the exact
   residual), report `research/T16/REPORT_358.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.Assembly` (0 errors), `lake env lean` on the module, probe and axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results). Also write it to `research/T16/REPORT_358.md`
(if a guard blocks the write, put the full report in your final message).
