# Lane 447-T15-U10-pressure — T15 U10: pressure normalisation (`pressureSlice_integrable` + the mean-zero gauge of `normalizedScaledPressure`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/447-T15-U10-pressure` (git branch `erenup/447-T15-U10-pressure`, based on `origin/erenup/integration-section3`: `Section3/T15/{Bridges,ParsevalZero,HaarBridge,Scaling,Placement,SingleCopy}.lean`,
`Section3/T13/TorusIdentity.lean:419 lintegral_fundamentalCube_ofReal` and the Haar-on-torus = Lebesgue-on-cube facts, the T11 pressure gauge `PressureGaugeT`/`normalizePressureT`/`pressureMeanT`
(grep `Section3/T11` and `T10`), lane 433's hypothesis-free `pressureGradient_normalizePressureT` (on lane 433's branch, `Section3/T18/Momentum.lean` — reprove locally if you need it)). Read `CLAUDE.md`,
**`research/T15/T15_SPLIT.md` §0 and unit U10** (`:140-145`), the canonical field `pressureSlice_integrable` (`Section3/T15/Scaling.lean:314-319`) and the pressure gauge obligation of `solution`
(the `ClassicalSolutionT` field that says the pressure has mean zero / satisfies `PressureGaugeT` — read the T11 structure), `research/T15/REPORT_{376,421}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T15/Pressure.lean` (namespace `NSFormalization.Section3.T15`): `theorem pressureSlice_integrable` with type literally the `ScalingAPI` field
(`∀ ε ∈ Ioc 0 place.ε₀, ∀ t ∈ Ico 0 place.T, Integrable (torusLift (fun x ↦ periodizedScaledPressure p place.x₀ place.T ε (t, x))) periodicTorusMeasure`) under the raw packet clauses actually needed
(smoothness of `zeroPastField p` on the slab), and `theorem pressure_gauge` — the mean-zero/`PressureGaugeT` property of `normalizedScaledPressure p place.x₀ place.T ε` at every `t ∈ Ico 0 place.T`, in the
exact form the T11 `ClassicalSolutionT` structure requires (so U11 can plug it in). Route: U3's single copy collapses each slice to a smooth compactly supported function on the cube ⇒ continuous on the
compact torus ⇒ integrable (probability measure); `normalizedScaledPressure = normalizePressureT (periodizedScaledPressure …)` (`rfl`, U1/384) subtracts the Haar mean, so the mean of the normalised slice
is `0` (`integral_sub`, `integral_const` on the probability measure). Deliverables: the module, `research/T15/probes/pressure_closes.lean` (field by `exact`; gauge instantiated at the concrete packet of
`placement_closes.lean`), `research/T15/axioms_u10.lean`, `research/T15/ATTEMPTS_U10.md`, U10 status line in `T15_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Pressure` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T15/REPORT_447.md`.
