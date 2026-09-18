# Lane 426-T18-U2-U4-force-class-kinematics-div — T18 U2 + U3 + U4: force-class memberships, regularity/initial/history/periodicity, incompressibility

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/426-T18-U2-U4-force-class-kinematics-div` (git branch `erenup/426-T18-U2-U4-force-class-kinematics-div`, based on lane 422's branch merged with
`origin/erenup/integration-section3`: `Section3/T18/Insertion.lean` (U1: `InsertionData` bundling the raw-field `PlacementData`, the canonical `ScalingAPI` record, the T11 reference data, the
canonical 45-field `CorrectionAPI` record; `velocity`/`pressure`/`force` of the inserted triple; `ε₀`, `eps_*`, `delta_pos`, `reference_force_mem`, `initial_mem`), plus the T15/T17/T11/T16
canonical modules). Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0 and units U2 (`:69-75`), U3 (`:77-86`), U4 (`:88-93`)**, the corresponding Spec fields `research/T18/Spec.lean:1741`
(`force_mem`), `:1746` (`forceDifference_mem`), `:1753` (`velocity_smooth`), `:1758` (`pressure_smooth`), `:1763` (`initial`), `:1767` (`incompressible`), `:1780` (`history`), `:1786`
(`velocity_periodic`), `:1858` (`velocityDifference_divFree`), `research/T18/REPORT_422.md` + `research/T18/probes/insertion_closes.lean` (how U1's canonical layer maps to the Spec fields),
the threaded records' field names: `ScalingAPI` (`Section3/T15/Scaling.lean`: `force_mem`, `solution` (periodized packet as a classical-solution-like record with `.divergence`, smoothness,
periodicity), …), `CorrectionAPI` (`Section3/T17/Correction.lean`: `force_smooth`, `force_periodic`, `force_support`, `correction_smooth`, `correction_periodic`, `correction_support`,
`correction_divergence_free`, …), the T11 reference hypotheses (`velocity_smooth`, `pressure_smooth`, `divergence`, periodicity), `forceClassT = MemForceT` (`Contracts/V1/TorusLocalTheory.lean`
and its canonical copy), the R42 analogue `Section4/R42/*` (`memForceR_insertedForce`, `forceDifference_compact`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- No named inputs (every fact is a summand property of a threaded record or of the T11 reference). Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.
  `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
Three new modules (namespace `NSFormalization.Section3.T18`), each theorem's type = the Spec field's type with the Spec parameters replaced by `InsertionData` projections (same convention as
U1; probe each by the fieldwise conversion in `insertion_closes.lean`):
- `Section3/T18/ForceClass.lean` (U2): `force_mem` (`g_ε ∈ forceClassT` for `ε ∈ Ioc 0 ε₀`) and `forceDifference_mem` (`g_ε − g ∈ forceClassT`). Route: `g_ε − g = H_ε + F_ε`; `MemForceT`
  (smooth + unit-periodic + compact support in positive time) is closed under `+`; `H_ε ∈ 𝓕` from `correction.force_smooth`/`force_periodic`/`force_support`; `F_ε ∈ 𝓕` from `scaling.force_mem`;
  `+ g` via `reference_force_mem`.
- `Section3/T18/Kinematics.lean` (U3): `velocity_smooth`, `pressure_smooth` (smooth on `Ico 0 T ×ˢ univ`), `initial` (`u_ε(0,·) = a`), `history` (`u_ε = v` on `0 ≤ t ≤ T − 2ε²`),
  `velocity_periodic`. Route: summand facts — reference smoothness/periodicity, `correction.correction_smooth`/`correction_periodic`/`correction_support` (so `w_ε = 0` before `T − 2ε²`),
  the periodized packet's smoothness/periodicity/pre-activation vanishing from `scaling` (read which `ScalingAPI` fields give `U_ε = 0` for `t ≤ T − ε²` and `P_ε` likewise), `normalizePressureT`
  smoothness (T11).
- `Section3/T18/Divergence.lean` (U4): `incompressible` (`div u_ε = 0` on `Ico 0 T`) and `velocityDifference_divFree`. Route: `div v = 0` (reference), `div w_ε = 0` (`correction_divergence_free`,
  a spatial curl), `div U_ε = 0` (`scaling.solution.divergence`); additivity of the torus divergence for differentiable summands.
Deliverables: the three modules, `research/T18/probes/u2_u4_closes.lean` (Spec-form fields discharged from the canonical theorems via the U1 conversions), `research/T18/axioms_u2_u4.lean`,
`research/T18/ATTEMPTS_U2_U4.md`, status lines for U2/U3/U4 in `T18_SPLIT.md`. If one field genuinely needs a threaded fact that no record carries (say exactly which), deliver the others and
record the exact residual statement — do not add a named input.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.ForceClass NSFormalization.Section3.T18.Kinematics NSFormalization.Section3.T18.Divergence` (0 errors),
`lake env lean` on each module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T18/REPORT_426.md`.
