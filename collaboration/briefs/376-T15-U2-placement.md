# Lane 376-T15-U2-placement — T15 U2: scaled-support placement (each spatial slice of the rescaled packet fields lies in `x₀ + ε • K_* ⊆ ball chartCenter chartRadius ⊆ interior fundamentalCube`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/376-T15-U2-placement` (git branch `erenup/376-T15-U2-placement`, based on `origin/erenup/integration-section3` after #336:
`Section3/T15/{Bridges,ParsevalZero,HaarBridge}.lean` (lane 362's canonical rescaling definitions `scaledVelocity`/`scaledPressure`/`scaledForce` and their `rfl` bridges to
the I03 upstream spellings), `Section3/T13/ConstantEndpoints.lean` (`interior_fundamentalCube`, …)). Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U2 (and U3–U8 for
how the support lemmas are consumed)**, `research/T15/Spec.lean` (`PlacementData` `:560-650`: `chartCenter`, `chartRadius`, `chartBall_in_cube`, `Kstar`, `Kstar_compact`,
`carrier_subset`, `force_projection_subset`, `eps_space`; and the rescaled definitions), `research/T15/REPORT_362.md`, `Section4/I03/Energy.lean` (`scaled_slice_hasCompactSupport :197`,
`scaled_smoothOn :181` — the ℝ³ support shape), `verification/Contracts/V1/Packet.lean` (`PacketAPI.carrier`, `velocity_support`, `force_support`), and the top 40 lines of `logs/LESSONS.md`.
Note: `PlacementData` mentions `Contracts.V1.PacketAPI`, which `formalization/` cannot import; state the lemmas over the raw data (`x₀ chartCenter chartRadius Kstar ε₀ : …` and the
packet's raw fields `u f : VelocityField` with the `PacketAPI` support clauses as hypotheses verbatim), and add a probe that instantiates them from a `PlacementData P` (probes may import
`Contracts.*`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T15/Placement.lean` (namespace `NSFormalization.Section3.T15`): for `ε ∈ Ioc 0 ε₀` (with the `eps_space` hypothesis `ε * R_* < r`
or the Spec's exact form) and each `t`, `tsupport (fun x => scaledVelocity u x₀ T ε (t, x)) ⊆ x₀ + ε • Kstar` (the exact set spelling of the Spec: `{x₀ + ε • y | y ∈ Kstar}` or
`(fun y => x₀ + ε • y) '' Kstar` — match `research/T15/Spec.lean`), the same for `scaledPressure` and `scaledForce`, then the inclusions `x₀ + ε • Kstar ⊆ Metric.ball chartCenter chartRadius`
(from `eps_space` + `Kstar ⊆ ball 0 R_*` or the Spec's `∀ y ∈ Kstar, x₀ + ε • y ∈ ball …` form) and `Metric.ball chartCenter chartRadius ⊆ interior fundamentalCube` (`chartBall_in_cube`),
so the slices are supported strictly inside the fundamental cube (the hypothesis shape of `HaarBridge.eLpNorm_torusLift_periodize`, lane 364, and of `periodize_eq_of_mem_cube`). Also the
compactness of the slice support and `HasCompactSupport` of each slice. Route: unfold the rescaling (space scaled by `ε⁻¹` around `x₀`: `scaledVelocity u x₀ T ε (t,x) = ε⁻¹ • u (…, ε⁻¹ • (x − x₀))`
— check the exact formula in `Bridges.lean`), so a slice is nonzero only where `ε⁻¹ • (x − x₀) ∈ carrier ⊆ Kstar`, i.e. `x ∈ x₀ + ε • Kstar`; `tsupport` of the slice ⊆ closure of that set = itself
(compact). Reuse `I03/Energy.lean` support lemmas for the ℝ³ shape if they match.

## Deliverables
1. `Section3/T15/Placement.lean`; 2. probe `research/T15/probes/placement_closes.lean` (instantiate from a `PlacementData P` built on `Bindings.packet ν hν` if a placement witness is
cheap, else on raw data with explicit numbers; non-vacuity with `ε = ε₀/2`); 3. `research/T15/ATTEMPTS_U2.md`, `research/T15/axioms_u2.lean`, status in `research/T15/T15_SPLIT.md` U2,
report `research/T15/REPORT_376.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Placement` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T15/REPORT_376.md`.
