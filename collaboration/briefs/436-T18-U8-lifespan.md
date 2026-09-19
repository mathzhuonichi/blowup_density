# Lane 436-T18-U8-lifespan — T18 U8: the inserted solution, lifespan exactly `T`, maximality and blow-up (clause (i))

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan` (git branch `erenup/436-T18-U8-lifespan`, = lane 433's branch + `origin/erenup/integration-section3`: the T18 layer
`Section3/T18/{Insertion,ForceClass,Kinematics,Divergence,CrossTransport,Momentum}.lean` (U1–U6: smoothness, initial value, history, periodicity, incompressibility, exact momentum), the canonical T15
`ScalingAPI` (`scaling.solution`, `unboundedSpeed`, single copy, placement), the canonical T17 `CorrectionAPI` (`correction_cancels`, `correction_support`), the registered T11 contract
`Contracts/V1/TorusLocalTheory.lean` (`ClassicalSolutionT`, `maximalLifespanT`, `IsMaximalPeriodicSolution`, `torusLocalTheoryAPI.velocity_unique :467`, `torusContinuationH3API.lifespanInfiniteOfLocallyFinite :579`,
`higherOrderBound :539`) with its `Bindings/TorusLocalTheory.lean` (structure conversions, `maximalLifespanT_eq`) and the canonical T11 modules (`Section3/T11/ClassicalRegularity.lean`
`regularity_of_classical`, `Section3/T11/*` datum paths), T12's `boundedRepresentative` (`Section3/T12/FourierEmbeddings.lean:386`)). Read `CLAUDE.md`, **`research/T18/T18_SPLIT.md` §0 and unit U8**
(`:129-148`, routes (a)–(e); uses only the H³-narrowed continuation API — no `PeriodicRestartH1`, see `research/T11/H1_GAP.md` §4), the Spec fields `research/T18/Spec.lean:1796` (`solution`), `:1806`
(`maximal`), `:1812` (`lifespan`), `:1818` (`blowup`), `:1825` (`blowup_limsup`), the R³ analogue `Section4/R42/` (`LIFESPAN_SPLIT.md`, `MAXIMAL_SPLIT.md`, `Bindings/InsertionLifespan.lean` §9
`isMaximalSolution_of_inserted`, `blowup_essSup`), `research/T18/REPORT_{422,426,433}.md` and probes, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** — every fact comes from a threaded record field, the registered T11/T12 contracts, or the T18 U1–U6 layer. An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T18/Lifespan.lean` (namespace `NSFormalization.Section3.T18`), the five fields under `InsertionData` projections:
(a) `solution`: a full-horizon `ClassicalSolutionT ν a (force ε) place.T` for the inserted triple — fields from U3/U4/U6 plus the Sobolev datum path (cutoff-in-time the compact-support difference
`w_ε + U_ε`, angular path smoothness, added to `reference.sobolev`; mirror R42 residual 1a/1e-i) and `pressure_gradient`; regularity via `regularity_of_classical`.
(b) `blowup`: on the active support `u_ε = U_ε` (U5's cancellation), so `SpeedUnboundedAt` transfers from `scaling.unboundedSpeed`.
(c) `blowup_limsup`: pointwise unbounded speed + slice continuity ⟹ ess-sup lower bound (`IsOpenPosMeasure`) ⟹ `limsup … = ⊤` (mirror R42 `blowup_essSup`).
(d) `lifespan = place.T` by `le_antisymm`: `≥` from (a) on every horizon `S < T` + `velocity_unique`; `≤` from `lifespanInfiniteOfLocallyFinite` + `higherOrderBound` at `m = 3` against (c),
transferred `L^∞ → H²` by `boundedRepresentative`.
(e) `maximal`: `IsMaximalPeriodicSolution` from (d), the shorter-horizon family and `velocity_unique`.
This is an L unit: if one of (a)–(e) genuinely cannot be closed from the records + registered APIs, deliver the others and isolate the exact residual statement (probe-level only). Deliverables: the
module, `research/T18/probes/u8_closes.lean` (Spec-form fields via the U1 conversions), `research/T18/axioms_u8.lean`, `research/T18/ATTEMPTS_U8.md`, U8 status line in `T18_SPLIT.md`, one
`logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Lifespan` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Try `research/T18/REPORT_436.md`; if the report-file guard blocks
it, put the full report in your final message.
