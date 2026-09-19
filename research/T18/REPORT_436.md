# REPORT_436 — T18 U8 lifespan exactly T (Opus; transcribed by lead from the agent message, report-file guard)

Lane 436 (T18 U8) is complete and committed. Report follows.

## 1. What was proved

All five U8 fields of the reconciled `PeriodicInsertionAPI` — (a)–(e) — are closed. Nothing is residual, nothing is a named input, no `sorry`/`axiom`/`native_decide`.

Over the canonical bundle `data : InsertionData` (the U1 record threading the raw packet fields, the T15 `PlacementData`/`ScalingAPI`, the T10 reference solution, the T17 `CorrectionAPI`, and the three paper hypotheses), for every `ε ∈ Ioc 0 (ε₀ data)`:

- **(a) `solution`** — `∃ w : ClassicalSolutionT data.ν data.a (force data ε) data.place.T, w.velocity = velocity data ε ∧ w.pressure = pressure data ε`. The witness `insertedSolution` is a full 13-field record on the whole horizon `[0,T)`.
- **(b) `blowup`** — `NSFormalization.Source.PacketScaling.SpeedUnboundedAt data.place.T (velocity data ε)`.
- **(c) `blowup_limsup`** — `NSFormalization.Section4.A02.limsupLeft data.place.T (fun t ↦ A02.speedENorm (fun x : Space ↦ velocity data ε (t, x))) = ⊤` (the `A02` spellings are `rfl`-equal to `Contracts.V1.MaximalPartial.limsupLeft`/`speedENorm`, `Bindings/MaximalPartial.lean:57,61`).
- **(d) `lifespan`** — `maximalLifespanT data.ν data.a (force data ε) = ENNReal.ofReal data.place.T`.
- **(e) `maximal`** — `NSFormalization.Section3.T11.IsMaximalPeriodicSolution data.ν data.a (force data ε) (velocity data ε) (pressure data ε)`.

Two route changes against `T18_SPLIT.md` U8, both of which **shrink** the dependency set:

1. `solution`'s `sobolev` and `pressure_gradient` need none of the R42 residual-1a/1e-i machinery (time cutoff, `contDiff_angularPath`, datum-path addition). On the compact torus a slab-smooth unit-periodic slice already carries a datum at every order (`T11.exists_periodicDatum_smooth`) and the selected path is continuous on the same `Ico 0 T` (`T11.continuousOn_periodicDatum_path_of_slab`); `pressure_gradient` is one `T10.memLp_torusLift_vector`.
2. The `≤ T` half of `lifespan` does **not** use `lifespanInfiniteOfLocallyFinite` + `higherOrderBound` + `boundedRepresentative`. Instead: if some horizon `S > T` carried a solution `w`, `T11.velocity_unique` would identify `w.velocity` with `u_ε` on `[0,T)`, and a slab-smooth unit-periodic field is bounded on `Icc 0 T × R³` (compactness of `Icc 0 T ×ˢ fundamentalCube` plus the lattice reduction `x ↦ ⌊x i⌋` and `T13.periodic_latticeVector`) — contradicting (b).

**Consequence worth flagging to the lead:** U8 consumes **no field of `torusContinuationH3API`** and **nothing from T12**. The only T11 field it uses is `torusLocalTheoryAPI.velocity_unique`, which carries no data ball at all. So `research/T11/H1_GAP.md` §4's "expected OK" verdict holds a fortiori, and `PeriodicRestartH1`/`PeriodicRestartBeyondH1` stay unconsumed with room to spare.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/formalization/NSFormalization/Section3/T18/Lifespan.lean` — new, 350 lines, 21 declarations. Key ones: `insertedSolution:150`, `solution:167`, `blowup:177`, `blowup_limsup:207`, `exists_speed_bound:249`, `lifespan_le:273`, `lifespan:300`, `insertedSolutionOn:308`, `maximal:338`. Supporting: `pressureGaugeT_normalize`, `isPeriodicOn_normalizePressureT`, `pressure_periodic`, `pressure_gauge`, `sobolev_path`, `pressure_gradient_memLp`, `exists_sub_latticeVector_mem_fundamentalCube`, `isCompact_fundamentalCube`. Imports only `Section3.T18.Momentum`, `Section3.T11.ExtendsBeyond`, `Section4.R42.BlowupEssSup`. No `set_option maxHeartbeats` was needed anywhere.
- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/research/T18/probes/u8_closes.lean` — Spec-form conformance: `Spec.PeriodicInsertionU8Fields` states the five fields in the **registered contract** vocabulary (`Contracts.V1.TorusLocalTheory.{ClassicalSolutionT, IsMaximalPeriodicSolution, maximalLifespanT}`, `Contracts.V1.SpeedUnboundedAt`, `Contracts.V1.MaximalPartial.{limsupLeft, speedENorm}`), and `insertionU8OfCanonical` discharges them from the canonical theorems through the U1 conversions plus `Bindings.TorusLocalTheory.{toContract, isMaximalPeriodicSolution_eq, maximalLifespanT_eq}`.
- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/research/T18/axioms_u8.lean` — all 21 declarations audited.
- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/research/T18/ATTEMPTS_U8.md` — successful routes and every rejected/failed approach.
- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/research/T18/T18_SPLIT.md` — U8 status paragraph added.
- `/data_8T/ping/blowup_density/.claude/worktrees/436-T18-U8-lifespan/logs/LESSONS.md` — one line at the top.
- Commit `26af11b8` on `erenup/436-T18-U8-lifespan`. No push, no merge, no rebase; no existing module was edited.

Per my operating instructions I did **not** write `research/T18/REPORT_436.md`; this message is the report.

## 3. Gap

No mathematical gap inside U8 — all five fields are theorems over the threaded structure hypotheses. What remains outside this unit:

- **Non-vacuity is still elsewhere.** As with U1–U6, every field is proved *given* `scaling : ScalingAPI` and `correction : CorrectionAPI`; the concrete end-to-end inhabitation waits on T15 U15 and the T17 assembly witnesses. U8 adds no new gate.
- **Two facts the tree does not contain** (found while rejecting the split's route, both recorded in ATTEMPTS_U8 §"Rejected"):
  - no torus analogue of A02's registered `MaximalPartial.lifespan_le_of_unbounded`; `grep -rn "maximalLifespanT" formalization/NSFormalization/` yields only lower-bound lemmas (`lifespan_ge_of_horizon`, `lifespan_ge_of_extends`, `maximalLifespanT_eq_lifespan`, `horizon_le_lifespan`);
  - no bridge between `periodicLpENorm ⊤ v = eLpNorm (torusLift v) ⊤ periodicTorusMeasure` (Haar essSup, what `T12.boundedRepresentative` bounds) and `speedENorm z = eLpNorm z ⊤ (volume : Measure Space)` (Lebesgue essSup, what `blowup_limsup` uses). `grep` for `periodicLpENorm ⊤` finds only `FourierEmbeddings.lean:388,464,472`, `Contracts/V1/MeanZeroCalculus.lean:223`, `Tests/MeanZeroCalculus.lean:69`. These are equal for continuous periodic fields, but proving it needs an `IsOpenPosMeasure`-style argument on `PeriodicTorus` that is also absent. If a later unit (T19/T21) wants to combine `boundedRepresentative` with the `L^∞` blow-up vocabulary, that bridge is the missing piece.
- No error text to report: the final state compiles clean.

Errors encountered and fixed along the way (full text in ATTEMPTS_U8):
- `Application type mismatch: the argument integrable_const ?m.53 has type Integrable (fun x => ?m.53) ?m.50 but is expected to have type Integrable (fun y => pressureMeanT q (t, NavierStokes.PeriodicIntegration.toSpace ↑((UnitAddTorus.measurableEquivPiIoc 0) y)).1) periodicTorusMeasure` — the unfolded `torusLift` makes the subtracted mean non-syntactically-constant; fixed by naming the constant's integrability in its own `have`.
- `Type mismatch: After simplification, term Eq.symm h has type u (t, x - T13.latticeVector n) = u (t, x) but is expected to have type u (t, x) = u (t, x - T13.latticeVector n)` — `simp` already cancels `(x - v) + v`, so `.symm` was one flip too many.
- Two linter-only failures (the gate is "0 output"): an unused `hT₀ : 0 ≤ T₀` in `exists_speed_bound`, and `fun ε hε ↦ …` bodies needing an explicit `(ε := ε)`.

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, with `lake` invoked from `verification/` and `LEAN_NUM_THREADS=6`.

| command | result |
|---|---|
| `lake build NSFormalization.Section3.T18.Momentum` | `Build completed successfully (10021 jobs).` (baseline) |
| `lake build NSFormalization.Section3.T11.ExtendsBeyond NSFormalization.Section4.R42.BlowupEssSup NSFormalization.Section3.T12.FourierEmbeddings` | exit 0 (dependency warm-up) |
| `lake build NSFormalization.Section3.T18.Lifespan` | `✔ [10611/10611] Built NSFormalization.Section3.T18.Lifespan (2.0s)` — `Build completed successfully (10611 jobs).`, **0 errors** |
| `lake env lean ../formalization/NSFormalization/Section3/T18/Lifespan.lean` | **no output**, exit 0 |
| `lake env lean ../research/T18/probes/u8_closes.lean` | **no output**, exit 0 |
| `lake env lean ../research/T18/axioms_u8.lean` | exit 0; all **21** declarations print exactly `[propext, Classical.choice, Quot.sound]` |
| `lake env lean` on a `tmp/` copy of the probe with `#print axioms` appended | `insertionU8OfCanonical` and `insertionU1OfCanonical` both `[propext, Classical.choice, Quot.sound]`; temp file deleted |
| `grep -rn "sorry\|admit\|native_decide\|^axiom " <the three new files>` | no matches |
| `make check` | architecture checks OK; `test_contract_policy.py` — `Ran 13 tests … OK`; `check_work_queue.py` — `45 work items: ownership, contract registration and task cards consistent.` |
| `make test` | completed through `[10904/10904] Replayed Tests.CompletedDensity`; every registered contract line reads `checked; standard logical axioms only` |
| `git commit` | `26af11b8 [436-T18] U8: full-horizon solution, blow-up, lifespan exactly T, maximality`; working tree clean afterwards |
