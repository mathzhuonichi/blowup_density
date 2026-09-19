# Lane 461-T19-U0-insertion-from-reference — T19 U0: thread a regular reference through T15/T17/T18 (`insertionData`, `insertion`, export lemmas)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/461-T19-U0-insertion-from-reference` (git branch `erenup/461-T19-U0-insertion-from-reference`, = `origin/erenup/integration-section3` after lanes 455 (T18 U12), 459 (T15 U15) and
460 (T17 U13) merged). Read `CLAUDE.md`, `research/T17/SPEC_ISSUES.md` §G5 (why this unit exists), **`research/T19/T19_SPLIT.md`** (§0 and wave 2: U7/U8/U9/U13 all start with "from `RegularThroughT ν a g T` build `ins` (T18 U12)" —
this lane builds `ins` once, for everybody), `research/T18/REPORT_455.md` + `Section3/T18/Assembly.lean` (`InsertionData` — 19 fields incl. `place`, `scaling`, `reference`, `correction`; `RawPremises` = `hsupp`/`hM`/`hD`;
`assemble`; `PeriodicInsertionAPI data`), `research/T15/REPORT_459.md` + `Section3/T15/Assembly.lean` (`placementData … T hT` with `(placementData …).T = T` by `rfl`, `scalingAPI`, the raw packet clauses they take),
`research/T17/REPORT_460.md` + `Section3/T17/SlabBridge.lean` (`correctionStatementSlab_holds` and the probe `research/T17/probes/slab_from_classical.lean` — the exact call for a `ClassicalSolutionT` reference),
`verification/Bindings/PacketImport.lean` (`packetImportFamily : PacketImportFamily`, `.select ν hν : PacketImportAPI ν`; raw fields `velocity pressure force carrier energyBound dissipationBound`, clauses `velocity_support`,
`carrier_compact`, `force_support`, …; for `0 ≤ energyBound`/`0 ≤ dissipationBound` mirror how `research/T18/probes/*.lean` discharged `hM`/`hD` from the energy API — grep `energy_isLUB`, `dissipation_eq`),
`verification/Contracts/V1/TorusLocalTheory.lean:130-210` (`ClassicalSolutionT` fields: `velocity_smooth` on `Ico 0 T ×ˢ univ`, `velocity_periodic : IsPeriodicOn (Ico 0 T) velocity`, `divergence : ∀ t ∈ Ico 0 T, ∀ x, …`;
`RegularThroughT ν a f T := ∃ δ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))`), `Section3/T19/Density.lean` (lane 457's canonical T19 records), and the top 40 lines of `logs/LESSONS.md`.
**Verify every name above by `grep -rn` before use** — the three upstream lanes may have chosen slightly different spellings; cite what is actually in the tree.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure first
  (`lake build NSFormalization.Section3.T18.Assembly NSFormalization.Section3.T15.Assembly NSFormalization.Section3.T17.SlabBridge`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]` (`Classical.choose` on the T17 existential is fine). `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed
  approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T19/Threading.lean` (namespace `NSFormalization.Section3.T19`), for `{ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField} (ha : a ∈ initialClassT) (hg : g ∈ forceClassT)
{T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (reference : ClassicalSolutionT ν a g (T + δ))`:
1. `noncomputable def insertionData … : InsertionData` — packet `P := packetImportFamily.select ν hν` (raw fields projected), `place := placementData … T hT` (T15 U15), `scaling := scalingAPI …` (T15 U15, its raw clauses from `P`),
   `a g δ reference` as given, `r` chosen so that `0 < r`, `r < 1/2`, `ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius` (e.g. `r := (place.chartRadius − dist place.x₀ place.chartCenter)/2`, or whatever 459's placement
   makes trivial — `x₀ = chartCenter` gives `r := chartRadius/2`; `chartRadius < 1/2` follows from `chartBall_in_cube`), `D`/`correction` := `Classical.choose`/`choose_spec` of `correctionStatementSlab_holds ν … place reference.velocity r δ hν hr hr2 hδ
   reference.velocity_periodic reference.velocity_smooth hdiv hsupp hball` (`hdiv` from `reference.divergence` restricted to `Ioo 0 (T+δ) ⊆ Ico 0 (T+δ)`; `hsupp` from `P.velocity_support` + `carrier_subset`-type facts as the slab
   statement spells them). The `reference` field must typecheck against `place.T + δ` — with `(placementData … T hT).T` reducing to `T` this is definitional; if 459 shipped an `∃`-form only, record that as the residual and stop.
2. `theorem insertionData_rawPremises … : RawPremises (insertionData …)` (`hsupp` from `P.velocity_support`, `hM`/`hD` as in the T18 probes).
3. `noncomputable def insertion … : PeriodicInsertionAPI (insertionData …) := assemble _ (insertionData_rawPremises …)`.
4. **Export lemmas** (so U7–U14 never open `InsertionData`): with `ins := insertion …` and `ε₀ := ins.ε₀`, restate over `a g T` directly (the `data.a`/`data.g`/`data.place.T` projections must reduce by `rfl`/`show`):
   `insertion_eps_pos : 0 < ε₀`, `force_mem : ∀ ε ∈ Ioc 0 ε₀, ins.force ε ∈ forceClassT`, `lifespan : ∀ ε ∈ Ioc 0 ε₀, maximalLifespanT ν a (ins.force ε) = ENNReal.ofReal T`, `solution : ∀ ε ∈ Ioc 0 ε₀, ∃ w : ClassicalSolutionT ν a (ins.force ε) T,
   w.velocity = ins.velocity ε ∧ w.pressure = ins.pressure ε`, `blowup_limsup`, `energyRate` (with `reference.velocity` and the constants spelled as in T18), `forceDifference_mixed_bound`, `forceDifference_sobolev_bound`,
   `forceDifference_negativeSobolev_tendsto`, and the honesty guards (`MemMixedLebesgueT`, `MemForceSobolevT`) — copy the T18 field statements verbatim with the substitutions.
5. `theorem exists_insertion_of_regularThrough … (hreg : RegularThroughT ν a g T) : ∃ δ, 0 < δ ∧ ∃ reference : ClassicalSolutionT ν a g (T + δ), True` is NOT wanted (it is `regularThrough_iff`); instead give U7 the
   packaging it needs: `theorem exists_force_close … (hreg : RegularThroughT ν a g T) (s : ℝ) (hs : s < 1/2) (r' : ℝ) (hr' : 0 < r') : ∃ f ∈ forceClassT, maximalLifespanT ν a f = ENNReal.ofReal T ∧ forceSobolevENormT 1 s (fun z => f z − g z) < ENNReal.ofReal r'`
   — the "eventual `< r`" step of `T19_SPLIT.md` U7/U8 done once (`forceDifference_sobolev_bound` for `0 ≤ s < 1/2` with the powers `→ 0` along `𝓝[>] 0`, `forceDifference_negativeSobolev_tendsto` for `s < 0`, `Ioc_mem_nhdsGT`).
   If this last theorem does not close in time, deliver 1–4 and record its exact residual.
Deliverables: the module, `research/T19/probes/threading_closes.lean` (each export lemma by `exact`), `research/T19/axioms_u0.lean`, `research/T19/ATTEMPTS_U0.md`, a U0 status line + the U7/U8/U9/U13 route note ("build `ins` = `T19.insertion`") in
`research/T19/T19_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Threading` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T19/REPORT_461.md`.
