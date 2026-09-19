# Lane 441-T20-U12-global-regularity — T20 U12: `globalRegularity` verbatim (`prop:critical`: under `ρ < cν` the from-rest solution is global)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/441-T20-U12-global-regularity` (git branch `erenup/441-T20-U12-global-regularity`, = lane 437's branch + `origin/erenup/integration-section3`:
`Section3/T20/{CriticalRegularity,MeanReduction,BIntegral,ConstantTransport,CriticalTrilinear,CriticalEnergy,YBound,H1Trilinear,H1Energy,Continuation}.lean` — lane 437's `continuationBound` at
`c := criticalSmallnessH1`, `Ccriterion`, and its reusable pieces (`meanFreeHTwoSq_integral_le`, `meanFreeForceLTwoSqIntegral_ne_top`, `memForceT_meanFreeForce`); the canonical T11 modules
(`Section3/T11/Assembly.lean:318` `lifespanInfiniteOfLocallyFinite` — the proved H³-narrowed continuation field; `Section3/T11/ExtendsBeyond.lean`, lower-bound lemmas
`lifespan_ge_of_horizon`/`lifespan_ge_of_extends`/`maximalLifespanT_eq_lifespan`/`horizon_le_lifespan`, `velocity_unique`); `squaredHTwoIntegralT` in `Section3/T11`). Read `CLAUDE.md`,
**`research/T20/T20_SPLIT.md` §0 and unit U12** (`:257-264`), the canonical field `globalRegularity` (`Section3/T20/CriticalRegularity.lean:365-368`: `∀ ν, 0 < ν → ∀ g ∈ forceClassT, criticalRho g <
ofReal (c·ν) → maximalLifespanT ν (fun _ ↦ 0) g = ⊤`), `paper/sections/03-torus.tex:486-505`, `research/T20/REPORT_437.md` §1/§3, `research/T20/H1_CHECK.md` §Consumer (only the H³-narrowed API is
needed; `PeriodicRestartH1` is NOT a T20 obligation), the R³ analogue `Section4/R44/Prop44.lean` and `Section4/R43/Endpoint.lean` (S5), the exact statement of `lifespanInfiniteOfLocallyFinite`
(`sed -n 310,330p formalization/NSFormalization/Section3/T11/Assembly.lean`; read what "locally finite" means there — which `S`, which squared-`H²` integral, which horizon quantifier), and the top 40
lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first (`lake build <module>`), never assume `.olean`s exist.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Goal
New module `formalization/NSFormalization/Section3/T20/GlobalRegularity.lean` (namespace `NSFormalization.Section3.T20`): `theorem globalRegularity` whose type is literally the canonical field at
`c := criticalSmallnessH1` (probe `example : globalRegularityFieldType criticalSmallnessH1 := globalRegularity` mirroring lanes 428/432/437's probe pattern). Route: for every finite horizon `S` with
`ofReal S < maximalLifespanT ν 0 g` (or `≤`, per the continuation API's quantifier), T11 gives a classical solution `w` on `[0,S)` (`maximalLifespanT_eq_lifespan` / the existence side of the maximal
lifespan — read `ExtendsBeyond.lean`), and U11 gives `squaredHTwoIntegralT S w.velocity ≠ ⊤` (its three conjuncts); if the continuation API needs the bound for **all** `0 < S ≤ T` uniformly or for
the specific solution family it quantifies over, match that spelling (uniqueness `velocity_unique` identifies any two solutions on a common horizon); then `lifespanInfiniteOfLocallyFinite` yields
`maximalLifespanT ν 0 g = ⊤`. Handle the zero-force/zero-solution case only through the general argument. Deliverables: the module, `research/T20/probes/global_regularity_closes.lean`
(field-type match; non-vacuity at the zero-force instance with the satisfiable smallness `ρ = 0 < c·ν`), `research/T20/axioms_u12.lean`, `research/T20/ATTEMPTS_U12.md`, U12 status line in
`T20_SPLIT.md`, one `logs/LESSONS.md` line if pin-specific.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.GlobalRegularity` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T20/REPORT_441.md`.
