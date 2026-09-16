# Lane 213-A02-A04-wiring — plug the A01 local theory into A02 (`exists_maximal`) and A04 (`Restart` → `restartBeyond`/`extendsBeyond`/`lifespanInfiniteOfLocallyFinite`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/213-A02-A04-wiring` (git branch `erenup/213-A02-A04-wiring`, based on `origin/erenup/integration`, which contains lane 211's
`Section4/A01/LocalTheoryBundle.lean` (`localHorizon'`, `localCarrier` with `.w : ClassicalSolutionR ν a f (localHorizon' ν a f)` for `0 < ν`, `a ∈ initialClassR`, `MemForceR f`;
`manuscriptLocalRegularity_localCarrier`; `horizon_lower_bound_H7_fixedForce`), lane 179's `GronwallEndpoint.lean` (uniform `H^m` bounds on `Ico 0 T` from the `H²` cap), lanes 149/147
(`AprioriRows`, `OrderTwoCap`), and A02/A04). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7/P9, `Section4/A02/Maximal.lean:140-200` (`exists_maximal_of_localSolution
(horizon) (localSolution : ∀ ν a f, 0 < ν → a ∈ initialClassR → MemForceR f → ClassicalSolutionR ν a f (horizon ν a f)) …` and `maximal_unique`), `Section4/A04/Continuation.lean:40-240`
(`structure Restart`, `HigherOrderBound`, `restartBeyond_of_restartAt`, `restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`), `research/A04/Spec.lean` (`restartBeyond`,
`extendsBeyond` shapes), `research/A01/REVIEW.md` (M5: what A04's restart needs from A01), `research/A02/COMPARISON.md`, `research/A04/COMPARISON.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`).
- **Satisfiability rule:** if one genuinely missing fact remains (e.g. the restart datum's membership in `initialClassR`, or a force-shift lemma), isolate it exactly as ONE named
  hypothesis; do not weaken A02/A04's conclusions.

## Goal
1. **A02:** `theorem exists_maximal' : …` := `exists_maximal_of_localSolution localHorizon' (fun ν a f hν ha hf => (localCarrier ν a f hν ha hf).w) …` — the spec field with no
   explicit local-existence hypothesis; also the accessor lemmas A02's `Spec.lean` §4 expects (`maximal_unique` unchanged).
2. **A04 `Restart`:** inspect `structure Restart` (`Continuation.lean`): it packages "restart at `t₀ ↑ S` with the same force gives a solution on `[t₀, t₀+δ)` with `δ` uniform
   over the restart data". Construct it from the bundle: the restart datum `a' := u(t₀,·)` is in `initialClassR` (lane 209's `sobolev_smooth` all-order data + divergence at every time —
   prove `initialClassR` membership of a slice; grep `A02/Restrict.lean` `restart_datum`), the shifted force is in `MemForceR` (lane 160's `ForceShift`), and the uniform `δ` comes from
   `horizon_lower_bound_H7_fixedForce` with `K :=` the Grönwall bound of `sobolevENorm 7 (u(t₀,·))` uniform in `t₀ < S` (lane 179's `GronwallEndpoint`, given the `H²` cap / eq:criterion
   hypothesis that `Restart`/`extendsBeyond` already carry). Then `restartBeyond'`, `extendsBeyond'`, `lifespanInfiniteOfLocallyFinite'` as unconditional instances of A04's theorems
   (with `HigherOrderBound` discharged by lane 179 if its shape matches; else say exactly what remains).
3. Record in `research/A02/` and `research/A04/` what is now unconditional vs what (if anything) still carries a named input.

## Deliverables
1. New modules `formalization/NSFormalization/Section4/A02/MaximalWiring.lean` and `formalization/NSFormalization/Section4/A04/RestartWiring.lean`.
2. Records `research/A02/ATTEMPTS_WIRING.md`, `research/A04/ATTEMPTS_RESTART_WIRING.md`, conformance `research/A02/axioms_wiring.lean`, `research/A04/axioms_restart_wiring.lean`.

## Gates
`lake build` both modules (silent), `lake env lean` on each (0 output), the axioms files, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A02/REPORT_213.md`.
