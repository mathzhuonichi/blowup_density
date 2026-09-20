# Lane 215-A04-restart-fixed-force — the restart step uniform over all restart times of one force (`RestartFixedForce`), and the bridge from lane 179's Grönwall to A04's `HigherOrderBound`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/215-A04-restart-fixed-force` (git branch `erenup/215-A04-restart-fixed-force`, based on `origin/erenup/integration` **plus** lane 213's
branch `erenup/213-A02-A04-wiring` (being merged as PR #218: `Section4/A02/MaximalWiring.lean`, `Section4/A04/RestartWiring.lean` — restart slice `∈ initialClassR`, `timeShift t₀ f ∈ MemForceR`,
per-time local restart, fixed-shifted-force H⁷-uniform existence)). On integration: lane 211's `LocalTheoryBundle.lean` (`localHorizon'`, `localCarrier`, `horizon_lower_bound_H7_fixedForce`,
`uniformHorizon_antitone`), lane 210's `HorizonUniform.lean`, lane 179's `GronwallEndpoint.lean` (uniform `H^m` bounds on all of `Ico 0 T` with the endpoint constant from the `H²` cap),
lanes 149/147 (`AprioriRows`, `OrderTwoCap`), lane 160's `A04/ForceShift.lean`, A04's `Continuation.lean` (`structure Restart`, `HigherOrderBound`, `restartBeyond`, `extendsBeyond`,
`lifespanInfiniteOfLocallyFinite`, the restart at `Continuation.lean:101-109` with `timeShift t₀ f`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P9,
`research/A02/REPORT_213.md` §3 and `research/A04/ATTEMPTS_RESTART_WIRING.md` (the interface table), `research/A01/REVIEW_210-A01-horizon-uniform.md` §2.4 (the vendor's
`forced_uniform_restart_time`: one window length uniformly over restart points for one force bundle — grep it in `vendor/NavierStokesAndEuler/Euler`), `research/A04/Spec.lean`
(`restartBeyond`/`extendsBeyond` shapes), `research/A01/REVIEW.md` M5, `paper/sections/appendix-a-local-theory.tex:140-157`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules (in particular do NOT
  change A04's `Restart`/`HigherOrderBound` definitions — the owner's decision on their V2 wording is pending); new files only. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol`).
- **Satisfiability rule:** if one genuinely missing fact remains, isolate it as ONE named hypothesis with the exact statement.

## Goal (formalization-level; the contract/def re-cut is a separate decision)
1. `def RestartFixedForce (ν) (f) (S) : Prop` — the paper's restart step (Appendix A:147-150) for **one** force: `∀ K ≠ ⊤, ∃ δ > 0, ∀ t₀ ∈ Icc 0 S, ∀ a', a' ∈ initialClassR →
   sobolevENorm 7 a' ≤ K → δ ≤ localHorizon' ν a' (timeShift t₀ f)` (δ before `t₀` and `a'`). Prove `restartFixedForce_of_memForceR : MemForceR f → RestartFixedForce ν f S` for `0 < ν`,
   `0 ≤ S`: the sup-in-time order-6 norm of `timeShift t₀ f`'s force path on `[0,1]` is bounded by the sup on `[0,S+1]` (continuity of the jets of `C01.forcePath` on a compact interval),
   then lane 211's antitone selection (`uniformHorizon_antitone`) gives one `δ`; alternatively use the vendor's `forced_uniform_restart_time` directly if it matches — say which.
2. `HigherOrderBound` ↔ lane 179: state exactly A04's `HigherOrderBound` and prove `higherOrderBound_of_gronwall : … → HigherOrderBound …` from `GronwallEndpoint`'s uniform `H^m`
   bound given the `H²` cap (`kbnd_of_sup_bound_Icc_endpoint` / eq:criterion), including the bridge the 213 report names (the closed-interval cylinder carrier and its norm bound for the
   same classical solution — available from lane 211's `LocalCarrier`?). If a piece is genuinely missing, isolate it.
3. Consumers: show (probe) that A04's `restartBeyond`/`extendsBeyond`/`lifespanInfiniteOfLocallyFinite` proofs use `Restart` only through restarts of the **same** force at times
   `t₀ ∈ [0,S]` with Grönwall-bounded data (read `Continuation.lean:100-240`), so that a V2 `RestartFixedForce`-shaped hypothesis suffices: prove `restartBeyond_fixed`,
   `extendsBeyond_fixed`, `lifespanInfiniteOfLocallyFinite_fixed` as **copies of A04's theorems with `Restart` replaced by `RestartFixedForce`** (new declarations, A04's untouched),
   then instantiate them with items 1–2 to get the unconditional continuation theorems for `MemForceR` forces. If a proof genuinely needs cross-force uniformity, report exactly where.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean` (namespace `NSFormalization.Section4.A04`).
2. Records `research/A04/ATTEMPTS_RESTART_FIXED_FORCE.md`, update `research/A04/COMPARISON.md` (what is now unconditional; the V2 wording question), conformance
   `research/A04/axioms_restart_fixed_force.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.RestartFixedForce` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A04/REPORT_215.md`.
