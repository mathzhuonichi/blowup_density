# Lane 254-R45-compact-rider — Corollary 4.5's regular-reference rider for `Y = F_c`: the `regularReference` field of `research/R45/Spec.lean` at `Y = forceClassCompact`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/254-R45-compact-rider` (git branch `erenup/254-R45-compact-rider`, based on lane 252's branch `erenup/252-R45-compact-class` =
`origin/erenup/integration` + `verification/Bindings/CompactClassDensity.lean` (`memForceCompact_add_memForceCompact`, `memForceR_of_memForceCompact`, `density_compact`, `zeroIff_compact`)).
Read `research/R45/Spec.lean` (the `regularReference` field — copy its statement with `Y := forceClassCompact`; note the rider's shape: `∀ δ > 0, ∀ v : ClassicalSolutionR ν a g (T+δ), ∀ τ, 0 ≤ τ → τ < T,
∀ r η > 0, ∃ f ∈ Y, ∃ u : ClassicalSolutionR ν a f T, maximalLifespanR = ofReal T ∧ ‖f − g‖ < r ∧ energyENorm T (u.velocity − v.velocity) < η ∧ history on [0, τ]` — read the exact conjuncts),
`research/R45/RECONCILIATION.md` §2.3, `research/R45/COMPARISON.md`, lane 249's `verification/Bindings/MainThresholds.lean` (**the template**: how Theorem 4.1's rider `regularReferenceApproximation`
was bound from ONE call of lane 233's `insertionLifespanV2_of_data`, with the reference identified to the quantified solution by registered uniqueness, history from the R42 record, force
convergence from `forceConvergence`, and the `E_T` limit squeezed from R42's registered rate — reuse those lemmas; R41's rider is `Tendsto`-shaped while R45's is ε-shaped with an arbitrary
history cutoff `τ < T`: derive the ε-form from the limits and pick `ε` small enough that `T − 2ε² ≥ τ`), `Bindings/InsertionFromData.lean` (lane 233; import caveat: not with `Bindings.Packet`),
`Contracts/V1/InsertionFamily.lean` (`history`, `forceDifference_compact`), `Contracts/V2/InsertionLifespan.lean`, `CLAUDE.md`, `collaboration/HANDOFF.md` §0, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; heartbeats ≤ 400000 per declaration, commented. No edits to existing modules/Bindings/Tests (252's file is on your base but unmerged — do not
  edit it); new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`ν = T = 1`, `a = 0`, `g = 0`).
- **Statement fidelity:** the theorem = the Spec field at `Y = forceClassCompact` with identical binders. If the ε-form history clause cannot be met for a given `τ` (e.g. `2ε₀² ≥ T − τ`), shrink
  `ε` — do not weaken the statement; if something genuinely resists, isolate ONE named hypothesis with its exact statement.

## Goal (in `verification/Bindings/CompactClassRider.lean`, namespace `BlowupDensity.Bindings`)
`regularReference_compact : <Spec.regularReference at Y = forceClassCompact>`; plus, if cheap, `regularReference_of_memForceR` (the same statement for `Y = F_R`, which R41's contract already
proves in `Tendsto` form — derive the ε-form once and specialize). Audit `research/R45/axioms_compact_rider.lean`; records `research/R45/ATTEMPTS_COMPACT_RIDER.md`; update `research/R45/COMPARISON.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build Bindings.CompactClassRider` (silent), `lake env lean Bindings/CompactClassRider.lean` (0 output), the audit, `make check`, `make test`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R45/REPORT_254.md`.
