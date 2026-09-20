# Lane 193-A01-a3-m2-bounds — A3-M2: the all-order a-priori bound family on the order-six horizon (base-order-radius route)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/193-A01-a3-m2-bounds` (git branch `erenup/193-A01-a3-m2-bounds`, based on
`origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/A3_SPLIT.md` (rows A3-M2, A3-L1·k, A3-U),
`Section4/A01/Horizon.lean` (`HasAprioriBound`, `localTheory_on_prescribed_horizon`), `Section4/A01/AprioriInvariance.lean` (173),
`Section4/A01/OrderTwoCap.lean:209-246` (`kbnd_of_sup_bound`: from `‖u‖ ≤ R` the `H²` time-integral cap `256·R²·T₀`), `Section4/A01/GronwallInstance.lean`,
`AprioriRows.lean`, `GronwallEndpoint.lean` (149/179: the Grönwall output for a `ClassicalSolutionR`), `Section4/A01/CommonHorizon.lean` (186: lowering
`restrictOperator` commutes with `quadraticDuhamel`), `Section4/A01/MildUniqueness.lean` (188: `mildUniqueness`), the vendor's local existence and
continuation for `quadraticDuhamel` (`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean` and neighbours: grep `exists_local`, `continuation`,
`extend`, `lifespan`, `norm_le`, `ballLipschitz`, `kernelMass`), `research/A01/REVIEW_192-A01-wiring-hsob.md:105-125` (the reviewer's route), and the
top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** every named input must be a restriction of a standard property that a genuine (nonzero) local solution has; one sentence each.
- Do NOT route through the all-order constructor (that would assume the conclusion).

## The problem
Lane 192 wires everything downstream of `hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q)` (uniform bound of every order-`q` mild solution
on every subwindow of one prescribed `[0,S]`). Supplying `hb` is the last analytic unit of A3 (row A3-M2). The naive route is circular (radius before
solution). The non-circular route (paper `appendix-a-local-theory.tex:60-80`; reviewer 192):
1. **Base order:** take `q₀ = 6`; the vendor's local existence gives a horizon `S₆ = S₆(ν, a, F)` and radius `R₆` with `‖u₆‖ ≤ R₆` for the order-6
   mild solution on `[0,S₆]` (and every subwindow). This *is* `HasAprioriBound (q := 6) … R₆` on `[0,S₆]` once uniqueness (188) identifies any
   competitor with `u₆`. Prove it: `hasAprioriBound_base`.
2. **Higher orders:** for `q > 6`, any order-`q` mild solution `u` on `[0,T] ⊆ [0,S₆]` lowers (186) to an order-6 fixed point, hence equals `u₆|[0,T]`
   (188), so its order-2 norm path is controlled by `R₆`: `kbnd_of_sup_bound` gives the `H²` integral cap `Kbnd := 256·R₆²·T` independent of `q`.
   Then the **mild-level** Grönwall: the order-`q` norm of `u` is bounded by `(‖u₀‖_{q+1} + ‖F‖_{L¹H^q})·exp(C_q ν · Kbnd)` — check whether the tree has
   this for mild/cylinder solutions (`GronwallInstance.lean` is stated for `ClassicalSolutionR`; `A04/Gronwall.lean`, `A04/HighEnergy.lean`,
   `EnergyIdentityHigh.lean` may have the differential inequality at datum level; lane 169's derivative identity gives `d/dt` of the datum path).
   If the mild-level Grönwall is genuinely absent, isolate it as ONE named hypothesis `MildGronwall q` with the exact statement (differential
   inequality ⇒ bound, in the tree's language) and prove everything else; define `R q` explicitly from it.
3. Conclude `hb_of_base : ∀ q hq, HasAprioriBound hq hν a F hF (R q)` on `[0,S₆]` (and the `Inv` variant), with `R : ℕ → ℝ` explicit.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/AprioriFamily.lean` (namespace `NSFormalization.Section4.A01`): `hasAprioriBound_base`,
   the lowering/identification lemma at subwindow level, the `H²`-cap transfer, `hb_of_base` (conditional on `MildGronwall` if unavoidable), and the
   composition with lane 192's export once it lands (branch `erenup/192-A01-wiring-hsob`; if not importable, a probe with the copied statement).
2. Records `research/A01/ATTEMPTS_A3_M2.md` (what the vendor's local existence gives exactly: horizon formula, radius, continuation; negative examples),
   update `research/A01/A3_SPLIT.md` row A3-M2, conformance `research/A01/axioms_a3_m2.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.AprioriFamily` (silent), `lake env lean` on the module (0 output), the
axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands). Also write it
to `research/A01/REPORT_193.md`.
