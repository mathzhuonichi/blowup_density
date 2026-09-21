# Lane 203-A01-signed-limit — `CylinderSignedRootLimit`: pass the signed (dissipation-retaining) regularized energy inequality to the maximal-approximation limit

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/203-A01-signed-limit` (git branch `erenup/203-A01-signed-limit`, based on branch `erenup/201-A01-root-comparison`
= `origin/erenup/integration` + lane 201's `Section4/A01/RootComparison.lean` (`def CylinderSignedRootLimit … a ha F hF E A` — solenoidal version after its fix —
and the conditional exports `cylinderRootComparison_of_forcingBound`, `finiteMildEnergy_of_forcingBound`); lane 201 is landing, its def will not change).
On integration: lane 198 `MildEnergyPremises.lean` (`energy_maximal_limit` at `:137`, representative construction `:289-300`, `mild_energy_estimate_of_cylinder`,
`def ForcingFamilyBound`), lane 199 `MildEnergyEnvelope.lean` (`regularized_full_energy_hasDerivAt` at `:72` retaining the negative full gradient square,
`energyComparison`, `cylinderEnvelopeDriver`, `energyRootPath`), lane 196 `MildGronwall.lean`. Lane 200 (branch `erenup/200-A01-forcing-bound`, landing) supplies
`ForcingFamilyBound` under `CylinderCommutatorBound`; **take `hFB : ForcingFamilyBound hq hν a ha F hF E A` as a hypothesis** and, if you need the stronger
*regularized-family* forcing estimates (uniform in the approximation index `n`), state exactly what lane 200 must additionally export (see the route).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/REPORT_201.md`, `research/A01/REVIEW_201-A01-root-comparison.md` §3 (your route,
verbatim below), `research/A01/REPORT_199.md`, `research/A01/REPORT_198.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules;
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement (never a zero instance
  as certification of a general-data premise); never route through the all-order constructor.

## Route (reviewer 201, verbatim)
Reuse `energy_maximal_limit` (Premises:137) and the representative construction (:289–300); begin with `regularized_full_energy_hasDerivAt` (Envelope:72),
retaining the negative full gradient square. Supply the transport/pressure cancellations used in `vendor/…/Euler/MildMajorantEnergy.lean:95–119`. The vendor
limit route is `EulerPDEMajorantLimit.weighted_pde_majorized_subinterval_limit` (`Euler/PDEMajorantLimit.lean:21`), ultimately
`EulerTimeLpSubinterval.integral_energy_subinterval_limit` (`Euler/TimeLpSubinterval.lean:74`) — its statement has NO dissipation slot, so it cannot prove the
signed residual by replacing one argument. Reuse `regularizedValueFamily_tendsto` (`Euler/RegularizedEnergyFamily.lean:44`), `weightedMetricPath_tendsto`
(`Euler/MetricPathConvergence.lean:60`), `regularizedWeightedForcing_tendsto` (`Euler/RegularizedEnergyFamily.lean:89`) while adding a **signed passage
retaining the gradient-square integral**: prove its convergence from the strong `TimeLp` maximal limit through the derivative word maps (or lower
semicontinuity under weak convergence); handle the `ε`-regularized root denominator before `ε ↓ 0`. The limiting tame estimate `hFB` is not a bound on every
`n`-indexed regularized forcing family: pass to the signed limiting energy estimate first, then absorb using RootComparison:94 with a properly justified
regularized division, or supply uniform regularized bounds (coordinate with lane 200).

## Goal
`theorem cylinderSignedRootLimit_of_forcingBound (hFB : ForcingFamilyBound hq hν a ha F hF E A) [+ at most one further named input, exact] :
CylinderSignedRootLimit hq hν a ha F hF E A` — token-for-token lane 201's `def` — hence, composing with lane 201, `finiteMildEnergy_of_forcingBound'` with
only `hFB` (and, with lane 200, only `CylinderCommutatorBound`).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/SignedLimit.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_SIGNED_LIMIT.md` (negative examples), update `research/A01/A3_SPLIT.md` A3-M2 sub-row "envelope/limit", conformance
   `research/A01/axioms_signed_limit.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.SignedLimit` (silent), `lake env lean` on the module (0 output), the axioms file,
`make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands). Also write it to `research/A01/REPORT_203.md`.
