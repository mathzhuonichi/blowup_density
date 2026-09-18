# Lane 395-T24-Uc2-potential-pairing — T24 Uc2: `potential_pairing` of `ConservativeForcingAPI` (the Haar pairing of a periodic gradient with a divergence-free periodic field vanishes)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/395-T24-Uc2-potential-pairing` (git branch `erenup/395-T24-Uc2-potential-pairing`, based on `origin/erenup/integration-section3`;
lane 392 (T24 Uc1 + Ua1, codex, in progress in its own worktree) is creating `Section3/T24/Conservative.lean` with the T24c vocabulary `PeriodicPotentialT`/`conservativeForceT` —
if it has not landed on your base, restate those two definitions verbatim from `research/T24/Spec.lean:1367-1372` in your module under the same names and namespace, and note it;
the assembly lane will dedupe). Read `CLAUDE.md`, **`research/T24/T24_SPLIT.md` §0 and unit Uc2 (target verbatim `Spec.lean:1391-1406`, route)**, `research/T24/RECONCILIATION.md` §4 ⑨/⑩,
`formalization/NSFormalization/Paper1/ConservativeForce.lean` (`zero_of_conservative_residual :23` — the internal pairing scaffold), `Paper1/TorusCube.lean` (`integral_torusLift :40`),
the T10 canonical modules (`Section3/T10/PhysicalBridge.lean`: `torusLift`, `periodicTorusMeasure`, integrability of smooth periodic lifts; `IsPeriodicOn`), `Section3/T11/LocalTheory.lean`
(`ClassicalSolutionT` fields: `initial`, `divergence`, `velocity_periodic`, `velocity_smooth`), `Section3/T20/…` if lane 390's `constantTransportSkew` (torus integration by parts) has
landed on your base (grep `Section3/T20/ConstantTransport.lean`; reuse its IBP lemmas if present), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T24/PotentialPairing.lean` (namespace `NSFormalization.Section3.T24`): `theorem potential_pairing` verbatim (`Spec.lean:1391-1406`):
for `0 < ν`, `0 < T`, `φ` with `PeriodicPotentialT φ`, `S : ClassicalSolutionT ν 0 (conservativeForceT φ) T`, every `t ∈ Ico 0 T`: `∫ torusLift (fun x => ⟪−∇φ (t,x), S.velocity (t,x)⟫) ∂periodicTorusMeasure = 0`
(match the exact spelling). Route: at `t = 0` from `S.initial` (`u = 0`); at `t ∈ Ioo 0 T` torus integration by parts: `∫ ∇φ · u = −∫ φ (div u) = 0` via `S.divergence`, periodicity
(`S.velocity_periodic`, `φ`'s clauses), Haar integrability of smooth periodic lifts, `integral_torusLift` (torus integral = cube integral) and the cube IBP with periodic boundary terms
cancelling (the `zero_of_conservative_residual` scaffold, or lane 390's `constantTransportSkew`-style lemma if present).

## Deliverables
1. `Section3/T24/PotentialPairing.lean`; 2. probe `research/T24/probes/potential_pairing_closes.lean` (the Spec's field closed by `exact` through the canonical spelling; non-vacuity
with a nonzero periodic potential `φ = cos(2πx₁)` and the zero solution); 3. `research/T24/ATTEMPTS_UC2.md`, `research/T24/axioms_uc2.lean`, status in `research/T24/T24_SPLIT.md` Uc2,
report `research/T24/REPORT_395.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.PotentialPairing` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
