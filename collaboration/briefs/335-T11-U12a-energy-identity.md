# Lane 335-T11-U12a-energy-identity — T11 U12a — the `H^m` energy identity of a classical periodic solution (time differentiability of the coefficient path + the datum-form momentum equation)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/335-T11-U12a-energy-identity` (git branch `erenup/335-T11-U12a-energy-identity`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/*.lean` (all T11 modules landed so far, in particular `HighOrder.lean` (lane 322: `higherOrderBound_of_energyInequality` and its exact hypothesis `hRhigh` — read `research/T11/REPORT_322.md` and `ATTEMPTS_HIGH_ORDER.md` §3 first), `MildMomentum.lean` (lane 327: Duhamel time differentiation of the coefficient paths, the coefficient form of the momentum equation, `convectionDivergenceT_coeff`), `MildPressure.lean` (periodic convolution theorem), `ConvolutionBoundReal.lean` (real-order convolution bound), `FlowConversion.lean`, `Persistence.lean`), `Section3/T10/{FourierCalculus,ForcePaths,Leray}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/energy_identity_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U12a** of U12 (`research/T11/ATTEMPTS_HIGH_ORDER.md` §3, fact (a)): for `w : ClassicalSolutionT ν a f T` (a genuine classical solution: `velocity_smooth` jointly `C^∞`, `momentum`, `divergence`,
`sobolev` continuous datum paths at every order — read `Section3/T10/PeriodicData.lean`), prove for every `m ≥ 3` (or every `m : ℕ`) and `t ∈ Ioo 0 T`: the coefficient path `t ↦ û(t)` (the datum of
the slice, at order `m`) is differentiable at `t` with derivative the coefficient form of the momentum equation, `d/dt û(t)(k) = −ν4π²|k|² û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)` — from the joint
smoothness of `w.velocity` by differentiating the Fourier coefficient integral under the integral sign (`FourierCalculus.lean` symbols, `MildMomentum.convectionDivergenceT_coeff` for the convection
coefficient, `Leray.lean` for `P̂`; the pressure gradient is the Leray complement by `pressure_gradient`/`momentum`) — and hence the **`H^m` energy identity**: `t ↦ torusSobolevNormAt m w.velocity t ^ 2`
(lane 322's spelling) is differentiable on `Ioo 0 T` with derivative `−2ν‖∇u‖²_{H^m} − 2⟨(u·∇)u, u⟩_{H^m} + 2⟨f, u⟩_{H^m}` (the pressure term vanishes — lane 322 already proved the coefficient-side
pressure drop; the Laplacian pairing value is also there). Deliver the identity in exactly the form lane 322's `hRhigh` consumes for its `HasDerivAt … d t` component (read the binder), so that with
U12b's pairing bound `hRhigh` follows; state `energyIdentity_of_classical` and a corollary `hRhigh_of_pairingBound` that takes the U12b estimate as an explicit hypothesis (not a `def … : Prop`) and
produces `hRhigh`. **No named input**; honest partial with the exact obstacle if stuck. (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/EnergyIdentity.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_energy_identity.lean`.
2. Records `research/T11/ATTEMPTS_ENERGY_IDENTITY.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_335.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.EnergyIdentity` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[335-T11] EnergyIdentity`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
