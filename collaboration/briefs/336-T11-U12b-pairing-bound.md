# Lane 336-T11-U12b-pairing-bound — T11 U12b — the nonlinear pairing bound `|⟨(u·∇)u, u⟩_{H^m}| ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m}` on the torus

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/336-T11-U12b-pairing-bound` (git branch `erenup/336-T11-U12b-pairing-bound`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/pairing_bound_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Sub-unit **U12b** of U12 (`research/T11/ATTEMPTS_HIGH_ORDER.md` §3, fact (b)): the tame estimate at the pairing level, on the coefficient carrier, for smooth periodic divergence-free `u` (or directly for
the data `A ∈ PeriodicSobolev m` with the convection given by `ConvolutionBoundReal.lean`'s `torusConvolutionCLM_real`): `|⟨Q(A,A), A⟩_{H^m}| ≤ Chigh m · ‖A‖_{H²} · ‖A‖_{H^m} · ‖A‖_{H^{m+1}}`-type (exactly the
shape lane 322's `hRhigh` needs: `Chigh m * ‖u(t)‖_{H²} * ‖u(t)‖_{H^m} * g` with `g` the gradient/`H^{m+1}` quantity — read the binder and match it), with an explicit `Chigh m`. Route: the standard
commutator/tame argument on Fourier side — split the convolution sum by `|l| ≤ |k−l|` vs `>`; in each half bound the weight `W(k)^{m/2}` by `2^{m/2}(W(l)^{m/2} + W(k−l)^{m/2})` (Peetre, in
`ConvolutionBoundReal.lean`), so one factor carries the full `H^m` weight and the other the `H²` (≥ `H^{3/2+}`) weight with the summable tail `∑ W^{-2}`; the derivative symbol `2πi k_j` is absorbed as
`‖∇u‖_{H^m}`; the divergence-free cancellation `⟨(u·∇)v, v⟩_{L²} = 0` is not needed for this bound (only for the `m = 0` energy), so do not rely on it. Alternatively (if cheaper) derive it from
T12's `tameProduct` field shape if lane 300+'s modules provide the scalar tame product — check `Section3/T12/`; if `tameProduct` is not yet proved there, do not assume it. **No named input**; honest partial
with the exact obstacle if stuck. (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/PairingBound.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_pairing_bound.lean`.
2. Records `research/T11/ATTEMPTS_PAIRING_BOUND.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_336.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PairingBound` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[336-T11] PairingBound`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
