# Lane 322-T11-U12-high-order — T11 U12 — `higherOrderBound` (periodic `eq:Rhigh` + Grönwall), first sub-lane

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/322-T11-U12-high-order` (git branch `erenup/322-T11-U12-high-order`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses,PhysicalRecovery,Rescaling,Uniqueness,MeanIdentity}.lean` (T11 wave 1–2 results; `LocalExistence.lean` defines the named existence input `PeriodicQuantitativeLocalInput'` — `research/T11/LEAD_AMENDMENTS.md` amendment 1), `Section3/T10/{FourierCalculus,ForcePaths}.lean` (ForcePaths only if lane 312 has landed — check `ls`), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/high_order_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U12** of `T11_SPLIT.md` §1 (`appendix-a-local-theory.tex:127-147` eq:Rhigh; mirror of Section 4 A04's `energyIdentityHigh → higherOrderBound` chain: read `research/A04/G1_SPLIT.md` SL0–SL8 and
`verification/Contracts/V2/Continuation.lean:140` `higherOrderBound` for the exact shape). Target: the `higherOrderBound` field of `PeriodicContinuationAPI` verbatim from `research/T11/probes/api_on_canonical.lean`
(read its exact statement: the `H^m` norm of a `ClassicalSolutionT` on `[0,S]` is bounded by the datum/force norms times `exp(C ∫₀^S ‖u‖²_{H²})`, or as the reconciliation spells it). Route on the
coefficient carrier: (1) the `H^m` energy identity — pair the momentum equation against `u` at order `m` (`d/dt ‖u‖²_{H^m} = −2ν‖∇u‖²_{H^m} − 2⟨(u·∇)u, u⟩_{H^m} + 2⟨f, u⟩_{H^m}`; the pressure term drops by Leray
self-adjointness / solenoidality — `Section3/T10/Leray.lean`); (2) the nonlinear term bound `|⟨(u·∇)u,u⟩_{H^m}| ≤ C_m ‖u‖_{H²} ‖u‖²_{H^m}` (tame product `Section3/T12`'s `tameProduct` field is **not yet proved**
— if you need it, take the torus tame product in the exact T12 field shape as your **single named input**, `def TorusTameProductInput : Prop := …` copied from `research/T12/probes/api_on_canonical.lean`'s
`tameProduct`/`boundedRepresentative` fields with explicit constants); (3) force term by Cauchy–Schwarz; (4) Grönwall (`Mathlib`'s `norm_le_gronwallBound_of_norm_deriv_right_le` or the ODE comparison used
in `Section4/A01/GronwallInstance.lean` — grep and reuse its shape). Deliver at least (1)+(3)+(4) fully and (2) conditionally on the single named input; if (1) itself needs the time-differentiability of
`t ↦ ‖G t‖²` for the datum path (`ClassicalSolutionT.sobolev`'s continuous path — check whether differentiability is available or must be derived from the momentum equation via `FourierCalculus`), state which
and prove it or fold it into the same single input — never two inputs. (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/HighOrder.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_high_order.lean`.
2. Records `research/T11/ATTEMPTS_HIGH_ORDER.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_322.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.HighOrder` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[322-T11] HighOrder`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
