# Lane 288-SPEC-t11-draft-a — Section 3 node T11 "periodic local theory and continuation" (`prop:local` on T³): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/288-SPEC-t11-draft-a` (git branch `erenup/288-SPEC-t11-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually
invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T11/` or `collaboration/briefs/` entries for other T11 lanes. T11 is the periodic
counterpart of Section 4's A01 (local theory) + A02/A04 (continuation): it is on the critical path (T10 → T11 → T18 → T19 → T21 and T20).

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines; the "结构体例外" paragraph), `collaboration/SECTION3_PLAN.md` §1–§3
(representation decision (b) and the T11 row), the **reconciled T10 vocabulary** `research/T10/Spec.lean` (binding: `IsPeriodicSpatial`, `IsPeriodicOn`,
`torusLift`, `PeriodicSobolev`, `IsPeriodicDatum` — with the `Integrable` conjunct of lead amendment 1, `research/T10/RECONCILIATION.md` §5 —
`periodicSobolevENorm`, `IsPeriodicSobolevPath`, `forceSobolevENormT`, `initialClassT`, `MemForceT`/`forceClassT`, `pressureMeanT`, `PressureGaugeT`,
`normalizePressureT`, `ClassicalSolutionT` (read every field), `maximalLifespanT`, `RegularThroughT`, `breakdownSetT`, `energyENormT`), the paper:
`paper/sections/02-preliminaries.tex:95-120` (Proposition `prop:local`, stated for the domain `D ∈ {ℝ³, T³}`: unique maximal smooth velocity with
pressure determined as above; the continuation criterion `eq:criterion` `∫₀^S ‖u(t)‖²_{H²(D)} dt < ∞ ⇒` extends beyond `S`), the surrounding
conventions on viscosity/pressure/mean (`02-preliminaries.tex:60-105`: read the whole preliminaries on the torus classes `X_T`, `F_T`, the pressure
normalization `∫ p = 0`, and the mean), and `paper/sections/appendix-a-local-theory.tex` in full (derivation of `prop:local` from the classical forced
local theory: one common existence interval for all Sobolev orders, the continuation criterion, the viscosity rescaling, and the **periodic mean
reduction** — the Galilean change of variables removing the mean of the velocity; identify the exact lines and the exact statements the appendix
proves for the torus). Then the registered Section 4 shapes T11 must mirror: `verification/Contracts/V2/LocalTheory.lean` (`ManuscriptLocalRegularity`,
`LocalTheoryAPI`: `horizon`, `solution`, `regularity`, `horizon_lower_bound`), `verification/Contracts/V2/Continuation.lean` (`ContinuationV2API`:
`restart`, `higherOrderBound`, `restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite`), and the V1 files they extend (find them via
`verification/contracts.json` entries `A01.*`, `A02.*`, `A04.*`; read the field statements, `grep -nE "^  [a-zA-Z_]+ :"` with context). Also skim the
local periodic layer heads for names to cite as "existing implementation candidates" (not to import): `formalization/NSFormalization/Paper1/PeriodicOrdinaryLocal.lean`,
`PeriodicInitialData.lean`, `PeriodicLifespan*.lean` if present (`ls formalization/NSFormalization/Paper1/ | grep -i lifespan`), `PeriodicMeanReduction*`/`Galilean*` if present.

## Deliverables (statements only, no proofs)
1. `research/T11/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T11/DraftA.lean`).
   Because `research/` is not an import root, begin with the same imports as `research/T10/Spec.lean` and copy **verbatim** (same names, same namespace
   `BlowupDensity.T10.Draft`, marked `-- copied from research/T10/Spec.lean:LINE; delete once T01.torus_data is registered`) only the T10 declarations you
   use. Then, in a namespace `BlowupDensity.T11.DraftA`, state:
   (i) `structure PeriodicLocalRegularity` (the torus analogue of `ManuscriptLocalRegularity`: which clauses of `prop:local`/Appendix A hold for the
   solution on `[0,T)` — smoothness into every `H^m` (via `IsPeriodicSobolevPath`/`periodicSobolevENorm`), pressure determined by the periodic Leray/
   `∫p = 0` gauge, periodicity in space, etc.);
   (ii) `structure PeriodicLocalTheoryAPI` with the existence/uniqueness/maximal-lifespan clauses of `prop:local` exactly as stated (quantifier order:
   `∀ ν > 0, ∀ a ∈ initialClassT, ∀ f ∈ forceClassT, …`; uniqueness as equality of velocities on the common interval; the maximal solution as an
   object on `[0, maximalLifespanT ν a f)` or a horizon function — say which and why; **one common existence interval for all Sobolev orders**);
   (iii) `structure PeriodicContinuationAPI` with `eq:criterion` exactly: `∫₀^S ‖u(t)‖²_{H²(T³)} dt < ∞` (as a Bochner or `lintegral` of
   `periodicSobolevENorm 2` — say which and why; `S < ∞`) ⇒ the solution extends beyond `S` (state "extends" concretely: a `ClassicalSolutionT` on a
   strictly larger horizon agreeing on `[0,S)`), plus the restart/higher-order-bound clauses Appendix A actually proves for the torus (mirror A04 V2's
   shapes only where the paper's appendix supports them; do not invent);
   (iv) the **mean reduction**: the Galilean transform `v(t,x) := u(t, x + ∫₀ᵗ m) − m(t)` with `m(t) := meanT (u(t,·))` and the exact statement the appendix
   proves (the transformed field solves the mean-free equation with the transformed force; the mean evolves by `m' = meanT (f(t))`), as a `structure`
   or `def`s + `Prop` fields with the exact quantifier order — this is what T20 consumes;
   (v) the viscosity rescaling clause if the appendix states one for the torus.
   Every field: docstring citing `02-preliminaries.tex:<line>` / `appendix-a-local-theory.tex:<line>`, exact quantifier order, a "non-vacuity" comment.
   Local verbatim definitions flagged "needs registration" for anything absent from T10.
2. `research/T11/COMPARISON_A.md`: paper-clause → Lean field table (with the Section 4 counterpart field for each: `A01.*`/`A02.*`/`A04.*` names);
   choices (how "maximal" and "extends beyond" are rendered; `ℝ≥0∞` vs real lifespans; how the mean reduction is packaged); ambiguities; "needs a lemma"
   list; which existing `Paper1/Periodic*` declarations look like implementation candidates.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T11/REPORT_288.md`.
