# Lane 303-SPEC-t20-draft-a — Section 3 node T20 "global regularity for small critical force" (`prop:critical`): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/303-SPEC-t20-draft-a` (git branch `erenup/303-SPEC-t20-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually
invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T20/` or `collaboration/briefs/` entries for other T20 lanes. T20 is the torus counterpart of Section 4's
R43 (registered `R43.critical_regularity`) combined with C01 (energy absorption) and A04 (continuation); it is the obstruction mainline (T12 → T20 → T21).

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (representation decision (b) and the T20 row), the paper
`paper/sections/03-torus.tex:370-505` in full — `sec:critical`, Proposition `prop:critical` `:383-391` (`eq:smallcritical` `:385-387`: the smallness of `‖g‖_{L¹(0,∞;Ḣ^{1/2})}` relative to `cν`
and the conclusion: the maximal solution from `prop:local` is global) and its proof `:392-505`: the mean reduction (`m' = ḡ`, `eq:meanbound` `:404-406`, `eq:meanfree` `:408-410`; skew-adjointness
of the constant transport `(m·∇)v` in `L²` and its commutation with the Fourier multipliers), `eq:criticalenergy` `:438-440`, `eq:bintegral` `:442-444`, the bootstrap `eq:ybound` `:454-456`,
`eq:H1energy` `:482-484`, and the continuation via `eq:criterion` `:500-503`. Read the exact displays, constants (`c`, the absolute constants from the T12 embeddings), quantifier order, and
which estimates are stated for the mean-free field `v = u − m`. Then the reconciled Section 3 vocabulary these statements must be written in: the registered `T01.torus_data`
(`verification/Contracts/V1/TorusData.lean` — import it and use its names: `IsPeriodicDatum` with the integrability conjunct, `periodicSobolevENorm`, `periodicHomogeneousENorm`, `meanT`,
`meanZeroPartT`, `IsMeanZeroT`, …), `research/T10/Spec.lean` (solution-class part: `forceSobolevENormT`, `MemForceT`, `ClassicalSolutionT`, `maximalLifespanT`, `RegularThroughT`, energy
norms), `research/T11/Spec.lean` (**binding**: `PeriodicLocalTheoryAPI`, `PeriodicContinuationAPI` (`SolvesBelowT`, `ExtendsBeyondT`, `lifespanInfiniteOfLocallyFinite`, the criterion as
`squaredHTwoIntegral`-shaped `lintegral`), `PeriodicMeanReductionAPI` (the data-defined Galilean mean `galileanMeanT`; note the reconciliation's §3 remark that T20 uses the **untranslated**
reduction `v = u − m`, `h = g − ḡ`, keeping the constant transport `(m·∇)v` in `eq:meanfree`)), `research/T12/Spec.lean` (`MeanZeroSobolevCalculusAPI`: `velocityCriticalL3`,
`gradientLambdaCriticalL3`, `gradientLSix`, `hTwo_le_laplacian`, `spectralGap`, `lambda_exists`, `IsPeriodicLambda`). Registered Section 4 shapes to mirror: `verification/Contracts/V1/CriticalRegularity.lean`
(find via `verification/contracts.json` entry `R43.critical_regularity`; read every field: how the ℝ³ version states smallness, the energy quantities `y`, `z`, the bootstrap, the conclusion),
`Contracts/V4/EnergyAbsorption.lean` (C01), `Contracts/V2/Continuation.lean` (A04). Also skim `formalization/NSFormalization/Paper1/PeriodicCriticalRegularity.lean`, `CriticalEnergy*.lean`,
`PeriodicMeanZeroEstimate.lean` heads (`grep -nE "^(def|structure|theorem) "`) for implementation candidates to cite (not to import).

## Deliverables (statements only, no proofs)
1. `research/T20/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T20/DraftA.lean`). Import `Contracts.V1.TorusData`
   (+ `Contracts.V1.Data`, the R43/C01/A04 contract files if cited) and copy **verbatim** (T13 copy policy: same names, namespaces `BlowupDensity.T10.Draft` / `BlowupDensity.T11.Draft` /
   `BlowupDensity.T12.Draft`, marker comments with source lines) only the still-unregistered declarations you use. Then, in a namespace `BlowupDensity.T20.DraftA`, state:
   (i) the mean-free reduction objects (`meanPathT`, `meanFreeVelocity`, `meanFreeForce`, the constant-transport term) as explicit `def`s; (ii) the energy quantities of the proof
   (`y(t) = ‖v‖²_{Ḣ^{1/2}}`-type, `z`, the `B`-integral of `eq:bintegral`) as `def`s in T10/T12 vocabulary; (iii) `structure CriticalRegularityT…API` (Type-valued with the constants as data
   fields — house style of A03/A05/R43 — or `Prop`; say which and why) whose fields are exactly the clauses of `prop:critical` and the displayed estimates of its proof that the paper states
   as standalone facts (`eq:meanbound`, `eq:meanfree` as an equation satisfied by `v`, `eq:criticalenergy`, `eq:bintegral`, `eq:ybound`, `eq:H1energy`), with the **main statement**
   (`eq:smallcritical` ⇒ `maximalLifespanT ν a g = ⊤`, or the paper's exact phrasing) as one field; every field: docstring citing `03-torus.tex:<line>`, exact quantifier order,
   "non-vacuity" comment, **no junk-value traps** (every norm carries the integrability/class hypotheses; the smallness constant `c` is a data field or explicit; `ν > 0`; the force in
   `forceClassT`; the datum in `initialClassT`).
2. `research/T20/COMPARISON_A.md`: paper-clause → Lean field table (with the `R43.*`/`C01.*`/`A04.*` counterpart field for each); choices; ambiguities; "needs a lemma" list;
   implementation candidates in `Paper1/`.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T20/REPORT_303.md`.
