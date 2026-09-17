# Lane 291-SPEC-t15-draft-a — Section 3 node T15 "scaling at fixed viscosity" (`prop:scaling`): double-blind draft A of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/291-SPEC-t15-draft-a` (git branch `erenup/291-SPEC-t15-draft-a`, based on `origin/erenup/integration-section3`). One of two **independent, mutually
invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T15/` or `collaboration/briefs/` entries for other T15 lanes. T15 is the torus
counterpart of Section 4's I03 (registered contract `I03.scaling`, Euclidean scaling identities) composed with the placement/periodization of the
whole-space packet into the fundamental cube; T18 (`thm:insertion`) consumes it.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (representation decision
(b) and the T15 row), the paper `paper/sections/03-torus.tex:99-175` in full (`sec:packet` placement of the packet `(U,P,F)` in a coordinate ball,
the rescaled fields `eq:scaling` (`:110-120`: `U_ε(t,x) = ε^{-1} U((t-t_ε)/ε², (x-x₀)/ε)` and its pressure/force companions — read the exact display,
the time shift `t_ε`, the centre `x₀`, the support radius condition that makes the periodization a **single copy** per period cell), and Proposition
`prop:scaling` `:122-140` with its proof `:141-175`: the momentum equation at viscosity `ν`, zero initial data, unbounded speed at `T`, the spatially
constant pressure normalization, `eq:packetEscale` (`‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2} M`, `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2} D`), `eq:packetFscale`
(`‖F_ε‖_{L^q(0,∞;L^p)} = ε^{α(p,q)} ‖F‖…`, `α(p,q) = -3 + 3/p + 2/q`, `1 ≤ p,q ≤ ∞`), and `eq:packetHs` (`‖F_ε‖_{L¹(0,∞;H^s(T³))} ≤ C_s (ε^{1/2} + ε^{1/2-s})`
for `0 ≤ s ≤ 1`, via `lem:localization`). Then the reconciled Section 3 vocabulary these statements must be written in: `research/T10/Spec.lean`
(`IsPeriodicSpatial`, `IsPeriodicOn`, `torusLift`, `periodicSobolevENorm` — with lead amendment 1's integrability conjunct, `research/T10/RECONCILIATION.md`
§5 — `forceSobolevENormT`, `MemForceT`, `energyEssSupT`/`energyGradientT`/`energyENormT`, `PressureGaugeT`, `ClassicalSolutionT`), `research/T14/Spec.lean`
(the imported packet `PacketImportAPI`/`PacketImportFamily`: `M`, `D`, quiet interval, zero extension — reuse it, do not restate the packet), and
`research/T13/Spec.lean` (`LocalizationAPI`: the uniform localization estimate that `eq:packetHs` is derived from — cite the field, do not re-prove).
Registered Section 4 shapes to mirror: `verification/Contracts/V1/Scaling.lean` (find the file through `verification/contracts.json` entry `I03.scaling`;
read every field: how the ℝ³ version states the scaled fields, the mixed-norm identities, `α(p,q)`, and `IsPacketScaling`-type predicates) and
`Contracts/V1/Packet.lean` (`PacketAPI`). Also skim `formalization/NSFormalization/Paper1/PeriodicScalingBounds.lean`, `ScalingLimits.lean`,
`PeriodicPacketEndpointRates.lean` heads (`grep -nE "^(def|structure|theorem) "`) for implementation candidates to cite (not to import).

## Deliverables (statements only, no proofs)
1. `research/T15/DraftA.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T15/DraftA.lean`).
   Begin with the same imports as `research/T10/Spec.lean` (+ `Contracts.V1.Packet`, `Contracts.V1.Scaling` as needed) and copy **verbatim** (same names,
   namespace `BlowupDensity.T10.Draft` / `BlowupDensity.T14.Draft` / `BlowupDensity.T13.Draft`, marked `-- copied from research/T1x/Spec.lean:LINE; delete once
   registered`) only the declarations you use. Then, in a namespace `BlowupDensity.T15.DraftA`, state:
   (i) the placed-and-rescaled fields as explicit `def`s (`scaledVelocity ε`, `scaledPressure ε`, `scaledForce ε` on `SpaceTime`, from the packet's
   fields, with the exact exponents and shifts of `eq:scaling`), and the **single-copy periodization** into a unit-periodic field (say how: sum over the
   lattice of the compactly supported field, or the explicit cube representative — and which hypothesis (support radius vs `ε`) makes the two agree);
   (ii) `structure ScalingAPI` whose fields are exactly the clauses of `prop:scaling`: (a) the periodized fields solve the periodic momentum equation at
   viscosity `ν` on the stated time interval with zero initial data (as a `ClassicalSolutionT`-shaped statement or the pointwise PDE — say which and
   why); (b) unbounded speed at `T` (state the exact quantifier: `∀ K, ∃ t < T, ∃ x, ‖U_ε(t,x)‖ > K`, or the paper's formulation); (c) the spatially
   constant pressure normalization / gauge; (d) `eq:packetEscale` as two **equalities** in T10's energy vocabulary (`energyEssSupT`, `energyGradientT`)
   with `ε^{1/2} M`, `ε^{1/2} D` (`M`, `D` from the packet); (e) `eq:packetFscale` as an equality for all `1 ≤ p, q ≤ ∞` with `α(p,q)` explicit (mixed
   norm in the T10/Section 4 spelling — say which); (f) `eq:packetHs` for `0 ≤ s ≤ 1` with a constant `C_s` (Type-valued API with the constant as a data
   field, house style of A03/A05, or `∃ C` — say which and why; the paper fixes `C_s` before `ε`); (g) the "in particular" corollary (force → 0 in
   `L¹_t H^s_x` for `s < 1/2`) only if you render it as a separate derived statement, clearly marked. Every field: docstring citing `03-torus.tex:<line>`,
   exact quantifier order, a "non-vacuity" comment; **no junk-value traps** (every norm identity over a field carries the integrability/`MemLp`
   hypotheses that make the Bochner integrals honest, or is stated for smooth compactly supported fields where that is automatic — say which).
2. `research/T15/COMPARISON_A.md`: paper-clause → Lean field table (with the `I03.scaling` counterpart field for each); choices (periodization
   rendering, `ε` range, which norms are `ℝ≥0∞`); ambiguities; "needs a lemma" list; implementation candidates in `Paper1/`.
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T15/REPORT_291.md`.
