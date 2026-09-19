# T21 proof-lane split — cor:nondensity + thm:main

Lead-facing, 2026-09-19. Target: nine-field `NonDensityAPI` and five-field `MainTheoremAPI`, their paper-order statements and assembly signatures.
Target: `research/T21/Spec.lean`; approved design: `research/T21/RECONCILIATION.md` §0.
Twin: Section4/R41. House style: T18/T20 splits.
Size legend: **S** ≤ approximately 100 lines; **M** one bounded lemma with a known route; **L** a multi-file campaign, which must be peeled before assignment. Model legend: **codex-sol = bookkeeping/transport, codex-astra = analytic core/planning**.

## 0. Ground rules

**Peeling rule.** Every N-unit ends in a theorem with the verbatim field type below, or a helper directly consumed by that field. If an M unit grows into a multi-file campaign, stop and split its exact residual into smaller helper theorems; do not introduce a named input, placeholder field, extra axiom, or stronger hypothesis to conceal it. T21 has **no named inputs**: everything is threaded from `CriticalRegularityTAPI` / `PeriodicDensityAPI`, proved by the units below, or registered.

**Threaded versus inhabited.** A theorem taking `K : CriticalRegularityTAPI` may be proved before a closed K exists. The analogous rule applies to T19 density. These parameterized theorems can start now; unconditional statements and registration wait for the actual suppliers. T20's canonical record is `Section3/T20/CriticalRegularity.lean:139`, with `c:145`, `hc:150`, `globalRegularity:365`. The consumed T19 record is `research/T19/Spec.lean:192`, copied in T21 `Spec.lean:115`; its `fixedInitialDensity` is at T19 `:207` / T21 `:130`. Do not import either blind draft or make another copy of T20/T12. T19's copied declaration is an interim Spec arrangement, not a second production record.

**Layering.** Analytic helpers belong under canonical `Section3/T21/` and use canonical T10 vocabulary. Verbatim registered-field probes and the lifespan conversion belong under `verification/` (temporary probes may live under `research/T21/probes/`). Do not import Contracts or Bindings into formalization. The final contract uses registered vocabulary and imports only permitted contract dependencies. Registered `forceClassT` / `forceSobolevENormT` have definitional bridges (`Bindings/TorusLocalTheory.lean:57,67`); lifespan needs the propositional bridge (`:270`). The explicit checked seam is T21 `Spec.lean:637-643`. Proposed module names below are destinations, not claims that those modules exist.

**Scope.** Preserve all nine `NonDensityAPI` fields (`Spec.lean:269-431`) and all five `MainTheoremAPI` fields (`:467-559`), both Prop-valued under lead approval (`RECONCILIATION.md` §0). The paper fixes q = 1, the threshold 1/2, positive viscosity/horizon, and the zero-datum converse (`paper/sections/03-torus.tex:6-16,506-525`, read with sed). Keep unrestricted real orders in monotonicity and the biconditional, including negative subcritical orders. No Section 4 q = 2 branch or regular-reference rider; compare `Contracts/V1/MainThresholds.lean:23,40,54,79`.

**Execution.** Work only in the lane worktree; no push, merge, or rebase. This delivery edits Markdown only. Future proof workers source `. scripts/lean-env.sh`, run lake only from `verification/` with `LEAN_NUM_THREADS=6`, provide exact-field probes and standard-axiom audits, and run required gates. Commit incremental sections. Registration/registry changes are confined to final assembly.

**Citation convention.** `Spec.lean` without a prefix means `research/T21/Spec.lean`; `Section3/`, `Section4/`, `Paper1/` mean `formalization/NSFormalization/`; `Contracts/`, `Bindings/`, `Tests/` mean `verification/`. Source observations below are from this checkout; lane progress supplied by the task brief is a scheduling snapshot, not a claim of a new local implementation.

## 1. Units and lanes

- **N0 — T20 bridge**: hc and criticalGlobalRegularity from a threaded T20 record.
- **N1 — datum order lowering**: contractive Fourier reweighting helper.
- **N2 — slice monotonicity**: sliceSobolevMonotone from N1.
- **N3 — force monotonicity**: forceSobolevMonotone via a continuous linear contraction.
- **N4 — zero force membership**: zero belongs to forceClassT.
- **N5 — zero force norm**: registered force norm vanishes at zero.
- **N6 — triangle inequality**: reusable force norm triangle for ballRelativelyOpen.
- **N7 — ball bookkeeping**: ballNonempty and ballRelativelyOpen.
- **N8 — critical disjointness**: criticalBallDisjoint using N0.
- **N9 — higher-order disjointness**: ballDisjoint using N3 and N8.
- **N10 — non-density**: nonDensity by the positive-radius density definition.
- **N11 — threshold**: thresholdValue from T19 bookkeeping.
- **N12 — zero datum**: zeroInitialClass.
- **N13 — fixed datum density**: fixedInitialDensity from threaded T19.
- **N14 — biconditional**: zeroInitialDensityIff from density and non-density.
- **N15 — explicit negative half**: zeroInitialNonDensity from nonDensity.
- **A — final assembly and registration**: three assembly signatures, statements, contracts/bindings/tests, gated on T19/T20 registration.

Lane bundles (provisional): N4+N5+N12; N1+N2; N3; N6; N7+N10; N0+N8+N9; N11+N13+N14+N15; A.

## 2. Dependency ledger

Pending source-verified field-level ledger. Separate proofs with threaded records from closed registered witnesses.

## 3. Waves

At most three concurrent lanes. Start independent helpers and parameterized assembly before upstream registration; closed assembly waits for suppliers.

## 4. Risks

Resolve Prop-versus-Type with owner; preserve registration order T19 → T20 → T21 and the lifespan bridge in Bindings. N6 is a real analytic obligation, shared with T18 U11 lane 445. Verify lane 428 critLower before assigning N3.
