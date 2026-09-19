# T21 proof-lane split — cor:nondensity + thm:main

Status: incremental skeleton, 2026-09-19; source verification and detailed routes follow in section commits.
Target: `research/T21/Spec.lean`; approved design: `research/T21/RECONCILIATION.md` §0.
Twin: Section4/R41. House style: T18/T20 splits.
Size legend: S = bookkeeping; M = bounded analytic work. Model legend: **codex-sol = bookkeeping/transport, codex-astra = analytic core/planning**.

## 0. Ground rules

Planning only; no Lean edits or placeholder fields. Peel oversized analytic work into helper units before assembly. T21 has no named inputs: consume threaded CriticalRegularityTAPI / PeriodicDensityAPI and registered vocabulary. Never push, merge, or rebase.

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
