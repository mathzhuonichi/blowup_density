# Section 3 — owner decisions pending (lead summary, 2026-09-19 17:35Z)

Status: 54 registered contracts (55 once lane 487 registers `T04.boundary_insertion`); every Section 3 node T10–T24 has proofs; `thm:main` is registered as `T03.main` (#439). All work is on `erenup/integration-section3`, tracked by draft PR #270. Nothing below blocks proofs; each item blocks only a V1 wording or a registration scope.

| # | Node | Decision needed | Where recorded | Lead's interim ruling |
|---|---|---|---|---|
| 1 | T17 | `correctionStatement` V1 wording: the registered statement is the **amended** G4 block (T16 hypothesis block + `0<ν` + global smoothness + chart inclusion + raw packet support); the unamended Spec text is unprovable | `research/T17/SPEC_ISSUES.md` G4 | registered `correctionStatementAmended`; V1 docstring says so |
| 2 | T17 | G5: the registered block demands global `ContDiff ℝ ∞ v` + `IsPeriodicOn univ v`, which a classical reference lacks; canonical slab bridge `correctionStatementSlab'` (#423) + T19 zero-extended reference close the gap without a contract change | `research/T17/SPEC_ISSUES.md` G5 | no contract change; owner may prefer a V2 with the slab hypotheses |
| 3 | T23 | G0: `boundaryInsertionStatement` quantifies an arbitrary `D : CutoffData` and is false at `D.ε₀ = 0` (kernel-checked); registration uses the **existential** repair `boundaryInsertionStatement'` | `research/T23/SPEC_ISSUES.md` G0 (+ lane 477 addendum) | register the repaired statement; V1 wording amendment owner-pending |
| 4 | T23 | G1: no-slip uniqueness on smooth-level domains needs a boundary integration-by-parts theorem Mathlib lacks; box domains are proved unconditionally, smooth domains conditional on the explicit `IBP Ω` | `research/T23/SPEC_ISSUES.md` G1 | V1 registers box domains unconditionally + the conditional smooth theorem |
| 5 | T23 | Domain record placement (`ClassicalSolutionOmega` canonical module vs contract), smooth-domain encoding (regular-level + boxes), pressure gauge/scope | `research/T23/T23_SPLIT.md` §4 | canonical in `Section3/T23/DomainSolution.lean`, fieldwise conversions in the binding |
| 6 | T19/T21/T24 | `Prop` vs `Type` convention for the density / main / multiple-regions records | `research/T21/RECONCILIATION.md`, `research/T24/RECONCILIATION.md` | as reconciled (T19/T21 `Prop`, T24b `Type`) |
| 7 | T22 | `Section3/T22/Assembly.lean:24 boundedDomainNorm` is a `Prop`-valued `def` (linter warning, the only Section 3 warning) | `logs/SECTION3_BUILD_20260919h.md` | small MAINT: `theorem` or `set_option linter.defProp false` |
| 8 | repo | Retarget PR #270 to `main` once #259 (Section 4) is merged; A01/A04 V2 wording, `L¹L²` norm spellings, H¹ gap (Section 4 list) | `NEXT_SESSION.md` | unchanged |
