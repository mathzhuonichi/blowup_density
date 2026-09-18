# Lane 416-SPEC-t21-reconcile — T21 reconciliation of the two double-blind drafts (thm:main + cor:nondensity) → `research/T21/RECONCILIATION.md` + reconciled `research/T21/Spec.lean`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/416-SPEC-t21-reconcile` (git branch `erenup/416-SPEC-t21-reconcile`, based on `origin/erenup/integration-section3`, which contains both
drafts: `research/T21/DraftA.lean` + `COMPARISON_A.md` + `REPORT_410.md` (codex) and `research/T21/DraftB.lean` + `COMPARISON_B.md` + `REPORT_411.md` (Opus)). Read `CLAUDE.md`
(rule 2: statement fidelity; no placeholder fields; standard axioms), the two drafts and comparisons in full, the paper `paper/sections/03-torus.tex:1-16` (`thm:main`), `:506-525`
(`cor:nondensity` and its proof), `:349-382` (`prop:density`), `:383-505` (`prop:critical`), the previous reconciliations as templates — `research/T19/RECONCILIATION.md`,
`research/T18/RECONCILIATION.md`, `research/T23/RECONCILIATION.md` (structure: §0 lead review placeholder, §1 clause-by-clause table A vs B vs decision with paper line, §2 base
choice and threading, §3 ambiguities/owner questions, §4 the reconciled Lean file) — and `research/T19/Spec.lean` / `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean`
(the consumed canonical structures).

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/`.
- Statements only, no proofs. No `True`/tautological/argument-ignoring fields, no `sorry`/`axiom`. The reconciled file must elaborate with 0 errors.
- The reconciliation is a **decision document**: for every clause of `thm:main` (i), (ii) both directions, and `cor:nondensity`, record A's field, B's field, the paper text, and the
  decision (take A / take B / merge / drop as tautology, with one-line reason). Where A and B disagree on *mathematics* (quantifier order, topology, norm spelling, which structure
  carries `c`), decide by the paper text and by consistency with the registered `Contracts/V1/TorusLocalTheory.lean` (`RelativelyDenseT`, `forceClassT`, `forceSobolevENormT`) and
  with the Section 4 counterpart `Contracts/V1/MainThresholds.lean` (`R41`), and say so. Known findings to settle explicitly: (a) B's observation that the canonical
  `maximalLifespanT` is not defeq to the registered one (structure exception) — the reconciled spec must consume `prop:critical` through a form that the T20 canonical module can
  actually discharge via `Bindings.TorusLocalTheory` (say how); (b) `Prop` vs `Type` for the two structures (T19 precedent: `Prop`; R41 precedent: `Type`) — pick one and justify;
  (c) the "dense subset cannot miss a nonempty open set" clause — B dropped it as a tautology of `RelativelyDenseT`; confirm or keep as an explicit field; (d) the monotonicity
  `‖g‖_{L¹H^{1/2}} ≤ ‖g‖_{L¹H^s}` for `s ≥ 1/2` — as a field of `NonDensityAPI` (both drafts?) or as a lemma the proof supplies.

## Deliverables
1. `research/T21/RECONCILIATION.md` with §0 `## 0. Lead review` (leave a placeholder line "pending lead approval"), §1 the clause table, §2 base/threading decision, §3 ambiguities
   and owner questions, §4 the list of proof units the reconciled statement will need (the "needs a lemma" union of both comparisons, deduplicated, each tagged with the
   T19/T20/T11 field or the Paper1 module that supplies it: `Paper1/PeriodicCriticalRegularity.lean`, `PeriodicMain.lean` per B's report).
2. `research/T21/Spec.lean` — the reconciled statements in namespace `BlowupDensity.T21` (structures `NonDensityAPI`, `MainTheoremAPI`, the two `…Statement : Prop` defs, and the
   assembly signatures), elaborating with 0 errors (`cd verification && lake env lean ../research/T21/Spec.lean`), with docstrings citing paper lines and provenance comments
   `-- from DraftA:<line>` / `-- from DraftB:<line>` on every field. Print `grep -nE ': *True|:= *0$|→ *True' research/T21/Spec.lean` (empty) in the report.
3. Commit on your branch. Report in four parts (decisions made / files / open questions for the lead / commands); write it to `research/T21/REPORT_416.md` (if the report-file
   guard blocks it, put the full report in your final message).
