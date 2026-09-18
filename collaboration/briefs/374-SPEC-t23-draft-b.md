# Lane 374-SPEC-t23-draft-b — Section 3 node T23 (`cor:boundary`, interior no-slip insertion on a bounded domain): double-blind draft B of the Lean statements

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/374-SPEC-t23-draft-b` (git branch `erenup/374-SPEC-t23-draft-b`, based on `origin/erenup/integration-section3`).
One of two **independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): **do NOT read** `research/T23/` or `collaboration/briefs/` entries for the other T23 lane.

Read: `CLAUDE.md` (contract rules; no placeholder `Prop`s; docstrings cite paper lines), `collaboration/SECTION3_PLAN.md` §1–§3 (the T23 row), the paper `paper/sections/03-torus.tex:632-667` (`cor:boundary`: interior no-slip insertion, the boundary collar preserved, domain-vs-zero-extension norms, no-slip uniqueness) **in full,
statements and proofs** (know which objects come from `thm:insertion` (T18), `prop:local` (T11), `prop:critical` (T20) and what each result adds), and the vocabulary the
statements must be written in — **import the registered contracts, copy the rest verbatim**:
- registered (import and use by name; nothing registered is copied): `verification/Contracts/V1/TorusData.lean`, `Contracts/V1/TorusLocalTheory.lean` (`ClassicalSolutionT`,
  `maximalLifespanT`, `breakdownSetT`/`breakdownSetInT`, `RelativelyDenseT`, `forceClassT`, `initialClassT`, the energy/mixed/Sobolev norms, the T11 APIs),
  `Contracts/V1/Packet.lean`, `Contracts/V1/PacketImport.lean`, and the Section 4 counterparts (none registered for the bounded domain; the structure is `thm:insertion` restricted to `Ω` — mirror T18's `PeriodicInsertionAPI` field-for-field where the proof is the same and add exactly the boundary clauses; the local implementation candidate `formalization/NSFormalization/Paper1/BoundaryCorollary.lean` has a `sorry` at `:90` and must NOT be imported — cite it only) — read every field; the torus statement should mirror the Section 4
  record field-for-field where the paper's proof is the same and differ exactly where the torus differs (say where).
- unregistered, copy verbatim (T13 copy policy: same names, namespaces, delimited blocks with provenance comments `-- copied verbatim from research/<T>/Spec.lean:<lines>`):
  `research/T18/Spec.lean` (`PeriodicInsertionAPI`, `periodicInsertionStatement` and the T15/T16/T17 vocabulary block it carries — copy exactly the declarations you use; T18 is
  the insertion input to T23), `research/T20/Spec.lean` (`CriticalRegularityTAPI` if T23 consumes `prop:critical`), `research/T12/Spec.lean` if needed, and the reconciled bounded-domain layer `research/T22/Spec.lean` (`BoundedDomainNormAPI`, `restrictField`, `zeroExtension`, `domainSobolevENorm`, `IsCutoffDatum`) — copy verbatim what you use. Do not
  re-invent any of them; where a copied block overlaps a registered name add an `example … := rfl` drift check.

## Deliverables (statements only, no proofs)
1. `research/T23/DraftB.lean` (create the directory): a file that **elaborates** (`cd verification && lake env lean ../research/T23/DraftB.lean`, 0 errors). In a
   namespace `BlowupDensity.T23.DraftB`, one structure per result — `BoundaryInsertionAPI` (cor:boundary; the hypotheses on `Ω` as parameters, the no-slip uniqueness and collar clauses as fields) — each field exactly one clause of the paper's statement (hypotheses and conclusions each
   their own field, docstring citing `03-torus.tex:<line>`, exact quantifier order, "non-vacuity" comment, **no junk-value traps**: integrability/class hypotheses on every norm,
   `ν > 0`, `ℝ≥0∞` suprema not real `sSup`, `tsum` only with summability), Type-valued when the paper has constants/data, `Prop` otherwise (say which and why), plus one
   `def <result>Statement : Prop` per result in the paper's quantifier order.
2. `research/T23/COMPARISON_B.md`: paper-clause → Lean field table (with the Section 4 counterpart field or "torus-only"); choices; ambiguities; "needs a lemma" list
   (which T11/T12/T18/T20 fields the proof will consume); implementation candidates (`grep -nE "^(def|structure|theorem) "` in the `Paper1/` modules named in the T23 row of
   `collaboration/SECTION3_PLAN.md`).
3. Commit on your branch (never push/merge/rebase). Report in four parts; write it to `research/T23/REPORT_374.md`.

## Quality clause
Earlier draft lanes that returned a ~100-line file with self-made stubs for the imported records, or structures of two or three fields, were **discarded**. Copy the vocabulary
verbatim; render every result clause by clause from the paper text (statement *and* proof); a draft is expected to be several hundred lines with a table in
`COMPARISON_B.md` covering every clause. No field may be `True`, a tautology, or a definition ignoring its arguments; print
`grep -nE ': *True|:= *0$|→ *True' research/T23/DraftB.lean` (empty) in the report. Spend the time; do not stop early.
