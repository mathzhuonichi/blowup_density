# Lane 236-SPEC-r41-draft-a — double-blind specification of Theorem 4.1 (thm:Rmain, R41): draft A of the Lean contract statement

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/236-SPEC-r41-draft-a` (git branch `erenup/236-SPEC-r41-draft-a`, based on `origin/erenup/integration`). This is one of two
**independent, mutually invisible** drafts (rule 2 of `CLAUDE.md` "陈述保真第一": two agents who only read the paper each write the Lean statement; the lead compares). Therefore:
**do NOT read** `research/section4/STATEMENTS.md`, `research/R41D/`, `research/R41/`, `collaboration/briefs/` for other R41 lanes, `formalization/NSFormalization/Section4/R41/`,
`verification/Bindings/DensityFromInsertion.lean`, or any file whose name mentions R41/R41D/RMain — write the statement from the manuscript and the registered vocabulary only.

Read: `CLAUDE.md` (contract import rules: `Contracts/*` import only `Mathlib`/`Contracts.*`; structures with explicit fields; no placeholder `Prop`s; docstrings cite paper lines),
the paper `paper/sections/04-whole-space.tex:1-60` (thm:Rmain and its surroundings), `:176-181` (the proof's structure — only to understand which objects the statement quantifies),
`02-preliminaries.tex:20-60` (the classes `X_R`, `F_R`, the breakdown set eq:Rsingularforces, the relative topology), `01-introduction.tex:120-145` (the force topologies), and the
registered vocabulary `verification/Contracts/V1/Data.lean` (§ `initialClassR`, `forceClassR`, `MemForceR`, `maximalLifespanR`, `breakdownSetIn/breakdownSetR/breakdownSetRZero`,
`RelativelyDense`, `BreakdownDenseR`, `forceSobolevENorm`, `RegularThrough` — `:225-236`, `:509-580`, `:657-712`) and `verification/Contracts/V1/Thresholds.lean` (`ThresholdAPI`, the registered
`R41.threshold_arithmetic`: `exponent q s = 2/q - 3/2 - s`), plus a registered contract as a formatting template (`verification/Contracts/V1/CriticalRegularity.lean`).

## Deliverables (no proofs — statements only)
1. `research/R41/DraftA.lean` (create the directory if absent): a Lean file that **elaborates** (`cd verification && lake env lean ../research/R41/DraftA.lean`, 0 errors) containing
   `structure RMainAPI` (or your preferred name) with one field per clause of Theorem 4.1 exactly as the manuscript states it — the fixed-initial-velocity density clause (i), the zero-velocity
   "if and only if" clause (ii) (as two fields or one iff — say why), and every rider sentence of the theorem statement (regular reference / insertion assertions / energy & earlier-history
   assertions) — each with a docstring citing `04-whole-space.tex:<line>` and the exact quantifier order transcribed from the paper. Use only `Contracts.V1.Data`/`Thresholds` vocabulary; if
   a needed notion is absent from `Data.lean`, define it locally in the draft **verbatim from the paper** with the paper line in its docstring, and flag it as "needs registration".
2. `research/R41/COMPARISON_A.md`: a table paper-clause → Lean field, the choices you made (types of `q`, `s`, casts, how "relative topology"/"dense" is rendered, how `T_max = T` exactly
   is rendered, which riders are re-exports of Theorem 4.2's fields), and every place the manuscript is ambiguous.
3. Commit on your branch (never push/merge/rebase). Report in four parts (statement written / choices / ambiguities / commands) and write it to `research/R41/REPORT_236.md`.
