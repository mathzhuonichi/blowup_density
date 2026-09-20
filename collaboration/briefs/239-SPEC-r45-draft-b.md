# Lane 239-SPEC-r45-draft-b — double-blind specification of Corollary 4.x "cor:Rclasses" (R45: Theorem 4.1 for the compactly supported and rapidly decaying force classes F_c, F_rd): draft B

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **specification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/239-SPEC-r45-draft-b` (git branch `erenup/239-SPEC-r45-draft-b`, based on `origin/erenup/integration`). This is one of two
**independent, mutually invisible** drafts (rule 2 of `CLAUDE.md`): write the Lean statement from the manuscript and the registered vocabulary only. Therefore **do NOT read**
`research/section4/STATEMENTS.md`, `research/R41*`, `research/R45*`, `formalization/NSFormalization/Section4/R41/`, `verification/Bindings/DensityFromInsertion.lean`, `collaboration/briefs/`,
or any file whose name mentions R41/R45/RMain/Rclasses.

Read: `CLAUDE.md` (contract import rules; no placeholder `Prop`s; docstrings cite paper lines), `formalization/blueprint/tasks.json` entry for **R45** only (its one-line contract),
the paper: `grep -n "cor:Rclasses" paper/sections/04-whole-space.tex` and read the corollary statement and its proof paragraph(s) (`:182-215` approximately), the class definitions
`02-preliminaries.tex:20-60` (`F_c`, `F_rd`, `S_σ`/Schwartz initial data, the relative topologies), `01-introduction.tex:120-145`, and the registered vocabulary
`verification/Contracts/V1/Data.lean` (`initialClassR`, `initialClassSchwartz`, `forceClassR`, `forceClassCompact`, `MemForceCompact`, `forceClassRapid`, `MemForceRapid`,
`breakdownSetIn Y ν a T` (parametric in the ambient class `Y`), `RelativelyDense q s Y S`, `forceSobolevENorm`, `maximalLifespanR` — `:225-236`, `:509-580`, `:657-712`),
`verification/Contracts/V1/Thresholds.lean`, and one registered contract as a formatting template (`verification/Contracts/V1/CriticalRegularity.lean`).

## Deliverables (statements only, no proofs)
1. `research/R45/DraftB.lean` (create the directory): a Lean file that **elaborates** (`cd verification && lake env lean ../research/R45/DraftB.lean`) containing `structure RClassesAPI`
   (or your name) with one field per clause of the corollary exactly as the manuscript states it — for each ambient class `Y ∈ {F_c, F_rd}` (parametric or two copies — say why), the density
   clause(s), the zero-datum iff, and every rider the corollary states (which initial data are allowed: `X_R` or `S_σ`; energy/history assertions if present) — each with a docstring citing
   `04-whole-space.tex:<line>` and the exact quantifier order. If a needed notion is absent from `Data.lean`, define it locally **verbatim from the paper** and flag "needs registration".
2. `research/R45/COMPARISON_B.md`: paper-clause → Lean field table; choices (parametric `Y` vs copies, casts, how "relative topology" is rendered, what the corollary inherits from Theorem 4.1
   vs. what is new — e.g. that the inserted forces stay in `F_c`/`F_rd`); every ambiguity in the manuscript.
3. Commit on your branch (never push/merge/rebase). Report in four parts and write it to `research/R45/REPORT_239.md`.
