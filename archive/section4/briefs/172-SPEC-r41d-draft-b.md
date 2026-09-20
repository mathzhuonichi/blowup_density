# Lane 172-SPEC-r41d-draft-b — blind specification draft B for R41D (Theorem 4.1, subcritical density branch)

You are writing a **Lean 4 statement draft only** (no proofs) in the worktree
`/data_8T/ping/blowup_density/.claude/worktrees/172-SPEC-r41d-draft-b` (branch `erenup/172-SPEC-r41d-draft-b`, based on
`origin/erenup/integration`). Read `CLAUDE.md` (rule 2: statement fidelity by two blind drafts),
`collaboration/HANDOFF.md` §0 and §2 P11, and `collaboration/tasks/R41D.md` first.

## Blindness rule
This is draft **B** of two independent drafts. Do NOT read, open, grep or search for any other R41D
draft, any `research/R41D/` file other than the ones you create, or any other worktree; do not read
`research/section4/STATEMENTS.md` entries about R41D beyond the ledger lines the task card cites. Your only
mathematical inputs are the paper and the `Contracts/V1` definitions listed below. Record in your report
that you complied.

## Ground rules
- Work only inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`; check your
  draft with `cd verification && lake env lean ../research/R41D/DraftB.lean` (it must elaborate with
  0 errors; `#check`/`#print axioms` of the structure allowed).
- The draft may contain only `def`s and one `structure` whose fields are fully spelled-out propositions
  about `Contracts.V1.Data` objects (and other registered contract objects): **no** `axiom`, `sorry`,
  `native_decide`, no abstract `Prop` placeholder fields, no proofs with mathematical content. Import only
  `Contracts.V1.*` / `Contracts.V2.*` / `Contracts.V3.*` and Mathlib (the contract import policy).

## Inputs (read these, in this order)
1. `paper/sections/04-whole-space.tex:1-30` (Theorem 4.1 `thm:Rmain`, the two thresholds; identify the
   **subcritical density branch** — the direction that produces, for every fixed smooth divergence-free
   `a` and every reference force `g`, density of blow-up forces in `L¹_t H^s` / `L²_t H^s` for
   subcritical `s` — and its proof `:176-195` incl. the remark `:195` about `F_c`/`F_rd`); the
   definitions it uses in `02-preliminaries.tex` (classes `X_R`, `F_R`, `F_c`, `F_rd`, lifespan
   `T_max`, the norms). `sed -n` every line you cite.
2. `collaboration/tasks/R41D.md` (goal: "split at `T_max(a,g) ≤ T`; use `g` itself in the first case,
   otherwise insert after choosing a positive margin beyond `T`; quantifier order ∀ a ∀ g …").
3. `verification/Contracts/V1/Data.lean` (`SpatialField`, `SpaceTimeField`, `initialClassR`,
   `MemForceR`, `MemForceCompact`, `ClassicalSolutionR`, `maximalLifespanR`, `RegularThrough`,
   `breakdownSetR*`, the `L¹_tH^s`/`L²_tH^s` force norms) and the registered R42 contracts this
   branch consumes: `verification/Contracts/V1/InsertionFamily.lean`, `Contracts/V1/InsertionLifespan.lean`,
   `Contracts/V2/InsertionLifespan.lean` (Theorem 4.2: the inserted family `g_ε`, its lifespan
   `= T`, the margin beyond `T`) — use their exact objects and names.
4. Template for the file shape: `research/R43/DraftB.lean` (header conventions, how fields cite
   paper lines, how the `c`-style constants are carried).

## Deliverables
1. `research/R41D/DraftB.lean`: `structure RDensityAPI` (or a name you justify) whose fields state
   the density branch of Theorem 4.1 exactly as the manuscript does, with the quantifier order of the task
   card, parameterized by the force subclass (`F_R` / `F_c` / `F_rd`, per `:195` and `PLAN.md` §9's
   DAG note), each field's docstring citing the paper line(s) and the `Contracts` objects used, and
   naming the R42 fields it consumes.
2. `research/R41D/COMPARISON_B.md`: a table paper-clause ↔ Lean field, plus every place where the
   `Contracts.V1` vocabulary forced a choice (e.g. how "density in `L¹_tH^s`" is spelled, which
   breakdown set, which lifespan clause), and a list of upstream gaps (objects the draft needed and could
   not find in the contracts — exact shape needed, owner).
3. Commit on your branch. End with a four-part report (what is stated / files / gaps / commands) and
   write it to `research/R41D/REPORT_172-SPEC-r41d-draft-b.md`.
