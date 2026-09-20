# Lane 174-SPEC-r41d-compare — reconcile the two blind R41D drafts into the frozen specification (rule 2, third agent)

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/174-SPEC-r41d-compare` (branch
`erenup/174-SPEC-r41d-compare`). Work only here; never `git push`, merge or rebase; committing on this branch
is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`;
check drafts with `cd verification && lake env lean ../research/R41D/<file>.lean`.

Read `CLAUDE.md` (rule 2), `collaboration/HANDOFF.md` §0 and §2 P11, `collaboration/tasks/R41D.md`, then the
two independent drafts written blind to each other: `research/R41D/DraftA.lean` + `COMPARISON_A.md` +
`REPORT_171-SPEC-r41d-draft-a.md`, and `research/R41D/DraftB.lean` + `COMPARISON_B.md` +
`REPORT_172-SPEC-r41d-draft-b.md`. The model for your output is `research/R43/COMPARISON.md`,
`research/R43/RECONCILIATION.md` and `research/R43/Spec.lean` (lane 037's reconciliation of R43).

## Deliverables
1. `research/R41D/COMPARISON.md`: a clause-by-clause table paper ↔ Draft A ↔ Draft B for the density branch
   of Theorem 4.1 (`paper/sections/04-whole-space.tex:7-30`, proof `:176-195`, remark `:195`;
   `sed -n` every cited line): quantifier order, force subclasses (`F_R`/`F_c`/`F_rd`), the two thresholds
   (`L¹_tH^s`, `s < 1/2`; `L²_tH^s`, `s < −1/2`), the split at `T_max(a,g) ≤ T`, the margin and the R42
   family, which `Contracts.V1`/`V2` objects each draft used (breakdown set, lifespan, norms). For every
   difference: which draft is faithful to the manuscript and why (cite the paper line), or whether both
   are defensible; list the upstream gaps both drafts found (G-table with owner, exact Lean shape, blocks
   stating vs proving), merging the two gap lists.
2. `research/R41D/RECONCILIATION.md`: the decisions (which shape wins per clause) and the risk notes
   (places where a wrong choice would make the statement false or vacuous — e.g. `⊤`-valued norms, empty
   breakdown sets, `T_max = 0` conventions, `Ico` vs `Icc` windows).
3. `research/R41D/Spec.lean`: the reconciled draft (`def`s + one `structure`, fully spelled-out fields,
   docstrings citing paper lines and the contracts consumed; no `axiom`/`sorry`/placeholder `Prop`), which
   must elaborate with 0 errors under `lake env lean`. Keep `DraftA.lean`/`DraftB.lean` untouched.
4. A short `research/R41D/REPORT_174.md` (what was reconciled / files / gaps / commands), `make check`
   from the worktree root, commit on the branch, and end with the same four parts.
