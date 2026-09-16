# Fix for lane 166-R44-split — apply the four review notes (records only)

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/166-R44-split` (branch `erenup/166-R44-split`,
your commit `ec56cb5`). Work only here; never `git push`, merge or rebase; committing on this branch is
allowed. The review is in `research/R44/REVIEW_166-R44-split.md` (verdict ACCEPT-WITH-NOTES). Apply
exactly its four fixes, in `research/R44/R44_SPLIT.md` and `research/R44/REPORT_166.md` (and
`research/R44/ATTEMPTS_R44.md` if the same claims appear there); do NOT change any Lean file:
1. Record that row S1 must supply one interval-integrable derivative function `E'` on the window, not
   merely pointwise derivative witnesses (the scalar bootstrap consumes an integrable `E'`).
2. Record the global-continuity / continuous-extension obligation for `Y` (the bootstrap inherits a
   global `Continuous Y` hypothesis from `Paper1`), and correct REPORT_166's "conditional only" wording
   accordingly.
3. Correct the paper citations `04-whole-space.tex:170` → `:171` in the two split-table locations the
   review names (verify with `sed -n 170,171p paper/sections/04-whole-space.tex`).
4. Correct the A04 V3 status: `extendsBeyond` is neither proved nor registered on this branch (the
   owner's PR #161 to `main` proves a conditional version but it is not on `origin/erenup/integration`).
Then run `make check` from the worktree root, commit on the branch, and end with a short report listing
the exact lines changed (`git diff --stat HEAD~1`).
