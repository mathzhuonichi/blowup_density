---
name: lane-merge
description: Merge a reviewed lane PR into erenup/integration (squash, rebase with registry three-way merge, push, gh pr merge, record).
---
Use after a lane's reviewer says ACCEPT (or its notes are fixed). Never while PR #15's CI is running a run you want to keep.

1. `scripts/merge_lane.sh <lane-worktree-name> "<squash commit message>"` — squashes the lane to one commit, rebases onto `origin/erenup/integration`, merges `verification/contracts.json` / `collaboration/work_items.json` three-way (integration's file + the lane's own entries), re-renders task cards.
2. In the lane worktree: `git diff origin/erenup/integration --stat -- verification/contracts.json collaboration/work_items.json` must be additive; for contract lanes `python3 -c "import json;print([c['id'] for c in json.load(open('verification/contracts.json'))['contracts']])"`.
3. `git push --force-with-lease origin <branch>`; then retry `gh pr merge N --merge` in a loop (up to 10 × 6 s): GitHub's `mergeable` flips between UNKNOWN and MERGEABLE for 10–60 s after a force-push and a single poll is not enough.
4. Contract lanes: afterwards run `scripts/gates.sh` in `000-integration` (after `git pull --ff-only`).
5. Record: PLAN.md progress row → 已合入 + PR number; one CSV line in `logs/AGENT_RUNS.csv` if not yet written; bookkeeping commits are held until the current CI run finishes.
Batch several PRs back to back; each merge triggers the integration→main CI with cancel-in-progress, so only the last run matters.
