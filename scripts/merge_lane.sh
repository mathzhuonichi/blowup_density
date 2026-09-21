#!/usr/bin/env bash
# Usage: merge_lane.sh <lane-worktree> "<squash message>"   (run gates + gh pr merge separately)
set -euo pipefail
LANE=$1; MSG=$2
ROOT=/data_8T/ping/blowup_density/.claude/worktrees; cd "$ROOT/$LANE"
git fetch -q origin
MB=$(git merge-base HEAD origin/erenup/integration)
if [ "$(git rev-list --count "$MB"..HEAD)" -gt 1 ]; then git reset -q --soft "$MB"; git commit -q -m "$MSG"; fi
LANE_TIP=$(git rev-parse HEAD)
if ! GIT_EDITOR=true git rebase origin/erenup/integration >/dev/null 2>&1; then
  for f in verification/contracts.json collaboration/work_items.json; do
    if git ls-files -u -- "$f" | grep -q .; then
      git show "$MB:$f" > /tmp/mb.json; git show "origin/erenup/integration:$f" > /tmp/int.json; git show "$LANE_TIP:$f" > /tmp/lane.json
      python3 "$(git rev-parse --show-toplevel)/scripts/merge_json3.py" "$f" /tmp/mb.json /tmp/int.json /tmp/lane.json; git add "$f"
    fi
  done
  # Bookkeeping files are owned by integration: a lane's stale copies (e.g. from a rewritten local
  # integration history) always lose to the version being rebased onto.
  for f in PLAN.md NEXT_SESSION.md CLAUDE.md logs/AGENT_RUNS.csv logs/LESSONS.md; do
    if git ls-files -u -- "$f" | grep -q .; then git checkout --ours -- "$f"; git add "$f"; fi
  done
  # Research records (split tables, attempts) conflict only because several lanes append notes at the
  # same spot: keep both sides (integration's first, then the lane's lines not already present).
  for f in $(git ls-files -u | cut -f2 | sort -u | grep '^research/.*\.md$'); do
    python3 - "$f" <<'PY'
import sys
p=sys.argv[1]; L=open(p,encoding='utf-8').read().split('\n'); out=[]; st=0; ours=[]; theirs=[]
for l in L:
    if l.startswith('<<<<<<<'): st=1; ours=[]; theirs=[]; continue
    if l.startswith('=======') and st==1: st=2; continue
    if l.startswith('>>>>>>>') and st==2:
        out.extend(ours); out.extend([x for x in theirs if x not in ours]); st=0; continue
    (ours if st==1 else theirs if st==2 else out).append(l)
open(p,'w',encoding='utf-8').write('\n'.join(out))
PY
    git add "$f"
  done
  git checkout --ours -- collaboration/TASKS.md collaboration/tasks 2>/dev/null || true
  python3 experiments/tasks.py render >/dev/null; git add collaboration
  GIT_EDITOR=true git -c core.editor=true rebase --continue >/dev/null
fi
echo "rebased: $(git log --oneline -1 | cat)"; git status --short | head -3
