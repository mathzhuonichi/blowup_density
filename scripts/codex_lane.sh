#!/usr/bin/env bash
# Run one lane's brief through `codex exec` inside a tmux window, non-interactively.
#
#   scripts/codex_lane.sh <lane> <model> <effort> <brief.md> [tag]   (tag=fix → names fix_<lane>)
#
#   lane    = NNN-<node>-<slug>; the worktree .claude/worktrees/<lane> must already exist
#             (create it with `git worktree add … origin/erenup/integration` + scripts/lean-install.sh)
#   model   = gpt-5.6-sol | gpt-6-astra | …      effort = low | medium | high | xhigh
#   brief   = markdown file with the full task (fed to codex on stdin)
#
# Output: tmp/codex/<lane>.log (full transcript), tmp/codex/<lane>.last.md (codex's final message),
#         tmp/codex/<lane>.DONE (exit code) — watch the DONE file, never tail the log into context.
# The tmux session is `bd`; one window per lane, named after the lane.  Codex runs with
# --sandbox danger-full-access and approval never (user's choice); the brief must forbid
# `git push`, touching other worktrees, and the root checkout.
set -euo pipefail
LANE=$1; MODEL=$2; EFFORT=$3; BRIEF=$4; TAG=${5:-}
NAME=${TAG:+${TAG}_}$LANE   # e.g. fix_167-… : same worktree, separate log/DONE/window
ROOT=/data_8T/ping/blowup_density
WT=$ROOT/.claude/worktrees/$LANE
[ -d "$WT" ] || { echo "no worktree $WT"; exit 1; }
[ -f "$BRIEF" ] || { echo "no brief $BRIEF"; exit 1; }
BRIEF=$(readlink -f "$BRIEF")
mkdir -p "$ROOT/tmp/codex"
LOG=$ROOT/tmp/codex/$NAME.log; LAST=$ROOT/tmp/codex/$NAME.last.md; DONE=$ROOT/tmp/codex/$NAME.DONE
RUN=$ROOT/tmp/codex/run_$NAME.sh
rm -f "$DONE"
cat > "$RUN" <<EOS
#!/usr/bin/env bash
cd "$WT" || { echo "cd failed" > "$DONE"; exit 1; }
. scripts/lean-env.sh
echo "== start \$(date -u +%FT%TZ) model=$MODEL effort=$EFFORT" > "$LOG"
codex exec -C "$WT" -m "$MODEL" -c model_reasoning_effort="$EFFORT" -c approval_policy="never" \\
  -s danger-full-access --color never -o "$LAST" - < "$BRIEF" >> "$LOG" 2>&1
RC=\$?
echo "== end \$(date -u +%FT%TZ) rc=\$RC" >> "$LOG"
echo "\$RC" > "$DONE"
EOS
chmod +x "$RUN"
tmux has-session -t bd 2>/dev/null || tmux new-session -d -s bd -n lead
tmux new-window -d -t bd -n "$NAME" "bash '$RUN'"
echo "launched $NAME ($MODEL/$EFFORT) in tmux window bd:$LANE; log $LOG"
