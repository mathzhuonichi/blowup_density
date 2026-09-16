#!/usr/bin/env bash
# Review a finished lane with codex (non-interactive) inside the lane's worktree.
#
#   scripts/codex_review.sh <lane> [model] [effort]      (defaults: gpt-5.6-sol xhigh)
#
# Reads the lane's brief (collaboration/briefs/<lane>.md) and its report
# (research/<node>/REPORT_<n>.md or tmp/codex/<lane>.last.md), writes the review to
# research/<node>/REVIEW_<lane>.md inside the worktree, and the verdict line to
# tmp/codex/review_<lane>.last.md; DONE marker tmp/codex/review_<lane>.DONE.
set -euo pipefail
LANE=$1; MODEL=${2:-gpt-5.6-sol}; EFFORT=${3:-xhigh}
ROOT=/data_8T/ping/blowup_density
WT=$ROOT/.claude/worktrees/$LANE
NODE=${LANE:4}; NODE=${NODE%%-*}
# SPEC/MAINT lanes name the real node in the next token (e.g. 174-SPEC-r41d-compare → R41D).
if [ "$NODE" = SPEC ] || [ "$NODE" = MAINT ]; then
  N2=${LANE#*-*-}; N2=${N2%%-*}; N2=$(echo "$N2" | tr '[:lower:]' '[:upper:]')
  [ -d "$ROOT/research/$N2" ] && NODE=$N2 || NODE=MAINT
fi
N=${LANE%%-*}
BRIEF=$ROOT/collaboration/briefs/$LANE.md
[ -d "$WT" ] || { echo "no worktree $WT"; exit 1; }
[ -f "$BRIEF" ] || { echo "no brief $BRIEF"; exit 1; }
mkdir -p "$ROOT/tmp/codex"
RB=$ROOT/tmp/codex/briefs/review_$LANE.md
cat > "$RB" <<EOF
# Review of lane $LANE (read-only reviewer)

You are the independent reviewer for lane \`$LANE\` in the worktree \`$WT\` (branch
\`erenup/$LANE\`). Read \`CLAUDE.md\`, \`.claude/skills/lane-review/SKILL.md\` if present, the top 40 lines
of \`logs/LESSONS.md\`, the lane's brief below, and the worker's report
(\`research/$NODE/REPORT_$N.md\`, else \`$ROOT/tmp/codex/$LANE.last.md\`).

Rules: read-only — do not edit the lane's Lean or records and make no git state changes; you may
add probe files under \`research/$NODE/probes/rev${N}_*.lean\` and you MUST write your report to
\`research/$NODE/REVIEW_$LANE.md\` (new file). Lean: \`. scripts/lean-env.sh\`; \`lake\` only from
\`verification/\` with \`LEAN_NUM_THREADS=6\`.

Check, citing \`file:line\` for each:
1. **Statement fidelity**: every theorem the report claims exists with exactly the claimed statement;
   it is the mathematics the brief asked for (open the cited paper lines with \`sed -n\` and the cited
   tree lemmas); no hypothesis was silently added that makes it vacuous (\`⊤.toReal = 0\`, empty
   intervals, unused binders); named hypotheses are honest and isolated.
2. **Build**: rerun every gate the brief lists (\`lake build\` of the module — silent for this module,
   \`lake env lean\` on the module — 0 output, the axioms file — every \`#print axioms\` exactly
   \`[propext, Classical.choice, Quot.sound]\`, \`make check\`, plus \`scripts/gates.sh\` and
   \`check_contracts.py --base-ref origin/erenup/integration\` if \`verification/\` was touched).
   Paste exact outputs.
3. **Hygiene**: no \`sorry/admit/axiom/native_decide\`; \`maxHeartbeats\` only per declaration ≤ 400000
   with a comment; no existing module modified (\`git diff --name-only origin/erenup/integration...HEAD\`);
   citations correct.
4. **Negative check**: at least one substantive mutation of a main statement in a scratch probe
   (change a constant, flip a sign, widen an interval) and confirm the proof breaks with the expected
   error — never by merely dropping an argument. Plus a non-vacuity instance if the report has none.
5. **"Not in the tree" claims**: for every gap the report declares, \`grep -rn\` the whole
   \`formalization/NSFormalization/Section4\` tree for the missing lemma before accepting the claim.

Verdict on the first line of your report: \`ACCEPT\` / \`ACCEPT-WITH-NOTES\` (exact one-line fixes) /
\`REJECT\` (with the reproducing error). Then four parts: what the lane claims / what is in Lean /
gaps / commands and results. End your final message with the verdict line and the list of fixes.

$( [ -f "$ROOT/tmp/codex/briefs/review_notes_$LANE.md" ] && { echo "---- RAW OUTPUT LIMIT: in the review file quote at most the first and last 40 lines of any command output (never paste full build/make-check logs) ----
---- lead's specific check points (address each explicitly) ----"; cat "$ROOT/tmp/codex/briefs/review_notes_$LANE.md"; } )

---- lane brief ----
$(cat "$BRIEF")
$( [ -f "$ROOT/tmp/codex/briefs/fix_$LANE.md" ] && { echo; echo "---- LATER FIX BRIEF (supersedes the lane brief where they conflict; judge the lane against THIS) ----"; cat "$ROOT/tmp/codex/briefs/fix_$LANE.md"; } )
EOF
LOG=$ROOT/tmp/codex/review_$LANE.log; LAST=$ROOT/tmp/codex/review_$LANE.last.md; DONE=$ROOT/tmp/codex/review_$LANE.DONE
RUN=$ROOT/tmp/codex/run_review_$LANE.sh
rm -f "$DONE"
cat > "$RUN" <<EOS
#!/usr/bin/env bash
cd "$WT" || { echo "cd failed" > "$DONE"; exit 1; }
. scripts/lean-env.sh
echo "== start \$(date -u +%FT%TZ) review model=$MODEL effort=$EFFORT" > "$LOG"
codex exec -C "$WT" -m "$MODEL" -c model_reasoning_effort="$EFFORT" -c approval_policy="never" \\
  -s danger-full-access --color never -o "$LAST" - < "$RB" >> "$LOG" 2>&1
RC=\$?
echo "== end \$(date -u +%FT%TZ) rc=\$RC" >> "$LOG"
echo "\$RC" > "$DONE"
EOS
chmod +x "$RUN"
tmux has-session -t bd 2>/dev/null || tmux new-session -d -s bd -n lead
tmux new-window -d -t bd -n "rev-$N" "bash '$RUN'"
echo "review of $LANE launched ($MODEL/$EFFORT) in tmux window bd:rev-$N; log $LOG"
