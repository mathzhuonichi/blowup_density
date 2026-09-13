# Source this file before any lake/lean command:  . scripts/lean-env.sh
# Toolchains live inside the main checkout at <repo>/.elan (gitignored), shared by all worktrees.
_common="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)"
export ELAN_HOME="$(dirname "$_common")/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
unset _common
