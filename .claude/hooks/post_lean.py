#!/usr/bin/env python3
"""PostToolUse check for .lean edits: no sorry/admit/axiom/native_decide outside comments; contract files
must still satisfy the import policy. Exit 2 + stderr feeds the finding back to the agent."""
import json, os, re, subprocess, sys

try:
    ev = json.load(sys.stdin)
except Exception:
    sys.exit(0)
path = (ev.get("tool_input", {}) or {}).get("file_path", "") or ""
if not path.endswith(".lean") or not os.path.exists(path):
    sys.exit(0)
src = open(path, encoding="utf-8", errors="replace").read()
code = re.sub(r"/-.*?-/", "", src, flags=re.S)           # block comments (incl. doc comments)
code = "\n".join(l.split("--", 1)[0] for l in code.split("\n"))
hits = [(i + 1, l.strip()) for i, l in enumerate(code.split("\n"))
        if re.search(r"\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\b", l)]
msgs = []
if hits:
    msgs.append("post_lean: forbidden token(s) in %s: %s" % (path, "; ".join("L%d: %s" % h for h in hits[:5])))
if "/verification/Contracts/" in path:
    root = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=os.path.dirname(path),
                          capture_output=True, text=True).stdout.strip()
    if root and os.path.exists(os.path.join(root, "experiments", "check_contracts.py")):
        r = subprocess.run([sys.executable, "experiments/check_contracts.py"], cwd=root, capture_output=True, text=True)
        if r.returncode != 0:
            msgs.append("post_lean: check_contracts.py failed after editing %s:\n%s" % (path, (r.stdout + r.stderr)[-1500:]))
if msgs:
    print("\n".join(msgs), file=sys.stderr); sys.exit(2)
sys.exit(0)
