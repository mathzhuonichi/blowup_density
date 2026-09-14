import os, re, sys
ROOT = "formalization/NSFormalization"
imp = {}
def mod_of(path):
    rel = os.path.relpath(path, "formalization")[:-5]  # drop .lean
    return rel.replace(os.sep, ".")
for dp, _, fns in os.walk(ROOT):
    for fn in fns:
        if fn.endswith(".lean"):
            p = os.path.join(dp, fn)
            m = mod_of(p)
            deps = []
            for line in open(p, encoding="utf-8"):
                mm = re.match(r"\s*import\s+(NSFormalization\.\S+)", line)
                if mm: deps.append(mm.group(1).strip())
            imp[m] = deps
def closure(start):
    seen, stack = set(), [start]
    while stack:
        x = stack.pop()
        for d in imp.get(x, []):
            if d not in seen:
                seen.add(d); stack.append(d)
    return seen
# 1. Any Section4.D01.* module whose closure contains a Section4.A04.* module?
bad = []
for m in imp:
    if m.startswith("NSFormalization.Section4.D01."):
        a04 = sorted(d for d in closure(m) if d.startswith("NSFormalization.Section4.A04."))
        if a04:
            bad.append((m, a04))
print("=== D01 modules whose import-closure reaches A04 (reverse edge) ===")
if not bad:
    print("  NONE — no Section4.D01.* module imports any Section4.A04.* module.")
else:
    for m, a in bad:
        print(f"  {m} -> {a}")
# 2. Sanity: the two moved modules' direct imports
for m in ["NSFormalization.Section4.D01.LaplacianPairing","NSFormalization.Section4.D01.RealPairing"]:
    print(f"  {m} imports: {imp.get(m)}")
# 3. Confirm A04 pairing modules no longer exist
for m in ["NSFormalization.Section4.A04.LaplacianPairing","NSFormalization.Section4.A04.RealPairing"]:
    print(f"  {m} present as file? {m in imp}")
sys.exit(1 if bad else 0)
