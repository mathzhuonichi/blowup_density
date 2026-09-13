#!/usr/bin/env python3
"""Validate and render the source-only proof plan; never invoke Lean or Lake."""
import argparse
from pathlib import Path
import hashlib
import json
import re
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "formalization/blueprint"


def uncomment(text):
    """Remove nested Lean comments and string contents, retaining line numbers."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                break
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                c = text[i]
                out.append("\n" if c == "\n" else " ")
                i += 1
                if c == "\\" and i < len(text):
                    out.append(" ")
                    i += 1
                elif c == '"':
                    break
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", action="store_true",
                        help="Also require byte identity with the historical migration snapshot")
    parser.add_argument("--check", action="store_true",
                        help="Verify generated plan documents without rewriting any files")
    args = parser.parse_args()

    def emit(path, content, generated=False):
        if args.check:
            if generated:
                assert path.read_text() == content, f"Regenerate {path.relative_to(ROOT)}"
        else:
            path.write_text(content)

    data = json.loads((PLAN / "tasks.json").read_text())
    nodes = {n["id"]: n for n in data["nodes"]}
    assert len(nodes) == len(data["nodes"]), "Duplicate task IDs"
    order, active, done = [], set(), set()

    def visit(key):
        assert key in nodes, f"Missing task {key}"
        assert key not in active, f"Dependency cycle at {key}"
        if key in done:
            return
        active.add(key)
        for dep in nodes[key]["dependencies"]:
            visit(dep)
        active.remove(key)
        done.add(key)
        order.append(key)

    for key, node in nodes.items():
        visit(key)
        for file in node["evidence"]:
            assert (ROOT / file).is_file(), f"Missing evidence {file}"
    for field in ["target", "pdf"]:
        assert (ROOT / data[field]).is_file()

    manifest = json.loads((ROOT / "logs/FORMALIZATION_SOURCE_MANIFEST.json").read_text())
    changed_snapshot_files = []
    for item in manifest["files"]:
        path = ROOT / item["path"]
        if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            changed_snapshot_files.append(item["path"])
    if args.snapshot:
        assert not changed_snapshot_files, changed_snapshot_files
    roots = [ROOT / "formalization", ROOT / "vendor/NavierStokesAndEuler",
             ROOT / "vendor/HeliCorgi"]
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
    forbidden = [p for p in tracked if p and
                 (any(x in Path(p).parts for x in [".lake", ".elan", "__pycache__"])
                  or Path(p).suffix in [".olean", ".ilean", ".o", ".trace", ".pyc"])]
    assert not forbidden, forbidden
    local_cfg = (roots[0] / "lakefile.toml").read_text()
    lock = json.loads((roots[0] / "lake-manifest.json").read_text())
    assert 'path = "../vendor/NavierStokesAndEuler"' in local_cfg
    for package in lock["packages"]:
        if package["type"] == "path":
            assert (roots[0] / package["dir"] / package["configFile"]).is_file()

    modules, imports, tokens, counts = {}, {}, [], {}
    for root in roots:
        files = []
        for directory, dirs, names in os.walk(root):
            dirs[:] = [d for d in dirs if d not in [".lake", ".git", ".elan", "__pycache__"]]
            files.extend(Path(directory) / name for name in names if name.endswith(".lean"))
        files.sort()
        counts[str(root.relative_to(ROOT))] = len(files)
        for path in files:
            mod = ".".join(path.relative_to(root).with_suffix("").parts)
            assert mod not in modules, f"Ambiguous module {mod}"
            modules[mod] = path
            code = uncomment(path.read_text())
            imports[mod] = [name for line in re.findall(
                r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M)
                for name in line.split()]
            for m in re.finditer(r"\b(?:axiom|sorry|admit)\b", code):
                tokens.append({"module": mod, "path": str(path.relative_to(ROOT)),
                               "line": code[:m.start()].count("\n") + 1,
                               "token": m[0]})
    missing = sorted({imp for imps in imports.values() for imp in imps
                      if imp.startswith(("NSFormalization", "NavierStokes", "Euler", "Formal."))
                      and imp not in modules})
    assert not missing, f"Missing copied imports: {missing}"

    reachable = set()
    def closure(mod):
        if mod in reachable:
            return
        reachable.add(mod)
        for dep in imports.get(mod, []):
            if dep in modules:
                closure(dep)
    closure("NSFormalization")
    citation_reachable = sorted(m for m in reachable if m.startswith("NSFormalization.Citations."))
    assert not citation_reachable, "Schematic citation interfaces entered the umbrella"
    reachable_tokens = [t for t in tokens if t["module"] in reachable]
    # Preserve and report legacy admissions; source copying is not certification.

    report = json.loads((ROOT / "logs/MANUSCRIPT_CHECK.json").read_text())
    mapping = {label: n["id"] for n in nodes.values() for label in n["manuscript_labels"]}
    aliases = {"lem:Rlocal": "prop:local"}
    rows = []
    for result in report["correspondence"]:
        label = result["label"]
        assert aliases.get(label, label) in mapping, f"Unmapped result {label}"
        rows.append((result, mapping[aliases.get(label, label)]))
    assert len(rows) == 34
    # The merged source has 28 distinct numbered results, including shared aliases.
    assert len({x[0]["merged_number"] for x in rows}) == 28

    graph = ["# Dependency graph", "", "Generated from [tasks.json](tasks.json). "
             "Arrows point from prerequisites to dependent tasks. "
             "This is a future proof plan, not a certification graph.", "",
             "```mermaid", "flowchart TD"]
    for n in data["nodes"]:
        graph.append(f'  {n["id"]}["{n["id"]}: {n["title"]}"]')
    for n in data["nodes"]:
        graph.extend(f'  {d} --> {n["id"]}' for d in n["dependencies"])
    graph += ["  classDef external fill:#dbeafe,stroke:#2563eb;",
              "  classDef adapter fill:#fef3c7,stroke:#b45309;",
              "  classDef assembly fill:#dcfce7,stroke:#15803d;",
              "  classDef deferred fill:#f3f4f6,stroke:#6b7280;"]
    for kind, style in [("upstream", "external"), ("literature", "external"),
                        ("adapter", "adapter"), ("assembly", "assembly"),
                        ("deferred", "deferred")]:
        graph.append("  class " + ",".join(n["id"] for n in nodes.values() if n["kind"] == kind)
                     + " " + style + ";")
    graph += ["```", "", "Blue: reusable upstream or literature input; amber: adapter; "
              "green: target assembly; grey: deferred periodic work. "
              "Colors classify work, not proof completion.", "", "## Task contracts", ""]
    for n in sorted(nodes.values(), key=lambda x: (x["priority"], order.index(x["id"]))):
        graph += [f'### {n["id"]}: {n["title"]}', "",
                  f'Priority: P{n["priority"]}. Status: `{n["status"]}`. '
                  f'Dependencies: {", ".join(n["dependencies"]) or "none"}.', "", n["contract"], ""]
        graph.extend(f'- [{e}](../../{e})' for e in n["evidence"])
        graph.append("")
    # blueprint is two directories below the repository root.
    emit(PLAN / "DEPENDENCY_GRAPH.md", "\n".join(graph).rstrip() + "\n", generated=True)
    table = ["# Result-to-task correspondence", "", "All 34 source occurrences map to "
             "28 merged results. Shared analytic nodes cover the whole-space branch first; "
             "their periodic specialization remains in T01-T04.", "",
             "| Original | Label | Merged result | Task |", "|---|---|---|---|"]
    for x, key in rows:
        table.append(f'| {x["source"]} | `{x["label"]}` | {x["merged_kind"]} '
                     f'{x["merged_number"]} | {key} |')
    emit(PLAN / "RESULT_MAP.md", "\n".join(table) + "\n", generated=True)
    summary = {"scope": "Static source/manifest/import/task validation; no Lean build, "
               "kernel proof check, or transitive axiom audit.", "task_count": len(nodes),
               "topological_order": order, "source_counts": counts,
               "source_manifest_entries": len(manifest["files"]),
               "local_umbrella_reachable_copied_modules": len(reachable),
               "local_modules_outside_umbrella": sorted(m for m in modules
                                                       if m.startswith("NSFormalization.")
                                                       and m not in reachable),
               "missing_copied_imports": missing, "citation_interfaces_reachable": citation_reachable,
               "explicit_axiom_or_admission_tokens": tokens,
               "tokens_in_copied_umbrella_closure": reachable_tokens,
               "original_result_occurrences": len(rows), "merged_result_count": 28,
               "tracked_cache_free": True, "source_hashes_match": not changed_snapshot_files,
               "changed_snapshot_files": changed_snapshot_files,
               "snapshot_identity_required": args.snapshot}
    emit(ROOT / "logs/FORMALIZATION_PLAN_CHECK.json", json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in ["task_count", "source_counts",
          "source_manifest_entries", "missing_copied_imports", "citation_interfaces_reachable",
          "tokens_in_copied_umbrella_closure", "tracked_cache_free", "source_hashes_match"]}, indent=2))
    print("Explicit axiom/admission tokens, all copied sources:", len(tokens))


if __name__ == "__main__":
    main()
