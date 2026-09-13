#!/usr/bin/env python3
"""Check document structure and source correspondence, not proof correctness."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
RESULT = re.compile(
    r"\\begin\{(theorem|proposition|lemma|corollary)\}"
    r"(?:\[([^\]]*)\])?(.*?)\\end\{\1\}", re.S
)


def expand(path):
    text = path.read_text()
    return re.sub(r"\\input\{([^}]+)\}",
                  lambda m: expand(PAPER / (m[1] + ".tex")), text)


def results(text):
    return [(m[1], m[2], re.findall(r"\\label\{([^}]+)\}", m[3]), m[3])
            for m in RESULT.finditer(text)]


def math_tokens(text):
    pattern = (r"(?<!\\)\$(?!\$).*?(?<!\\)\$|\\\[.*?\\\]|"
               r"\\begin\{(?:equation\*?|align\*?|gather\*?)\}.*?"
               r"\\end\{(?:equation\*?|align\*?|gather\*?)\}")
    parts = re.findall(pattern, text, flags=re.S)
    return [re.sub(r"\s+", "", re.sub(r"\\label\{[^}]+\}", "", p))
            for p in parts]


def main():
    merged = expand(PAPER / "blowup_density.tex")
    labels = re.findall(r"\\label\{([^}]+)\}", merged)
    counts = Counter(labels)
    assert not [k for k, v in counts.items() if v > 1], "Duplicate labels"
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", merged)
    assert not set(refs) - set(labels), "Unresolved cross-references"
    cites = {key for keys in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", merged)
             for key in keys.split(",")}
    bibs = re.findall(r"\\bibitem\{([^}]+)\}", merged)
    assert len(bibs) == len(set(bibs)), "Duplicate bibliography entries"
    assert cites == set(bibs), "Unresolved or unused bibliography entries"
    before_appendix = merged.split(r"\appendix", 1)[0]
    main_sections = re.findall(r"\\section\{([^}]+)\}", before_appendix)
    assert len(main_sections) == 5, main_sections
    assert merged.count(r"\section*{Declaration of generative AI use}") == 1

    current_results = results(merged)
    by_label = {label: record for record in current_results for label in record[2]}
    aux = (ROOT / "output/pdf/blowup_density.aux").read_text()
    numbers = dict(re.findall(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}", aux))
    manifest = {}
    correspondence = []
    for path in sorted((PAPER / "originals").rglob("*.tex")):
        manifest[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    for name in ("paper_1_theory.tex", "paper_3_whole_space.tex"):
        source = (PAPER / "originals/local" / name).read_text()
        for kind, title, old_labels, body in results(source):
            label = old_labels[0]
            assert label in by_label, f"Missing original result: {name}, {label}"
            new = by_label[label]
            correspondence.append({
                "source": name, "source_kind": kind, "source_title": title,
                "label": label, "merged_kind": new[0],
                "merged_number": numbers.get(label),
                "statement_math_unchanged": math_tokens(body) == math_tokens(new[3]),
            })
    log = (ROOT / "output/pdf/blowup_density.log").read_text()
    warnings = re.findall(r".*(?:Warning|Overfull|Underfull|undefined|multiply defined).*", log)
    assert not warnings, warnings
    report = {
        "main_sections": main_sections,
        "original_results": len(correspondence),
        "merged_results": len(current_results),
        "labels": len(labels), "bibliography_entries": len(bibs),
        "warnings": warnings, "source_sha256": manifest,
        "correspondence": correspondence,
        "scope": "Structural and formula comparison only; mathematical equivalence requires the accompanying proof review.",
    }
    (ROOT / "logs/MANUSCRIPT_CHECK.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items()
                      if k not in {"correspondence", "source_sha256"}}, indent=2))
    changed = [c for c in correspondence if not c["statement_math_unchanged"]]
    print("Statements requiring contextual/manual comparison:")
    for c in changed:
        print(c["source"], c["label"], c["merged_kind"], c["merged_number"])


if __name__ == "__main__":
    main()
