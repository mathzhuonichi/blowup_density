#!/usr/bin/env python3
"""Validate source packaging and the retained blueprint; never invoke Lean."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import textwrap

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / 'formalization/blueprint'

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


def validate_proof_graph(proof, report):
    nodes = {n['id']: n for n in proof['nodes']}
    assert len(nodes) == len(proof['nodes']), 'Duplicate proof-node IDs'
    assert report is not None, 'The proof graph requires the recorded kernel audit'
    expected = {r['label']: r['coverage'] for r in report['article_rows']}
    coverage = {}
    active, done = set(), set()
    def visit(key):
        assert key in nodes, f'Unknown proof dependency: {key}'
        assert key not in active, f'Cycle in the article proof graph: {key}'
        if key in done:
            return
        active.add(key)
        node = nodes[key]
        assert node['status'] in {'Closed', 'Partial'}, key
        assert node['scope'] and node['evidence'], key
        for path in node['evidence']:
            assert (ROOT / path).is_file(), (key, path)
        for source in node['depends_on']:
            visit(source)
            if node['status'] == 'Closed':
                assert nodes[source]['status'] == 'Closed', f'Closed proof depends on Partial input: {source} -> {key}'
        if node['completion_from']:
            assert node['status'] == 'Partial', f'Only unfinished scopes have completion links: {key}'
        for source in node['completion_from']:
            visit(source)
        active.remove(key)
        done.add(key)
    for key, node in nodes.items():
        visit(key)
        label = node['article_label']
        if label is not None:
            assert label in expected, label
            previous = coverage.get(label, 'Closed')
            coverage[label] = 'Partial' if 'Partial' in (previous, node['status']) else 'Closed'
    assert coverage == expected, 'Clause-level graph disagrees with whole-statement coverage'
    displayed, displayed_edges = set(), set()
    for panel in proof['panels']:
        ids = set(panel['nodes'])
        assert len(ids) == len(panel['nodes']) and ids <= nodes.keys(), panel['title']
        displayed.update(ids)
        displayed_edges.update((source, target) for target in ids
                               for source in nodes[target]['depends_on'] + nodes[target]['completion_from']
                               if source in ids)
    assert displayed == nodes.keys(), 'Some proof nodes are missing from the diagrams'
    required_edges = {(source, key) for key, n in nodes.items()
                      for source in n['depends_on'] + n['completion_from']}
    assert displayed_edges == required_edges, 'Some dependencies are missing from the diagrams'
    assert {nodes[k]['article_label'] for k in proof['main_results']} == {'thm:main', 'thm:Rmain'}
    assert all(nodes[k]['status'] == 'Closed' for k in proof['main_results'])


def render_graph(proof, report):
    nodes = {n['id']: n for n in proof['nodes']}
    rows = report['article_rows']
    closed = sum(r['coverage'] == 'Closed' for r in rows)
    lines = [
        '# Article proof dependencies and formalization coverage', '',
        'The project formalizes the two main density theorems, **Theorems 3.1 and 4.1**, '
        'and the proved cases used in their arguments. The diagrams follow the paper\'s '
        'mathematical reductions, rather than Lean imports or implementation task IDs.', '',
        '**All current nodes are Closed.** Each status belongs to the exact clause '
        'written in its node. Closed requires a Lean kernel-checked proof with all auxiliary '
        'results formally proved and instantiated. It introduces no assumptions beyond '
        'those explicitly stated in the article (for example, positive viscosity). '
        'Only the standard logical axioms `propext`, `Classical.choice` and '
        '`Quot.sound` are permitted.', '',
        '**Solid arrows** are dependencies of the proved argument. Repeated nodes in '
        'different panels denote the same result.', '',
        'The periodic argument splits into a construction/density branch and a critical '
        'regularity/non-density branch. The whole-space argument has the same structure, '
        'with separate low-frequency estimates and two critical norms. Proposition 2.1 '
        'also includes the fixed-force H1-uniform restart and endpoint clauses on both '
        'domains.', '',
    ]
    for panel in proof['panels']:
        ids = set(panel['nodes'])
        lines += ['## ' + panel['title'], '', '```mermaid', 'flowchart TD']
        for key in panel['nodes']:
            n = nodes[key]
            title = '<br/>'.join(line for part in n['title'].split(': ') for line in textwrap.wrap(part, width=27)).replace('"', '&quot;')
            lines.append(f'  {key}["{title}<br/>{n["status"]}"]')
        for key in panel['nodes']:
            n = nodes[key]
            for source in n['depends_on']:
                if source in ids:
                    label = '|trajectory estimates|' if (source, key) == ('E46', 'T47') else ''
                    lines.append(f'  {source} -->{label} {key}')
            for source in n['completion_from']:
                if source in ids:
                    lines.append(f'  {source} -. remaining scope .-> {key}')
        lines += ['  classDef closed fill:#dcfce7,stroke:#15803d,color:#14532d;',
                  '  classDef mainResult stroke-width:4px;']
        members = [k for k in panel['nodes'] if nodes[k]['status'] == 'Closed']
        if members:
            lines.append('  class ' + ','.join(members) + ' closed;')
        main = [k for k in proof['main_results'] if k in ids]
        if main:
            lines.append('  class ' + ','.join(main) + ' mainResult;')
        lines += ['```', '']
    lines += ['## Coverage status', '',
              'All 26 numbered statements and the numbered remark are Closed. There are '
              'no split or unfinished article entries in the current inventory.']
    lines += ['', '## Proof locations', '',
              '| Node | Status | Exact scope and Lean source |', '|---|---|---|']
    for n in proof['nodes']:
        refs = '; '.join(f'[{Path(path).name}](../../{path})' for path in n['evidence'])
        lines.append(f'| {n["title"]} | {n["status"]} | {n["scope"]} {refs} |')
    lines += ['', '## Verification and source data', '',
              f'The article-level inventory has **{closed} Closed entries** '
              '(26 numbered statements and one numbered remark). This count is distinct '
              'from the number of clause-level nodes above. '
              f'The recorded kernel audit checks **{len(report["targets"])} declarations**, with '
              '**no forbidden axioms**. The permitted logical axioms are `propext`, '
              '`Classical.choice` and `Quot.sound`; the retained source scan has no admissions '
              'or custom axiom declarations.', '',
              'The graph is generated from [proof_graph.json](proof_graph.json). '
              '[RESULT_MAP.md](RESULT_MAP.md) supplies declaration locations, '
              '[CLOSURE_AUDIT.md](CLOSURE_AUDIT.md) records the input review, and '
              '[AXIOM_AUDIT.json](AXIOM_AUDIT.json) records the kernel results. '
              'The implementation registry in `tasks.json` is used for package checks, '
              'not as the reader-facing proof graph.', '',
              'Run `python3 experiments/check_formalization_plan.py` to regenerate this file; '
              '`python3 experiments/check_formalization_plan.py --check` verifies coverage '
              'agreement, acyclicity, displayed edges, source paths and the rule that a '
              'Closed proof cannot depend on an unfinished node.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Check generated graph without rewriting it')
    args = parser.parse_args()
    data = json.loads((PLAN / 'tasks.json').read_text())
    nodes = {n['id']: n for n in data['nodes']}
    assert len(nodes) == len(data['nodes']), 'Duplicate task IDs'
    order, active, done = [], set(), set()
    def visit(key):
        assert key in nodes, f'Missing task {key}'
        assert key not in active, f'Dependency cycle at {key}'
        if key in done:
            return
        active.add(key)
        for dep in nodes[key]['dependencies']:
            visit(dep)
        active.remove(key)
        done.add(key)
        order.append(key)
    for key, node in nodes.items():
        visit(key)
        for path in node['evidence']:
            assert (ROOT / path).is_file(), f'Missing blueprint evidence: {path}'
    for key in ['target', 'pdf']:
        assert (ROOT / data[key]).is_file(), data[key]
    article_labels = set()
    for source in (ROOT / 'paper/revised').rglob('*.tex'):
        article_labels.update(re.findall(r'\\label\{([^}]+)\}', source.read_text()))
    for node in nodes.values():
        assert set(node['manuscript_labels']) <= article_labels, node['id']
    for package in ['formalization', 'verification', 'vendor/NavierStokesAndEuler']:
        directory = ROOT / package
        lock = json.loads((directory / 'lake-manifest.json').read_text())
        for dep in lock['packages']:
            if dep['type'] == 'path':
                assert (directory / dep['dir'] / dep['configFile']).is_file(), dep
        assert (directory / 'lean-toolchain').is_file()
    modules, imports = {}, {}
    for package in ['formalization', 'verification', 'vendor/NavierStokesAndEuler', 'vendor/HeliCorgi']:
        directory = ROOT / package
        for parent, dirs, names in os.walk(directory):
            dirs[:] = [d for d in dirs if d not in ['.git', '.lake', '__pycache__']]
            for name in names:
                if not name.endswith('.lean') or name == 'lakefile.lean':
                    continue
                path = Path(parent) / name
                module = '.'.join(path.relative_to(directory).with_suffix('').parts)
                assert module not in modules, f'Duplicate module: {module}'
                modules[module] = path
                code = uncomment(path.read_text())
                imports[module] = [v for line in re.findall(r'^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)', code, re.M) for v in line.split()]
    missing = [(m, d) for m, deps in imports.items() for d in deps
               if d.startswith(('NSFormalization.', 'Formal.', 'FormalPatched.', 'NavierStokes.', 'Euler.', 'Contracts.', 'Bindings.', 'Tests.', 'TestSupport.')) and d not in modules]
    assert not missing, f'Missing local imports: {missing}'
    roots = json.loads((PLAN / 'entrypoints.json').read_text())
    expected_tests = {m for m in modules if m.startswith('Tests.')}
    assert set(roots['test_modules']) == expected_tests, 'Current test roots differ from retained tests'
    reached, pending = set(), roots['proof_modules'] + roots['test_modules']
    for module in pending:
        assert module in modules, f'Missing public root: {module}'
    while pending:
        module = pending.pop()
        if module in reached or module not in modules:
            continue
        reached.add(module)
        pending.extend(imports[module])
    unused = sorted(set(modules) - reached)
    assert not unused, f'Unreferenced Lean modules: {unused}'
    admissions = [(m, i) for m, path in modules.items()
                  for i, line in enumerate(uncomment(path.read_text()).splitlines(), 1)
                  if re.search(r'\b(?:sorry|admit|axiom)\b', line)]
    assert not admissions, f'Admissions or custom axioms in retained sources: {admissions}'
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    forbidden = [p for p in tracked if p and (ROOT / p).exists() and
                 (any(x in Path(p).parts for x in ['.lake', '.elan', '__pycache__']) or
                  Path(p).suffix in ['.olean', '.ilean', '.o', '.trace', '.pyc'])]
    assert not forbidden, f'Tracked build artifacts: {forbidden}'
    report = None
    audit_path = PLAN / 'AXIOM_AUDIT.json'
    if audit_path.exists():
        report = json.loads(audit_path.read_text())
        fingerprints = {}
        for directory in ['formalization', 'verification', 'vendor']:
            for path in (ROOT / directory).rglob('*'):
                if not path.is_file() or any(part in path.parts for part in ['.git', '.lake', '__pycache__']):
                    continue
                if path.suffix == '.lean' or path.name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'LICENSE']:
                    fingerprints[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        digest = hashlib.sha256(json.dumps(fingerprints, sort_keys=True).encode()).hexdigest()
        assert digest == report['source_tree_sha256'], 'Source changed: rerun the article axiom audit'
        assert not report['source_tokens'], 'Audit recorded source admissions or custom axioms'
        assert all(not entry['unexpected_axioms'] for entry in report['targets']), 'Audit recorded forbidden axioms'
        guide_coverage = dict(re.findall(r'\\mapped\{[^}]+\}\{([^}]+)\}\s*&\s*\\coverage\{([^}]+)\}',
                                       (ROOT / 'paper/formalization_guide.tex').read_text()))
        assert {row['label']: row['coverage'] for row in report['article_rows']} == guide_coverage, 'Audit coverage differs from guide'
    proof = json.loads((PLAN / 'proof_graph.json').read_text())
    validate_proof_graph(proof, report)
    rendered = render_graph(proof, report)
    if args.check:
        assert (PLAN / 'DEPENDENCY_GRAPH.md').read_text() == rendered, 'Regenerate the dependency graph'
    else:
        (PLAN / 'DEPENDENCY_GRAPH.md').write_text(rendered)
    guide = (ROOT / 'paper/formalization_guide.tex').read_text()
    labels = {label for _, label in re.findall(r'\\mapped\{([^}]+)\}\{([^}]+)\}', guide)}
    result_map = (PLAN / 'RESULT_MAP.md').read_text()
    mapped = set(re.findall(r'`((?:thm|prop|lem|cor|rem):[^`]+)`', result_map))
    assert labels == mapped and len(labels) == 27, 'Blueprint result map differs from guide'
    print(f'Blueprint: {len(proof["nodes"])} proof nodes, 27 article/guide mappings; {len(modules)} source modules; local imports and package paths resolve.')
    print('Static packaging checks only; no Lean build or mathematical certification.')

if __name__ == '__main__':
    main()
