#!/usr/bin/env python3
"""Audit the guide's Lean declarations in separate environments, on Linux.

Run with the pinned elan toolchain available:
  python3 experiments/audit_article_axioms.py --build --output-dir /tmp/article-audit

Declarations are checked in their existing import environments. This checks
transitive axioms; article coverage and theorem inputs require the separate
statement review recorded in formalization/blueprint/CLOSURE_AUDIT.md.
"""
import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import re
import subprocess
from check_formalization_plan import uncomment

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXTRA = [
    ('NSFormalization.Section4.A04.RestartFixedForce', 'NSFormalization.Section4.A04.classical_hasSmoothSobolevPath'),
    ('NavierStokes.R3ActualCandidate', 'NavierStokes.R3CompactCandidate.selected_compact_candidate'),
    ('NavierStokes.R3FiniteEnergyComparison', 'NavierStokes.ComparatorBridge.compact_candidate_excludes_global_solution'),
    ('NavierStokes.ComparatorR3Theorem', 'NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3'),
    ('NSFormalization.Section3.T23.BoundaryIntegration', 'NSFormalization.Section3.T23.ibp_of_isOpen_isBounded'),
    ('NSFormalization.Section3.T23.NoSlipUniqueness', 'NSFormalization.Section3.T23.noSlip_uniqueness'),
]
HELPER = '''import Lean
open Lean Elab Command
def auditDeclaration (name : Name) : CommandElabM Unit := do
  let axioms ← Lean.collectAxioms name
  logInfo ("AUDIT_JSON " ++ (Json.mkObj [("declaration", toJson name.toString),
    ("axioms", toJson (axioms.toList.map Name.toString))]).compress)
'''


def full_name(path, line, declaration):
    stack = []
    for text in path.read_text().splitlines()[:line - 1]:
        match = re.match(r'^namespace\s+(\S+)', text)
        if match:
            stack.append(('namespace', match[1]))
            continue
        match = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', text)
        if match:
            stack.append(('section', match[1]))
            continue
        if re.match(r'^end(?:\s+(\S+))?\s*$', text) and stack:
            stack.pop()
    return '.'.join([name for kind, name in stack if kind == 'namespace'] + [declaration])


def source_location(name, line, declaration, kind):
    path = Path('formalization/NSFormalization' if name.startswith('F/') else
                'verification/Bindings') / (name[2:] + '.lean')
    return {'declaration': full_name(ROOT / path, int(line), declaration),
            'module': str(path).split('/', 1)[1].removesuffix('.lean').replace('/', '.'),
            'path': str(path), 'line': int(line), 'kind': kind}


def targets():
    guide = (ROOT / 'paper/formalization_guide.tex').read_text()
    pattern = r'\\source\{([^}]+)\}\{(\d+)\}\{([^}]+)\}\{(theorem|def)\}'
    entries = [source_location(*m) for m in re.findall(pattern, guide)]
    by_name = {entry['declaration']: entry for entry in entries}
    for module, declaration in EXTRA:
        if declaration in by_name:
            continue
        path = ('vendor/NavierStokesAndEuler/' if module.startswith('NavierStokes.')
                else 'formalization/') + module.replace('.', '/') + '.lean'
        by_name[declaration] = {'declaration': declaration, 'module': module,
                                'path': path, 'kind': 'theorem'}
    rows = []
    for match in re.finditer(r'\\mapped\{([^}]+)\}\{([^}]+)\}(.*?)(?=\\mapped\{|\\end\{longtable\})', guide, re.S):
        kind, label, body = match.groups()
        rows.append({'kind': kind, 'label': label,
                     'coverage': re.search(r'\\coverage\{([^}]+)\}', body)[1],
                     'declarations': [source_location(*m)['declaration']
                                      for m in re.findall(pattern, body)]})
    result_map = (ROOT / 'formalization/blueprint/RESULT_MAP.md').read_text()
    for row in rows:
        match = re.search(r'\| ' + re.escape(row['kind']) + r' ([^|]+) \| `' + re.escape(row['label']) + r'`', result_map)
        assert match, row['label']
        row['number'] = match[1].strip()
    return list(by_name.values()), rows


def import_groups(entries):
    """Cover target declarations by existing, individually valid import closures."""
    imports = {}
    for package in ['formalization', 'verification', 'vendor/NavierStokesAndEuler', 'vendor/HeliCorgi']:
        directory = ROOT / package
        for path in directory.rglob('*.lean'):
            if '.lake' in path.parts or path.name == 'lakefile.lean':
                continue
            module = '.'.join(path.relative_to(directory).with_suffix('').parts)
            imports[module] = [word for line in re.findall(
                r'^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)',
                uncomment(path.read_text()), re.M) for word in line.split()]
    def closure(root):
        seen, pending = set(), [root]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            pending.extend(imports.get(module, []))
        return seen
    candidates = {entry['module']: closure(entry['module']) for entry in entries}
    remaining = {entry['declaration']: entry for entry in entries}
    groups = {}
    while remaining:
        best = max(candidates, key=lambda module: sum(
            entry['module'] in candidates[module] for entry in remaining.values()))
        selected = [entry for entry in remaining.values() if entry['module'] in candidates[best]]
        assert selected
        groups[best] = selected
        for entry in selected:
            remaining.pop(entry['declaration'])
    return groups


def source_snapshot():
    files, tokens = {}, []
    for directory in ['formalization', 'verification', 'vendor']:
        for path in (ROOT / directory).rglob('*'):
            if not path.is_file() or any(p in path.parts for p in ['.git', '.lake', '__pycache__']):
                continue
            relative = str(path.relative_to(ROOT))
            if path.suffix == '.lean' or path.name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'LICENSE']:
                files[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
            if path.suffix == '.lean':
                for line, text in enumerate(uncomment(path.read_text()).splitlines(), 1):
                    if re.search(r'\b(sorry|admit|axiom)\b', text):
                        tokens.append({'path': relative, 'line': line, 'text': text.strip()})
    digest = hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()
    return digest, files, sorted(tokens, key=lambda row: (row['path'], row['line']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--workers', type=int, choices=[1, 2], default=2)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    entries, rows = targets()
    digest, files, tokens = source_snapshot()
    groups = import_groups(entries)
    lake = ['lake', '-d', str(ROOT / 'verification')]
    if args.build:
        with (output / 'build.log').open('w') as log:
            subprocess.run(lake + ['build', *sorted(groups)], stdout=log,
                           stderr=subprocess.STDOUT, check=True)
    def run(item):
        module, declarations = item
        code = 'import ' + module + '\n' + HELPER
        for entry in declarations:
            name = entry['declaration']
            code += f'\nrun_cmd auditDeclaration ``{name}\n#check {name}\n'
        path = output / (module + '.lean')
        path.write_text(code)
        result = subprocess.run(lake + ['env', 'lean', str(path)], capture_output=True, text=True)
        log = result.stdout + result.stderr
        (output / (module + '.log')).write_text(log)
        actual = [json.loads(line.removeprefix('AUDIT_JSON '))
                  for line in log.splitlines() if line.startswith('AUDIT_JSON ')]
        expected = {entry['declaration'] for entry in declarations}
        assert result.returncode == 0 and {entry['declaration'] for entry in actual} == expected, module
        print(f'{module}: {len(actual)} declarations checked', flush=True)
        return actual
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        actual = [entry for group in executor.map(run, groups.items()) for entry in group]
    assert source_snapshot()[0] == digest, 'Source tree changed during the audit'
    axioms = {entry['declaration']: sorted(entry['axioms']) for entry in actual}
    for entry in entries:
        entry['axioms'] = axioms[entry['declaration']]
        entry['unexpected_axioms'] = sorted(set(entry['axioms']) - ALLOWED)
    report = {'schema_version': 1, 'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'source_tree_sha256': digest, 'source_file_count': len(files),
              'allowed_axioms': sorted(ALLOWED), 'targets': entries, 'article_rows': rows,
              'source_tokens': tokens,
              'scope': 'Kernel transitive-axiom audit of the listed declarations; not an audit of all manuscript semantics or all source modules.'}
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    (output / 'source-hashes.json').write_text(json.dumps(files, indent=2, sort_keys=True) + '\n')
    unexpected = [entry for entry in entries if entry['unexpected_axioms']]
    print(f'{len(entries)} declarations; {len(rows)} article entries; {len(unexpected)} forbidden-axiom results')
    raise SystemExit(bool(unexpected))


if __name__ == '__main__':
    main()
