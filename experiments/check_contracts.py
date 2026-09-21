#!/usr/bin/env python3
"""Check contract registration, dependency boundaries for the current publication."""
import argparse
import json
import os
from pathlib import Path
import re
from check_formalization_plan import uncomment

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = 'verification/contracts.json'

# A versioned specification stays independent of this project's *proofs*. It may
# import Mathlib, Lean core and another contract. The root names carry no
# trailing dot of their own, so they are matched exactly or with a dot, and
# `MathlibExtras.X` or `Initialize.X` do not slip through.
CONTRACT_IMPORT_ROOTS = frozenset({'Mathlib', 'Lean', 'Init'})
CONTRACT_IMPORT_PREFIXES = ('Mathlib.', 'Lean.', 'Init.', 'Contracts.')

# A specification may additionally name a module that fixes a *definition-level
# convention* the whole project treats as canonical, and only from this explicit
# list, matched by exact module name: one pinned upstream module under `vendor/`
# for the equation, fields and operators; and, locally, the manuscript's angular
# Fourier transform and its distributional realization, the real-Sobolev and
# Euclidean-vector carriers, the (0, infinity) force-time measure, and grid
# geometry. Every other module, upstream or local, is an implementation
# dependency and stays rejected. The list governs *direct* imports, not the
# transitive closure. Extending it is a reviewed policy change, not a routine
# edit.
CONTRACT_CANONICAL_MODULES = frozenset({
    'NavierStokes.R3.ProblemStatement',
    'NSFormalization.Source.FourierConvention',
    'NSFormalization.Source.RealSobolev',
    'NSFormalization.Paper3.AngularFourierDilation',
    'NSFormalization.Paper3.RealVectorPositiveDensity',
    'NSFormalization.Paper3.PositiveTemporalDensity',
    'NSFormalization.Paper3.GridGeometry',
})


def contract_import_allowed(module):
    """Whether a versioned specification may directly import `module`."""
    return (module in CONTRACT_IMPORT_ROOTS
            or module.startswith(CONTRACT_IMPORT_PREFIXES)
            or module in CONTRACT_CANONICAL_MODULES)


def check(root=ROOT):
    assert (root / 'lean-toolchain').read_text() == (root / 'verification/lean-toolchain').read_text()
    assert (root / 'formalization/lean-toolchain').read_text() == (root / 'verification/lean-toolchain').read_text()
    data = json.loads((root / REGISTRY).read_text())
    assert data['schema_version'] == 1
    contracts = data['contracts']
    assert contracts, 'At least one actual acceptance contract is required'
    ids = [c['id'] for c in contracts]
    assert len(ids) == len(set(ids)), 'Duplicate contract IDs'
    tasks = {n['id'] for n in json.loads((root / 'formalization/blueprint/tasks.json').read_text())['nodes']}
    modules, imports = {}, {}
    for package in ['verification', 'formalization', 'vendor/NavierStokesAndEuler', 'vendor/HeliCorgi']:
        directory = root / package
        for parent, dirs, names in os.walk(directory):
            dirs[:] = [d for d in dirs if d not in ['.lake', '.git', '__pycache__']]
            for name in names:
                if not name.endswith('.lean') or name == 'lakefile.lean':
                    continue
                p = Path(parent) / name
                module = '.'.join(p.relative_to(directory).with_suffix('').parts)
                assert module not in modules, f'Duplicate module: {module}'
                modules[module] = p
                code = uncomment(p.read_text())
                imports[module] = [v for line in re.findall(
                    r'^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)', code, re.M) for v in line.split()]
                if module.startswith('Contracts.'):
                    assert not re.search(r'\b(?:axiom|sorry|admit)\b', code), p
                    forbidden = [x for x in imports[module] if not contract_import_allowed(x)]
                    assert not forbidden, (
                        f'Implementation-dependent specification: {p}: {forbidden}')
    registered_tests = set()
    closures = {}
    for contract in contracts:
        assert contract['enabled'] is True, f'Disabled acceptance test: {contract["id"]}'
        assert contract['parent_task'] in tasks
        assert re.fullmatch(r'[A-Za-z0-9_.-]+', contract['id'])
        assert contract['scope'].strip()
        spec = root / contract['specification']
        assert spec.is_file()
        assert f'/V{contract["version"]}/' in contract['specification']
        assert contract['binding_module'].startswith('Bindings.')
        assert contract['test_module'].startswith('Tests.')
        assert contract['binding_module'] in modules
        assert contract['test_module'] in modules
        registered_tests.add(contract['test_module'])
        seen = set()
        def visit(module):
            if module in seen:
                return
            seen.add(module)
            assert module not in ['NSFormalization', 'NSFormalization.Paper1.BoundaryCorollary']
            assert not module.startswith(('NSFormalization.Citations.', 'ComparatorChallenges.'))
            for dependency in imports.get(module, []):
                if dependency.startswith(('Mathlib', 'Lean', 'Init')):
                    continue
                assert dependency in modules, f'Missing source import: {dependency}'
                visit(dependency)
        visit(contract['test_module'])
        assert contract['binding_module'] in seen
        assert '.'.join(spec.relative_to(root / 'verification').with_suffix('').parts) in seen
        closures[contract['id']] = sorted(seen)
    assert registered_tests == {m for m in modules if m.startswith('Tests.')}, (
        'Every acceptance test must be registered, and every registration must exist')
    return {'registered_contracts': len(contracts), 'closures': closures,
            'scope': 'Architecture checks only; run lake test for Lean type and axiom checks.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--summary', action='store_true')
    args = parser.parse_args()
    result = check()
    if args.summary:
        result.pop('closures')
    print(json.dumps(result, indent=2))
