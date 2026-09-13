#!/usr/bin/env python3
"""Regression tests for append-only specifications and stable acceptance tests."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from check_contracts import check, check_compatibility, contract_import_allowed
from build_changed_lean import targets


class ChangedModuleSelection(unittest.TestCase):
    def test_unimported_new_proof_is_still_selected(self):
        self.assertEqual(targets(['formalization/NSFormalization/Paper3/NewProof.lean',
                                  'verification/Bindings/NewProof.lean', 'README.md']),
                         ['Bindings.NewProof', 'NSFormalization.Paper3.NewProof'])

    def test_incompatible_vendor_is_not_silently_skipped(self):
        with self.assertRaisesRegex(ValueError, '4.32.1'):
            targets(['vendor/HeliCorgi/Formal/NewProof.lean'])


class ContractImportBoundary(unittest.TestCase):
    def test_upstream_and_canonical_conventions_are_allowed(self):
        for module in ['Mathlib', 'Lean', 'Init', 'Mathlib.Data.Real.Basic',
                       'Contracts.V1.Thresholds',
                       'NavierStokes.R3.ProblemStatement',
                       'NSFormalization.Paper3.GridGeometry',
                       'NSFormalization.Paper3.AngularFourierDilation']:
            self.assertTrue(contract_import_allowed(module), module)

    def test_arbitrary_local_implementation_is_still_rejected(self):
        for module in ['NSFormalization', 'NSFormalization.Source.Insertion',
                       'NSFormalization.Paper3.RealAdmissibleForce',
                       'NSFormalization.Paper1.InsertionEnergy', 'Bindings.Thresholds',
                       'Euler.EulerProof']:
            self.assertFalse(contract_import_allowed(module), module)

    def test_vendor_is_an_exact_list_not_a_package_prefix(self):
        for module in ['NavierStokes.ComparatorTheorem', 'NavierStokes.ProblemStatement',
                       'NavierStokes.R3.CompactEnergy']:
            self.assertFalse(contract_import_allowed(module), module)

    def test_root_names_match_exactly_or_with_a_dot(self):
        for module in ['MathlibExtras.Tactic', 'LeanFoo.Bar', 'Initialize.X', 'Contracts']:
            self.assertFalse(contract_import_allowed(module), module)


class ContractImportBoundaryEndToEnd(unittest.TestCase):
    """Drive `check()` itself, so a refactor that stops consulting the predicate fails."""

    def tree(self, probe_import):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        item = {'id': 'probe.v1', 'parent_task': 'R41', 'version': 1,
                'specification': 'verification/Contracts/V1/Thresholds.lean',
                'binding_module': 'Bindings.Thresholds', 'test_module': 'Tests.Thresholds',
                'declaration': 'Probe.checked', 'scope': 'Probe only.', 'enabled': True}
        for path, text in [
            ('lean-toolchain', 'leanprover/lean4:probe\n'),
            ('verification/lean-toolchain', 'leanprover/lean4:probe\n'),
            ('formalization/lean-toolchain', 'leanprover/lean4:probe\n'),
            ('formalization/blueprint/tasks.json', json.dumps({'nodes': [{'id': 'R41'}]})),
            ('verification/contracts.json',
             json.dumps({'schema_version': 1, 'contracts': [item]})),
            ('verification/Contracts/V1/Thresholds.lean', 'import Mathlib.Data.Real.Basic\n'),
            ('verification/Bindings/Thresholds.lean', 'import Contracts.V1.Thresholds\n'),
            ('verification/Tests/Thresholds.lean', 'import Bindings.Thresholds\n'),
            ('verification/Contracts/V1/Probe.lean', f'import {probe_import}\n'),
        ]:
            p = root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        return root

    def test_check_rejects_a_non_allowlisted_local_import(self):
        root = self.tree('NSFormalization.Paper3.RealAdmissibleForce')
        with self.assertRaises(AssertionError) as caught:
            check(root=root)
        self.assertIn('NSFormalization.Paper3.RealAdmissibleForce', str(caught.exception))
        self.assertIn('Implementation-dependent specification', str(caught.exception))

    def test_check_accepts_a_canonical_convention_import(self):
        result = check(root=self.tree('NSFormalization.Paper3.GridGeometry'))
        self.assertEqual(result['registered_contracts'], 1)


class CompatibilityPolicy(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.item = {'id': 'test.v1', 'version': 1,
                     'specification': 'verification/Contracts/V1/Test.lean',
                     'binding_module': 'Bindings.Test', 'test_module': 'Tests.Test',
                     'declaration': 'Tests.test', 'enabled': True}
        for path, text in [
            (self.item['specification'], 'def FixedStatement := True\n'),
            ('verification/Tests/Test.lean', 'example : True := trivial\n'),
            ('verification/Bindings/Test.lean', '-- original binding\n'),
            ('verification/contracts.json', json.dumps({'contracts': [self.item]})),
        ]:
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Contract Tests', '-c', 'user.email=tests@example.invalid',
                 'commit', '-qm', 'Baseline')

    def git(self, *args):
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def check(self, items=None):
        check_compatibility(self.root, 'HEAD', items if items is not None else [self.item])

    def test_binding_refactor_is_allowed(self):
        (self.root / 'verification/Bindings/Test.lean').write_text('-- reorganized implementation\n')
        self.check()

    def test_existing_specification_cannot_change(self):
        (self.root / self.item['specification']).write_text('def FixedStatement := False\n')
        with self.assertRaisesRegex(AssertionError, 'Changed stable specification'):
            self.check()

    def test_existing_acceptance_test_cannot_change(self):
        (self.root / 'verification/Tests/Test.lean').write_text('-- test silently removed\n')
        with self.assertRaisesRegex(AssertionError, 'Changed stable acceptance'):
            self.check()

    def test_contract_cannot_be_deleted_or_disabled(self):
        with self.assertRaisesRegex(AssertionError, 'Removed contract'):
            self.check([])
        with self.assertRaisesRegex(AssertionError, 'enabled'):
            self.check([{**self.item, 'enabled': False}])

    def test_new_version_does_not_replace_old_version(self):
        path = self.root / 'verification/Contracts/V2/Test.lean'
        path.parent.mkdir(parents=True)
        path.write_text('def NewStatement := True\n')
        self.check([self.item, {**self.item, 'id': 'test.v2', 'version': 2,
                              'specification': str(path.relative_to(self.root))}])


if __name__ == '__main__':
    unittest.main()
