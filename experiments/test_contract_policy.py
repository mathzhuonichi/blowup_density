#!/usr/bin/env python3
"""Regression tests for current contract import boundaries and module selection."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from check_contracts import check, contract_import_allowed
from build_changed_lean import targets
from check_formalization_plan import ROOT, validate_proof_graph


class ArticleProofCoverage(unittest.TestCase):
    def setUp(self):
        plan = ROOT / 'formalization/blueprint'
        self.proof = json.loads((plan / 'proof_graph.json').read_text())
        self.report = json.loads((plan / 'AXIOM_AUDIT.json').read_text())

    def test_proved_cases_can_support_closed_downstream_results(self):
        validate_proof_graph(self.proof, self.report)

    def test_unfinished_clause_cannot_become_a_main_theorem_input(self):
        # Recolor one existing input of the main theorem as unfinished; the
        # graph must then refuse the Closed main theorem. (Formulated on a
        # current dependency rather than a fixed Partial node id so that the
        # test survives the closure of the remaining Partial scopes.)
        changed = copy.deepcopy(self.proof)
        nodes = {n['id']: n for n in changed['nodes']}
        nodes[nodes['T31']['depends_on'][0]]['status'] = 'Partial'
        with self.assertRaisesRegex(AssertionError, 'Closed proof depends on Partial input'):
            validate_proof_graph(changed, self.report)

    def test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial(self):
        # Every clause node of a statement is Closed while the recorded kernel
        # audit still reports the whole statement as Partial: the validator must
        # refuse. (Formulated against the audit row rather than a fixed clause
        # node id so that the test survives the closure of that clause.)
        report = copy.deepcopy(self.report)
        closed_rows = [r for r in report['article_rows'] if r['coverage'] == 'Closed']
        self.assertTrue(closed_rows)
        closed_rows[0]['coverage'] = 'Partial'
        with self.assertRaisesRegex(AssertionError, 'disagrees with whole-statement coverage'):
            validate_proof_graph(self.proof, report)

class ChangedModuleSelection(unittest.TestCase):
    def test_unimported_new_proof_is_still_selected(self):
        self.assertEqual(targets(['formalization/NSFormalization/Paper3/NewProof.lean',
                                  'verification/Bindings/NewProof.lean', 'README.md']),
                         ['Bindings.NewProof', 'NSFormalization.Paper3.NewProof'])

    def test_current_vendor_module_is_selected(self):
        self.assertEqual(targets(['vendor/HeliCorgi/Formal/NewProof.lean']), ['Formal.NewProof'])


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


if __name__ == '__main__':
    unittest.main()
