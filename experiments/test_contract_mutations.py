#!/usr/bin/env python3
"""Prove that the acceptance harness rejects realistic regressions."""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / 'verification'
IMPORTS = '''import Contracts.V1.Thresholds
import Bindings.Thresholds
import TestSupport.Axioms
open BlowupDensity
noncomputable section
'''
CASES = {
    'implementation_refactor': (True, '''
def reorganized : Contracts.V1.ThresholdAPI :=
  let unchangedPublicAPI := Bindings.thresholds
  unchangedPublicAPI
run_cmd TestSupport.checkAxioms ``reorganized
'''),
    'admitted_proof': (False, '''
def missing : Contracts.V1.ThresholdAPI := by sorry
run_cmd TestSupport.checkAxioms ``missing
'''),
    'extra_axiom': (False, '''
axiom fabricated : Contracts.V1.ThresholdAPI
def apparentlyImplemented : Contracts.V1.ThresholdAPI := fabricated
run_cmd TestSupport.checkAxioms ``apparentlyImplemented
'''),
    'weakened_hypothesis': (False, '''
def weaker : ∀ s : ℝ, s < -2 →
    ∃ r : ℝ, -3 / 2 < r ∧ r < -1 / 2 ∧ s < r := by
  intro s hs
  exact Bindings.thresholds.negativeIndex s (lt_trans hs (by norm_num))
def exactNegative : ∀ s : ℝ, s < -1 / 2 →
    ∃ r : ℝ, -3 / 2 < r ∧ r < -1 / 2 ∧ s < r := weaker
'''),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    if not args.skip_build:
        subprocess.run(['lake', 'test'], cwd=PACKAGE, check=True)
    parent = PACKAGE / '.lake'
    parent.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='contract-mutations-', dir=parent) as directory:
        for name, (success, body) in CASES.items():
            path = Path(directory) / 'Mutation.lean'
            path.write_text(IMPORTS + body)
            result = subprocess.run(['lake', 'env', 'lean', '--root=' + directory, str(path)],
                                    cwd=PACKAGE, capture_output=True, text=True)
            output = result.stdout + result.stderr
            assert (result.returncode == 0) == success, f'{name}: unexpected outcome\n{output}'
            if name in ['admitted_proof', 'extra_axiom']:
                assert 'forbidden axioms' in output, f'{name}: failed for the wrong reason\n{output}'
            if name == 'weakened_hypothesis':
                assert 'type mismatch' in output.lower(), f'{name}: wrong failure\n{output}'
            print(f'{name}: {"accepted" if success else "rejected as required"}')
    print('Mutation suite passed. This is an infrastructure check, not a PDE proof.')


if __name__ == '__main__':
    main()
