#!/usr/bin/env python3
"""Compile changed Lean modules even if no acceptance test imports them yet."""
import argparse
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def targets(paths):
    result = []
    for name in paths:
        path = Path(name)
        if path.suffix != '.lean' or path.name == 'lakefile.lean':
            continue
        for prefix in ['verification/', 'formalization/', 'vendor/NavierStokesAndEuler/', 'vendor/HeliCorgi/']:
            if name.startswith(prefix):
                result.append(name.removeprefix(prefix).removesuffix('.lean').replace('/', '.'))
                break
    return sorted(set(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-ref', required=True)
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    subprocess.run(['git', 'rev-parse', '--verify', f'{args.base_ref}^{{commit}}'], cwd=ROOT,
                   stdout=subprocess.DEVNULL, check=True)
    names = subprocess.check_output(['git', 'diff', '--name-only', '--diff-filter=ACMRT',
                                     args.base_ref, 'HEAD', '--'], cwd=ROOT, text=True).splitlines()
    modules = targets(names)
    print('Changed Lean modules:', ', '.join(modules) or 'none', flush=True)
    if modules and not args.dry_run:
        subprocess.run(['lake', 'build', *modules], cwd=ROOT / 'verification', check=True)


if __name__ == '__main__':
    main()
