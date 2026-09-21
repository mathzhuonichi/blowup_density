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


def changed_paths(base_ref, *, root=ROOT):
    base = subprocess.run(['git', 'rev-parse', '--verify', '--quiet',
                           f'{base_ref}^{{commit}}'], cwd=root,
                          stdout=subprocess.DEVNULL, check=False)
    if base.returncode:
        # Initial pushes and rewritten history may have no available base.
        # Check every committed module instead of silently skipping coverage.
        print('Base commit unavailable; selecting all committed Lean modules.', flush=True)
        command = ['git', 'ls-tree', '-r', '--name-only', '-z', 'HEAD']
    else:
        command = ['git', 'diff', '--name-only', '-z', '--diff-filter=ACMRT',
                   base_ref, 'HEAD', '--']
    return [name for name in subprocess.check_output(command, cwd=root, text=True).split('\0')
            if name]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-ref', required=True)
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    modules = targets(changed_paths(args.base_ref))
    print('Changed Lean modules:', ', '.join(modules) or 'none', flush=True)
    if modules and not args.dry_run:
        subprocess.run(['lake', 'build', *modules], cwd=ROOT / 'verification', check=True)


if __name__ == '__main__':
    main()
