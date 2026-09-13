# Source-only formalization snapshot

The copied source is now supported by a separate
[versioned acceptance-test package](../verification/README.md).
Follow [CONTRIBUTING.md](../CONTRIBUTING.md) for ongoing development.
Historical source hashes are provenance, not a restriction on future proof edits.

The active target is Section 4 of the merged
[blowup_density manuscript](../paper/blowup_density.tex), formerly Paper 3.
Start with the [proof task tree](blueprint/README.md), not the legacy umbrella
or the source archive's historical Paper 1 campaign.

This directory preserves 340 Lean source files from the existing local
formalization. No Lean proof or import was edited in this migration. The only
changes to copied package configuration are the local dependency paths in
`lakefile.toml` and `lake-manifest.json`, now pointing to
`../vendor/NavierStokesAndEuler`.

The two reusable upstream source packages are:

- [OpenAI](../vendor/NavierStokesAndEuler/): Lean 4.34.0-rc2, including both
  `NavierStokes/` and `Euler/`, since existing local proofs import both libraries.
- [HeliCorgi](../vendor/HeliCorgi/): Lean 4.32.1, including its complete `Formal/`
  source tree. This remains a separate Lake project until the selected imports
  are ported and checked against the OpenAI environment.

Both packages retain their license and dependency lockfile. Mathlib and its
dependencies are pinned in those lockfiles, not copied as caches. No `.lake`,
compiler installation, `.git`, binary artifact, numerical experiment output,
historical build log, or legacy build wrapper was copied from the source projects.
The standalone HeliCorgi package does not yet provide imports to this package.

## Verification boundary

Neither paper nor the merged manuscript is fully certified. This migration
performed static inspection and hash/import checks; it did not run a fresh
Lean build or a transitive kernel axiom audit. The copied legacy umbrella
imports `Paper1/BoundaryCorollary.lean`, whose theorem
`exists_interior_noSlip_insertion` contains `sorry` at line 90. The schematic
`Citations/` modules also contain explicit axioms, although none is reachable
from that umbrella. They are preserved historical source, not accepted inputs
to the new proof tree. See the [audit and reuse record](blueprint/EXTERNAL_REUSE.md).

## Reproduce the packaging checks

From the repository root:

```sh
python3 experiments/check_formalization_plan.py
```

This reports changes from the historical source hashes and verifies relative
dependency paths, copied import closure, exclusion of tracked caches, task
acyclicity, evidence paths and all 34 original result occurrences. Ignored local
build caches are allowed. Add `--snapshot` to require historical byte identity,
or `--check` to validate generated documentation without rewriting files.
The default invocation regenerates the task graph and result map. A successful
check means the package and plan are consistent, not that their proofs are complete.

For a future build session, use the package's pinned toolchain with standard
`lake` commands. Dependencies must first be restored from its lockfile. Build
selected modules and audit actual final theorem declarations; the old umbrella
is not a clean certification entry point. Do not use HeliCorgi's 4.32.1 lockfile
inside the 4.34.0-rc2 package.
