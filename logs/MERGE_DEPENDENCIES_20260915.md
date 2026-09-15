# Dependency integration: PRs #161–#170 (2026-09-15)

## Integration scope

At the owner's request, the existing dependency PRs were merged through their
original parent branches, preserving commit ancestry. The A01 chain was merged
in the order #170, #169, #167, #164, #162. The C01/R43 chain was merged in the
order #168, #166, #165, #163. PR #161 delivers the combined tree to `main`.
The collaboration documentation from PR #171 is retained.

The common proof base was `0b8e5e43e277bf4aa480d72204441beaba63e739`. The
pre-integration main snapshot was `95b4ae2b1a4cc0fc92782b7d5dab0f6ac9c387c6`.
The two proof chains were combined at `586b40f1dafeac5b01bc6ca5801906dd07a8545a`.

## Conflict resolution

Conflicts affected only `PLAN.md`, `NEXT_SESSION.md`, and `logs/AGENT_RUNS.csv`.
Both branches' dated progress and verification records were retained. The final
plan preserves PR #171's dashboard and package layout together with PR #170's
A01 implementation plan. Current integration notes explain that old pending-PR
labels and sibling-branch exclusions are historical. The collaborator handoff
points readers to the integrated plan before assigning new work.

All integrated Lean files retain exactly the blob hashes supplied by the source
PRs. No proof, frozen specification, acceptance test, or dependency was manually
edited during conflict resolution. C01 V4 is an additive contract from PR #166.

## Checks performed for this integration

A separate local review repository was materialized through the GitHub API after
ordinary Git transport repeatedly timed out. All 3,907 file modes and blob hashes
of the baseline were checked against GitHub's tree listing. The merged changes
were applied using their exact GitHub blobs, with explicit document resolutions.
The user's original checkout and its untracked audit note were left untouched.

| Check | Observed result |
| --- | --- |
| `make check` | Exit 0: plan, contract architecture, 13 policy tests, work queue |
| `python3 experiments/check_contracts.py --base-ref baseline-main` | Exit 0; frozen contracts and registered tests preserved |
| `git diff --cached --check` | Exit 0 |
| Integrated Lean blob comparison | Exact matches to source PR blobs |
| Contract registry | 27 registered contracts |

`baseline-main` is the local review commit whose files exactly match the
pre-integration main snapshot above; it is not a new upstream branch.
The final GitHub resolution tree is also compared with the staged local tree
before the source branch is advanced.

## Verification limits and remaining mathematics

The individual PR validation records report earlier successful Lean builds,
consumer and transitive-axiom checks, contract tests, and mutation tests. These
records were inspected as prior evidence. This integration did not rerun Lean
compilation, `lake test`, or Lean mutation tests on the combined tree.

All ten original PR architecture-job annotations were checked through GitHub.
They report that the jobs could not start because recent account payments failed
or the spending limit needed increasing; Lean jobs were skipped. Those failures
are neither Lean proof failures nor successful cloud validation. No repository
protection settings were changed.

C01 V4 and the R43 maximal-family endpoint estimate are included. The latter
retains its absorption premise. The full A01 classical constructor, required
critical estimates, and unconditional continuation remain open. Integration
does not certify completion of the manuscript's Section 4.

The dated source reports remain the provenance for their original proof claims.
Current merge status is given by GitHub, not by historical open-PR labels in
those reports.
