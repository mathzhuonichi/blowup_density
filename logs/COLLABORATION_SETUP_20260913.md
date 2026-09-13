# Two-person collaboration and durable test interfaces

Date: 13 September 2026.

## Access

The repository remains private. GitHub account `erenup`, identified by the
user's screenshot and verified against the public profile, was invited with
write permission. GitHub returned a pending repository invitation. The invitee
must accept it before private-repository access becomes available. No shared
credential, public visibility change or administrator role was introduced.

## Architecture

Added contribution guidance, a 30-item owned work queue, generated task cards,
PR and issue templates, CODEOWNERS and a separate versioned Lean verification
package. Research/specification work is distinct from implementation and
assembly; a proof task cannot enter the executable queue without a registered
concrete acceptance contract.

The first active contract, `R41.threshold_arithmetic`, checks six arithmetic
obligations against the existing Paper 3 lemmas. It does not certify any PDE
statement. Other task cards explicitly request specification work rather than
presenting assumed interfaces as proofs. Stable specification and test files
are preserved relative to a PR's base commit; implementations can be refactored
behind the binding layer.

The daily plan checker now reports historical-source drift rather than failing
all future proof edits. `--snapshot` remains available for provenance audits.
Ignored local caches are allowed; tracked caches are rejected. The root and
verification toolchains are pinned together so `lake -d verification` cannot
accidentally use an older global default.

## Validation

- `make check`: task DAG and registration, dependency boundaries, queue/card
  consistency and seven compatibility/changed-module policy tests.
- `make test`: actual Lean typecheck of the stable interface binding and
  transitive axiom inspection. The acceptance target reports only the standard
  logical axioms.
- Mutation tests: a binding refactor is accepted; a `sorry`, an additional
  assumed axiom and a weakened hypothesis are rejected for their intended causes.
- The initial local test run reused an ignored symlink to an existing dependency
  cache; no cache was copied or committed. Local source/test targets were built
  in this checkout. A fresh collaborator can restore dependencies from the
  committed Lake manifest using the standard cache command.

The full historical umbrella is not the acceptance entry point and is not
claimed to be clean. The same applies to the still-open manuscript main theorem.

## GitHub workflow

The `Contracts` workflow provides the `architecture` and `lean-contracts` PR
checks, with pinned actions, read-only permissions and cancellation of superseded
runs. It tests the registered target package rather than the upstream default
libraries. The initial setup is delivered through a PR. Remote application and
branch-protection results are recorded below after verification.
