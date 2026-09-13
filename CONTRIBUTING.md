# Working together on blowup_density

The repository is private. `mathzhuonichi` owns it; `erenup` has been invited
with write permission. Acceptance of the GitHub invitation is required before
the collaborator can read or push. Use individual accounts and branches.

Start with the [ready work queue](collaboration/TASKS.md) and the
[Section 4 dependency graph](formalization/blueprint/README.md). The queue
separates specification, compatibility, proof and final assembly work.
Source availability and a green component test do not close a manuscript theorem.

## Layout and responsibilities

| Directory | Purpose | Normal change policy |
|---|---|---|
| `paper/` | Authoritative manuscript and original snapshots | Explain mathematical statement changes explicitly. |
| `formalization/blueprint/` | Mathematical DAG and exact intended task scope | Update dependencies and evidence when interfaces change. |
| `collaboration/` | Ownership, task cards and review state | One owner per active task; keep generated cards synchronized. |
| `research/` | Explorations and source comparisons | No import into an accepted proof target. |
| `formalization/NSFormalization/` | Existing and future proof implementations | Proof bodies and organization may evolve. |
| `verification/Contracts/V1/` | Versioned, implementation-independent specifications | Existing files are append-only by version; add V2 for an incompatible correction. |
| `verification/Bindings/` | Adapters from current implementations to fixed contracts | Change these when implementation names or paths change. |
| `verification/Tests/` | Exact-type and transitive-axiom acceptance tests | Preserve existing registered tests; add tests for new contracts. |
| `vendor/` | Pinned upstream source packages and licenses | Review upgrades separately from mathematical changes. |

## Claim a bounded task

```sh
python3 experiments/tasks.py list --ready
python3 experiments/tasks.py show D01
python3 experiments/tasks.py claim D01 erenup
```

Replace the username with your own. Commit the claim in a small PR before
substantial work to prevent both contributors implementing the same node.
Use a branch such as `codex/D01-force-contract` or `erenup/A01-forced-adapter`.
A specification task may run while a prerequisite proof is incomplete;
a proof task must have a reviewed concrete statement and registered acceptance
contract before it becomes ready for bulk implementation.

Each task card gives its mathematical goal, dependencies, existing source,
deliverable and acceptance command. Split a large implementation into separately
reviewable lemmas rather than combining unrelated discoveries in one PR.
A proof PR should not also weaken its own acceptance specification.

## Local commands

Install [elan](https://github.com/leanprover/elan) and use the toolchain in
`verification/lean-toolchain`. From a fresh checkout:

```sh
lake -d verification exe cache get
make check
make test
make test-mutations
```

`make check` is lightweight Python validation of the DAG, task queue,
contract registration and architecture. `make test` is Lake's test driver;
it compiles the selected acceptance modules and their actual dependencies.
`make test-mutations` confirms that admissions, extra axioms and weakened
hypotheses are rejected, while a proof-binding refactor is accepted.
No test command imports the legacy umbrella or builds both upstream default
libraries. Local ignored `.lake` caches are expected and are not committed.

Use `make paper` for manuscript changes. `make snapshot` is the optional
historical migration identity check; it is deliberately not a normal proof-PR
requirement. Source changes must not fail merely because their hashes differ
from the first import.

## Stable tests and specification changes

There is no test that can safely keep passing after every semantic change.
The invariant here is that implementation refactoring does not require
rewriting the expected mathematical statement. Lean checks that the binding
inhabits the exact versioned contract; a separate command inspects the actual
transitive axioms of that bound declaration. Allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`. `sorryAx`, additional assumed PDE axioms
and native-reduction axioms are rejected for registered outputs.

CI compares existing versioned specifications, registered tests and their
identity fields against the PR base. It rejects silent edits, removal or
disabling of an established contract. Add V2 and a new registration when the
mathematics changes; keep V1 working through a compatibility binding until a
separately reviewed deprecation policy is adopted. Review canonical definitions
and upstream upgrades for semantic changes too: type checking cannot decide
whether a new definition still means the intended Navier-Stokes statement.

The first active contract is `R41.threshold_arithmetic`. It certifies the
existing arithmetic component only. The remaining PDE interfaces are
explicitly specification work; no placeholder `Prop` field or `sorry` turns
them into a passing theorem test. `make test` succeeding does not certify
Theorem 4.1 or the merged paper.

## Pull request and review

Include the task ID, contract version, exact exported declarations, validation
commands and the remaining hypotheses. Use the PR template. Review contracts
and trust-checking infrastructure particularly carefully; CODEOWNERS names both
contributors. The author cannot supply the requested independent review of
their own PR. A green check certifies only its stated scope.

The CI jobs are `architecture` and `lean-contracts`. They run on PRs and pushes
to the current default branch, with
read-only workflow permissions and cancellation of superseded runs. The Lean
job tests the registered suite, not the legacy all-source umbrella. No full
OpenAI or HeliCorgi build is scheduled by default. Branch-protection availability
for a private repository depends on the GitHub account plan; see the current
[setup record](logs/COLLABORATION_SETUP_20260913.md) for the applied settings.
