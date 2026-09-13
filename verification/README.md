# Versioned Lean acceptance contracts

Run `lake test` in this directory, or `make test` from the repository root.
The package follows the separate test-library / `testDriver` convention used
by Mathlib and Batteries. It requires the existing local formalization package
without importing its umbrella.

```text
Contracts/V1/Thresholds.lean   exact stable mathematical specification
              ^
Bindings/Thresholds.lean      current implementation adapter
              ^
Tests/Thresholds.lean         typed assignment + transitive axiom check
              |
TestSupport/Axioms.lean       Lean.collectAxioms, standard logical allowlist
```

The baseline suite has one registered component contract with six arithmetic
obligations. Its universal quantifiers, strict inequalities and intermediate
negative-index range are part of the fixed type. The adapter points at existing
Paper 3 arithmetic lemmas; it does not prove new PDE results.

Register additional contracts in `contracts.json`, connect them to a task ID,
and add concrete typed bindings and test modules. `Tests.+` discovers test
modules automatically; registration validation rejects unregistered tests.
The registry is a coverage list, not a declaration that its parent task is done.

Use `python3 ../experiments/check_contracts.py --base-ref <base-commit>` to
check compatibility against a previous commit. A protected V1 statement and
its acceptance test remain unchanged when a proof is refactored. New statements
belong in a new version; missing proofs remain unimplemented work items.

The axiom check reads Lean's declaration dependencies directly. It does not
parse `#print` output, depend on source line numbers, or treat zero textual
`sorry` occurrences as a proof certificate. Mutation tests verify both the
positive and rejection paths. Auditing a declaration is still relative to its
formal definitions; reviewing manuscript fidelity remains necessary.
