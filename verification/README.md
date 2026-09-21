# Current publication acceptance interfaces

Run `make test` from the repository root, or `lake test` here. There are
30 current typed acceptance interfaces. Each test names a mathematical
specification, a concrete implementation and a transitive axiom check.

The registry lists the retained interfaces. Superseded tests and unused
compatibility wrappers have been removed. Existing `Contracts/V1` definitions
remain where the current proof/test closure uses them; they are not required
for backward compatibility alone. Registration is not a claim that every
related manuscript statement is fully formalized.

`make check` validates the current registry, import boundaries and source
closure. `make test-mutations` checks that admitted proofs, extra axioms and a
weakened hypothesis are rejected, while an implementation refactor is accepted.
The axiom checker reads actual declaration dependencies, not textual `#print`
output or a grep count.

The article-declaration audit separately checks the actual guide targets,
including upstream comparison and boundary closure. See the
[dependency graph](../formalization/blueprint/DEPENDENCY_GRAPH.md). Its standard
axiom result must be read together with the guide's hypothesis/scope labels.
