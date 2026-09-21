# Current proof blueprint

Start with [DEPENDENCY_GRAPH.md](DEPENDENCY_GRAPH.md). It reports the current
article proof logic, clause-level Closed/Partial colors and remaining scope limits.
[RESULT_MAP.md](RESULT_MAP.md) links the 26 numbered article statements and
one remark to their current source declarations. The
[guide](../../output/pdf/formalization_guide.pdf) explains coverage labels.

The reader-facing graph is generated from [proof_graph.json](proof_graph.json).
The package-check inputs are [tasks.json](tasks.json),
[entrypoints.json](entrypoints.json), the
[acceptance registry](../../verification/contracts.json), and
[AXIOM_AUDIT.json](AXIOM_AUDIT.json). Historical work queues, compatibility-only
interfaces and placeholder propositions have been removed.

## Audit and reproduction

The audit follows actual transitive declaration dependencies through
`Lean.collectAxioms`; `sorry` or `admit` would be reported as `sorryAx`.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The independent
source scan rejects admission and custom-axiom tokens in every retained local
and vendored Lean module. These checks do not remove theorem hypotheses or
prove omitted manuscript variants.

In Linux, with the pinned toolchain:

```sh
make check
make test
python3 experiments/audit_article_axioms.py --build --output-dir /tmp/article-audit
```

Copy the resulting `report.json` to `formalization/blueprint/AXIOM_AUDIT.json`
only after reviewing its scope and checking for forbidden axioms, then run
`python3 experiments/check_formalization_plan.py` to regenerate the graph.
The full per-environment logs belong outside the publication tree.

## Coverage

Closed means that the complete article statement has a Lean kernel-checked
proof, including all auxiliary results and their instantiations. No unproved
theorem input, admission or extra axiom is allowed. The article's stated
hypotheses and the standard logical axioms `propext`, `Classical.choice` and
`Quot.sound` remain. Partial means that only part of the article statement is
formally proved. A downstream theorem can be Closed when it uses only fully
formalized cases of a Partial result.

The guide records 22 Closed and five Partial entries. The statement-level
[input-closure audit](CLOSURE_AUDIT.md) explains the corrected labels and
identifies the compiled suppliers for the remaining Closed results.
