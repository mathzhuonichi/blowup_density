# Current Lean implementation

This directory contains the local proof modules in the current article/guide
and test import closure. The old umbrella module, citation-axiom placeholders,
admitted boundary draft, and unused patched sources have been removed.

Use [the dependency graph](blueprint/DEPENDENCY_GRAPH.md),
[article-to-code correspondence](blueprint/RESULT_MAP.md) and
[guide](../paper/formalization_guide.pdf) to locate results. The
verification package is the supported public build entry point:

```sh
lake -d verification exe cache get
lake -d verification build
```

`python3 experiments/check_formalization_plan.py --check` rejects unused
retained modules, missing imports, admission tokens and custom axiom
declarations.

The main Lake package imports selected OpenAI/Euler sources from `vendor/` and
selected HeliCorgi `Formal` modules in place. All use the main pinned compiler
and Mathlib; no obsolete standalone HeliCorgi or patched compatibility target
is retained. Original licenses remain with the selected upstream sources.

The current boundary integration and no-slip uniqueness exports discharge IBP.
The fixed-force H1-uniform restart and endpoint continuation clauses are proved
on both domains through the enstrophy barrier and the retained H7/H3
continuation routes. Versioned definitions that remain are live dependencies,
not historical compatibility commitments.
