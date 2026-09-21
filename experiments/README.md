# Current checks

- `check_formalization_plan.py --check`: current dependency graph, package paths,
  local imports, entry-point closure and absence of admissions/custom axioms.
- `check_contracts.py --summary`: registration and specification import boundaries.
- `test_contract_policy.py`: eleven import-policy, module-selection and article-proof coverage tests.
- `build_changed_lean.py --base-ref <commit>`: CI compilation of changed Lean files.
- `test_contract_mutations.py`: positive and negative Lean acceptance cases.
- `audit_article_axioms.py --build --output-dir /tmp/article-audit`: Linux kernel
  transitive-axiom audit of all guide declarations and explicit upstream/boundary
  exports, using separate existing import closures.
- `check_reader_documents.py`: document labels, citations, coverage markers,
  proof locations, corpus hashes and LaTeX logs; run through `make paper`.
- `reader_terminology.py`: reviewed prose terminology rules.

Previous registries and retired version interfaces are not prerequisites of
current checks. Static checks do not replace Lean compilation or mathematical
review of statement scope.
