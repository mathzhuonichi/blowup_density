# Lane 497 — P5.1 and P5.2

## 1. Statements

`RegionsOmegaData` carries raw packet clauses and prescribed domain/region
geometry, mirroring `RegionsData` with Ω replacing the fundamental cube.
P5.1 constructs `placement`, its prescribed chart/time equalities, `ε`, both
scale bounds, and actual `ClassicalSolutionOmega` components with the exact
raw velocity and Ω-normalized pressure. Velocity support is global before T;
force support is global at every real time.

P5.2 defines the literal finite sums and proves their three formulas, constructs
`solution`, and proves `solution_pin`, `force_mem`, global `rest`, and `no_slip`.
Cross transports vanish by global disjoint supports and local constancy of the
other velocity. The finite pressure sum is gauged by integrability and linearity
of the Ω integral. No solution/API/existence premise or cross-lane input is used.
The article clauses are revised `03-torus.tex:512,517,520,523–526,533`.

## 2. Files and commits

- `formalization/NSFormalization/Section3/T24/MultipleOmegaComponents.lean`
- `formalization/NSFormalization/Section3/T24/MultipleOmegaAssembled.lean`
- `formalization/blueprint/entrypoints.json`: both modules registered.
- `research/T24/probes/p5a_closes.lean`: every P5.1/P5.2 target by `exact`.
- `research/T24/axioms_p5a.lean`: all 45 module definitions/theorems.
- `research/T24/ATTEMPTS_P5A.md`, `T24_SPLIT.md`, this report.
- `formalization/blueprint/AXIOM_AUDIT.json`: refreshed by a real article audit;
  only source hash/count changed. The regenerated dependency graph is unchanged.

P5.1 commit: `242fcb1b`. P5.2 commit: `b26406ce`.

## 3. Gaps and resolved diagnostics

No residual in P5.1/P5.2. P5.3 region agreement/blow-up, P5.4 energy/dissipation,
P5.5 API assembly, and V2 registration remain outside this lane. `M316_B` stays
Partial. Downstream consumers use `RegionsOmegaData` and its concrete components
and sums; the original M and E remain in `d.packet`.

Resolved Lean diagnostics are recorded in ATTEMPTS_P5A.md. The initial static
gate failed with `AssertionError: Source changed: rerun the article axiom audit`.
The full audit was rerun rather than editing its hash by hand.

## 4. Commands and results

All lake commands run from `verification/`, after sourcing `scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6`.

- Dependency build: MultipleOmega, Triple, MultipleAssembled — passed.
- `lake build NSFormalization.Section3.T24.MultipleOmegaComponents` — passed.
- `lake build NSFormalization.Section3.T24.MultipleOmegaAssembled` — passed.
- `lake env lean` on each new module — passed, zero output.
- `lake env lean ../research/T24/probes/p5a_closes.lean` — passed, zero output.
- `lake env lean ../research/T24/axioms_p5a.lean` — passed; 45/45 print exactly
  `[propext, Classical.choice, Quot.sound]`, also checked by a log parser.
- `python3 ../experiments/audit_article_axioms.py --build --output-dir
  ../tmp/article-audit-497 --workers 2` — passed, 56 declarations, no forbidden
  axioms. Report copied after checking scope and results.
- `python3 experiments/check_formalization_plan.py` — passed, graph unchanged.
- `make check` — passed after the audit refresh (blueprint, registry, policy tests).
