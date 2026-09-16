# Lane 245 — R46 reconciled specification report

## 1. Which theorem was specified

This lane specifies Proposition 4.6 (`prop:Renergy`),
`paper/sections/04-whole-space.tex:218-229`, following the binding decisions in
`research/R46/RECONCILIATION.md`.  The proposition states completed-space
density of finite-lifespan smooth compact forces in `L^q_tH^s_x` for
`q ∈ {1,2}`, `s < s_q`, and in `L²_tḢ⁻¹_x`, together with simultaneous strong
closure of one Theorem 4.2 insertion family in the energy norm and the displayed
sum of three force norms.

## 2. What Lean now contains

`research/R46/Spec.lean` contains the single reconciled structure
`BlowupDensity.R46.Draft.REnergyAPI` with exactly the fields
`completedSobolevDensity`, `completedHomogeneousDensity`, and
`strongTrajectoryClosure`.  The density fields use the registered
`CompletedDense` / `CompletedDenseHomogeneous` abbreviations, `q : ℝ≥0∞`, the
constraint `(q = 1 ∨ q = 2)`, and `criticalOrder q.toReal`.  Two generic
`example ... := rfl` checks verify that the abbreviations unfold to the two
required `CompletedDenseVia` predicates.

The strong-closure field uses the reconciled raw-data order
`a, ν, T, g, δ, R, ∃ P, ∃ A`.  It keeps only the explicit
`R : ClassicalSolutionR ν a g (T + δ)`, does not expose the insertion ball, and
retains inserted-force membership, exact lifespan, full-horizon classical
solution, and both same-family limits.  Every field docstring cites the relevant
`04-whole-space.tex` lines, states its exact quantifier order, and records why
the clause is non-vacuous.

`research/R46/COMPARISON.md` gives the merged paper-clause table with A/B
provenance and every reconciliation ruling, copies the reconciliation's proof
dependencies, and records the remaining owner questions.  The six draft
artifacts (`DraftA.lean`, `DraftB.lean`, both comparison files, and both reports)
were copied byte-for-byte from lanes 242 and 243 and verified with `cmp`.

## 3. What remains missing

This is a specification lane: it provides no inhabitant, binding, or registered
`Contracts/V1/CompletedDensity.lean` module.  The proof still needs R45's
class-relative density plus completed-target approximation.  In particular,
the full homogeneous completed-space assembly omitted by `HomogeneousPartial`
is open, as is the same-family `L²_tḢ⁻¹_x` scaling convergence omitted by I03.
The registered path predicates' every-time realization versus Bochner a.e.
equivalence is inherited vocabulary and was intentionally not changed here.

## 4. Commands run and results

- `cd verification && lake env lean ../research/R46/Spec.lean` — passed with
  zero diagnostics; both `rfl` checks elaborated.
- The same Lean command for `DraftA.lean` and `DraftB.lean` — both passed with
  zero diagnostics.
- `cmp` against `git show` for all six provenance files — all six matched.
- `git diff --check` and the placeholder scan for
  `sorry|admit|axiom|native_decide` in `Spec.lean` — passed, no matches.
- `make check` — exited 0; architecture, contract-policy tests, and work-queue
  checks passed.  The existing formalization-plan summary still reports
  `source_hashes_match: false`, as on the source lanes, but the gate accepts it.
- `LEAN_NUM_THREADS=6 make test` — exited 0; only pre-existing dependency linter
  warnings were replayed.
- `LEAN_NUM_THREADS=6 make test-mutations` — exited 0; the refactor mutation was
  accepted and the admitted-proof, extra-axiom, and weakened-hypothesis
  mutations were rejected as required.
