# Lane 511 — P21 Route B, B5 on T³ and `L21_H1` closure

Status: **periodic B5 is closed and registered, and the last Partial blueprint
node is closed.** Both domains of the Proposition 2.1 H¹-uniform obligation are
now registered. The authoritative graph has 41 Closed nodes and no Partial
nodes; all 27 article mappings are Closed.

## 1. Statements proved and registered

`NSFormalization.Section3.T11.restartBeyondH1T` proves the exact local-name
form of `research/P21/Targets.lean:h1UniformEndpointT`:

```lean
∀ ν, 0 < ν → ∀ f, f ∈ forceClassT → ∀ S, 0 < S →
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0, ∀ a ∈ initialClassT, ∀ u p,
    SolvesBelowT ν a f S u p →
    (∀ t ∈ Ico 0 S, periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
      ∃ v : ClassicalSolutionT ν a f (S + δ),
        (∀ t ∈ Ico 0 S, ∀ x, v.velocity (t, x) = u (t, x)) ∧
        (∀ t ∈ Ico 0 S, ∀ x, v.pressure (t, x) = p (t, x))
```

The proof copies the established periodic endpoint/gluing skeleton and replaces
its sole analytic input, `restart H`, with lane 508's `h1RestartT`. It keeps the
duration `d` delivered by `h1RestartT` unchanged, chooses
`t₀ = max 0 (S - d / 2)`, and returns the positive endpoint increment
`δ = t₀ + d - S`. Velocity uniqueness and normalized-pressure uniqueness give
the literal overlap on `[0,S)`.

`PeriodicContinuationH1API` registers two order-one fields: the H¹-ball
restart whose duration precedes the restart time and datum, and the endpoint
theorem above. `torusLocalTheoryV2Statement` is
`Nonempty TorusLocalTheoryAPI ∧ PeriodicContinuationH1API`, so the complete V1
package remains present and independently registered. The binding witnesses
the restart field with `h1RestartT`, the endpoint field with
`restartBeyondH1T`, and transports solutions and regularity through the
existing V1 conversions. The checked declaration is
`BlowupDensity.Tests.checkedTorusLocalTheoryV2`; registry entry
`T01.torus_local_theory_v2` has parent task `T11`. Together with lane 510's
`checkedContinuationV3`, both domain registrations print exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files and closure inventory

- `formalization/NSFormalization/Section3/T11/H1RestartBeyond.lean`: exact
  periodic H¹ endpoint theorem.
- `verification/Contracts/V2/TorusLocalTheory.lean`: proof-independent V2 API,
  importing and reusing all V1 registered definitions.
- `verification/Bindings/TorusLocalTheoryV2.lean`: V1 package plus the two H¹
  witnesses (`torusContinuationH1API` at line 27 and
  `torusLocalTheoryV2_holds` at line 48).
- `verification/Tests/TorusLocalTheoryV2.lean`: checked declaration, axiom
  command and exact projections of both new fields under `warningAsError`.
- `verification/contracts.json`: enabled V2 entry, raising the registry from
  35 to 36 contracts without replacing the V1 registration.
- `research/P21/probes/b5t_endpoint.lean`, `probes/b5t_registered.lean`,
  `axioms_b5t.lean` and `ATTEMPTS_B5T.md`: exact-target, consumer,
  non-vacuity, axiom and route evidence. The registered probe instantiates the
  order-one endpoint field on the genuine zero solution.
- `formalization/blueprint/proof_graph.json`: `L21_H1` is Closed, depends on
  the already Closed `L21T` and `L21R`, and cites both domains' restart and
  endpoint proofs/bindings. It remains in its original panel.
- `research/P21/P6_SPLIT.md`: B0 through B5 are all recorded Closed.
  `research/P21/ASSESSMENT.md` retains its history and adds the dated outcome.
- `output/pdf/blowup_density_revised.pdf` and
  `output/pdf/formalization_guide.pdf`: regenerated; the guide visibly marks
  Proposition 2.1 Closed.

Exact blueprint / guide / README line inventory changed by the closure commit:

- `README.md`: lines 35 and 41–42.
- `formalization/blueprint/proof_graph.json`: lines 78–95.
- `formalization/blueprint/entrypoints.json`: lines 20, 79 and 114.
- `formalization/blueprint/RESULT_MAP.md`: line 12.
- `formalization/blueprint/README.md`: line 48.
- `formalization/blueprint/CLOSURE_AUDIT.md`: lines 18–26, 31, 37–40, 45, 49,
  58–61 and 85.
- `formalization/blueprint/DEPENDENCY_GRAPH.md`: lines 21, 30–31, 39, 176 and
  215.
- `formalization/blueprint/AXIOM_AUDIT.json`: source snapshot lines 4–5; the
  new targets around lines 90–141; Proposition 2.1 coverage around lines
  1008–1018.
- `paper/formalization_guide.tex`: lines 82, 86–92 and 187–204.
- `experiments/check_reader_documents.py`: lines 60 and 71.

The Proposition 2.1 result-map row keeps its five inherited sources and adds
the four requested exact anchors:
`Bindings/ContinuationV3.lean:29`, `Bindings/TorusLocalTheoryV2.lean:48`,
`Section4/A04/H1Restart.lean:261`, and
`Section3/T11/H1Restart.lean:576`. The guide adds the same four sources and
explains the enstrophy differential inequality, the uniform ODE barrier and
the existing integral continuation criterion. README now reports
**27 Closed and 0 Partial**.

## 3. Gaps and resolved errors

There is no remaining P6 unit, `L21_H1` mathematical gap, Partial article
mapping, admission, custom axiom or heartbeat override. The result is for the
fixed force classes used by the project (`MemForceR` and `forceClassT`); it
does not assert rough-data local theory or cross-force uniformity, and the
H¹-uniform clauses are not used as assumptions by the proved continuation
routes.

One transient contract elaboration error was resolved. The initial V2 module
did not open the namespace containing the reused periodic data definitions and
reported:

```text
Function expected at periodicSobolevENorm
identifier unknown
```

Opening `BlowupDensity.Contracts.V1.TorusData` exposes the imported V1
definition; no contract vocabulary was restated. No error remains in the
proof, registration, zero-solution probe or reader documents. No applicable
lead-ruling files existed for lanes 503, 505, 506 or 508; the only matching
review was lane 504, whose authorized style fixes had already been applied by
lane 510.

## 4. Commands and results

All Lean invocations used the repository environment. The full required gate
sequence passed:

- `lake env lean ../research/P21/probes/b5t_registered.lean`: passed; both
  checked declarations printed exactly the three standard axioms and the
  order-one zero-solution instantiation elaborated.
- `python3 experiments/audit_article_axioms.py --build --output-dir
  tmp/article-audit --workers 2`: passed before `make check`; **76
  declarations / 27 article entries / zero forbidden-axiom results**.
- `python3 experiments/check_formalization_plan.py`: passed and regenerated
  the dependency graph with 41 Closed nodes.
- `python3 experiments/test_contract_policy.py`: all policy tests passed.
- `make check`: passed, **41 proof nodes / 27 article mappings / 2281 source
  modules / 36 contracts / all 11 policy tests**.
- `make test`: passed, 11,043 build/test jobs including
  `checkedTorusLocalTheoryV2`.
- `make test-mutations`: passed; the implementation refactor was accepted and
  the admitted proof, extra axiom and weakened hypothesis were rejected as
  required.
- `make paper`: passed; both PDFs regenerated and the guide shows Proposition
  2.1 Closed.
- `python3 experiments/check_reader_documents.py`: passed independently with
  **27 mappings / 36 registry declarations**.
- `scripts/gates.sh NSFormalization.Section3.T11.H1RestartBeyond
  Contracts.V2.TorusLocalTheory Bindings.TorusLocalTheoryV2
  Tests.TorusLocalTheoryV2`: passed through `== gates OK`.
- `git diff --check`: passed after the closure commit and final gate run.

The three completed closure commits are `f640f526`, `052d75f8` and
`e161bf09`, all with the required `[511-P21-B5T]` prefix. No push, merge or
rebase was performed by this lane.
