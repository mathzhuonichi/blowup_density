# Lane 510 — P21 Route B, B5 on R³

Status: **whole-space B5 closed and registered.** The periodic half and the
authoritative `L21_H1` closure remain lane 511; this lane makes no blueprint
status change.

## 1. Statements proved and registered

`NSFormalization.Section4.A04.restartBeyondH1` proves the exact local-name form
of `research/P21/Targets.lean:h1UniformEndpointR`:

```lean
∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ S, 0 < S → ∀ K : ℝ≥0∞, K ≠ ⊤ →
  ∃ δ > 0, ∀ a u p, a ∈ initialClassR → SolvesBelow ν a f S u p →
    (∀ t ∈ Ico 0 S, sobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
      ENNReal.ofReal (S + δ) < maximalLifespanR ν a f
```

The proof first exports `restartBeyondH1_le` with the full duration and
non-strict conclusion. Lane 507's `h1RestartAt` supplies one per-time lifespan
margin; `restartBeyond_of_restartAt` passes it to `S`. The strict theorem
returns half the margin and composes
`ofReal (S + δ/2) < ofReal (S + δ)` with the non-strict result. The module also
exports `RestartFixedForceH1` and its unconditional witness
`restartFixedForceH1`.

`ContinuationV3API` registers two fields in the existing public vocabulary:
the exact H¹ fixed-force restart target and the exact strict endpoint target.
V2 exposes a parameterized API but no standalone statement alias, so V3
registers its two-field API alone. `A04.continuation_v2` remains unchanged and
separately registered for all five H⁷/integral fields.

## 2. Files and proof boundary

- `formalization/NSFormalization/Section4/A04/H1RestartBeyond.lean`: named H¹
  restart predicate, non-strict endpoint theorem and exact strict theorem.
- `verification/Contracts/V3/Continuation.lean`: proof-independent two-field
  V3 statement, importing and reusing V1/V2 vocabulary only.
- `verification/Bindings/ContinuationV3.lean`: registered witness. The restart
  solution uses `maximalPartial_ofA02`; its regularity uses
  `localTheoryV2_regularity_ofA02`; `SolvesBelow` uses
  `continuationV2_solvesBelow_iff`; maximal lifespan uses the established
  `maximalPartial_maximalLifespanR_eq` bridge.
- `verification/Tests/ContinuationV3.lean`: `checkedContinuationV3`, its axiom
  command, and exact projections of both fields under `warningAsError`.
- `verification/contracts.json`: `A04.continuation_v3`, raising the enabled
  registry count from 34 to 35 without changing `A04.continuation_v2`.
- `research/P21/probes/b5r_registered.lean`: prints the checked witness's
  axioms and instantiates the strict field on the genuine zero solution, with a
  registered zero classical solution on every shorter horizon.
- `research/P21/axioms_b5r.lean`: all three exported proof theorems, the binding
  and the checked declaration print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `formalization/blueprint/entrypoints.json`: adds the proof module, binding and
  test. The fresh source-snapshot audit is recorded in `AXIOM_AUDIT.json`.
- `Section4/A04/EnstrophyInequality.lean`: the four syntax-only `<;>` linter
  fixes authorized by the lane-504 review; direct Lean now has zero local
  warnings. No statement or proof result changed.

No lane-503/506/507 module, V1/V2 contract, proof-graph node, result-map row,
guide row or paper source was edited.

## 3. Remaining scope and resolved errors

There is no remaining whole-space B5 Lean goal or analytic hypothesis. This
lane does not claim the periodic `h1RestartT` or `h1UniformEndpointT` target,
rough-H¹ local theory, cross-force uniformity, or the broader smooth force class
outside registered `MemForceR`. Consequently `L21_H1` correctly remains
`Partial`; lane 511 must register the periodic half before changing it.

Two transient elaboration errors were resolved and are not residual gaps.
Directly checking the new test before building its new imports reported:

```text
error: object file '.../Contracts/V3/Continuation.olean' of module
Contracts.V3.Continuation does not exist
```

Building `Tests.ContinuationV3` installed the dependency closure. The first
zero-solution probe rewrite also reported:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  D01.sobolevENorm 1 fun x => 0
in the target expression
  D01.sobolevENorm 1 0 ≤ 0
```

An explicit change across the definitionally equal registered/implementation
norms followed by `erw` handles the zero-function presentation. The completed
probe has no warnings or errors.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake from `verification/`.

- Direct Lean checks of `EnstrophyInequality.lean`, `H1RestartBeyond.lean`, the
  V3 contract and binding passed with zero output. The test emitted only the
  expected standard-axiom confirmation.
- `lake build Tests.ContinuationV3`: passed, 10,527 jobs; the V3 standard-axiom
  check passed.
- `lake env lean ../research/P21/probes/b5r_registered.lean`: passed; printed
  exactly `[propext, Classical.choice, Quot.sound]` and the standard-only
  confirmation. Its zero-solution strict endpoint example elaborated.
- `lake env lean ../research/P21/axioms_b5r.lean`: passed; all five named
  declarations printed exactly the standard three axioms and passed the
  automated check.
- `python3 experiments/audit_article_axioms.py --build --output-dir
  tmp/article-audit --workers 2`: passed, **72 declarations / 27 article
  entries / zero forbidden-axiom results**; `AXIOM_AUDIT.json` was refreshed.
- `make check`: passed, **41 proof nodes / 27 article mappings / 2275 source
  modules / 35 contracts / all 11 policy tests**.
- `make test`: passed, 11,036 build/test jobs including
  `checkedContinuationV3`.
- `make test-mutations`: passed; implementation refactor accepted and admitted
  proof, extra axiom and weakened hypothesis rejected as required.
- `make paper`: passed; both PDF logs and the reader-document checks were clean.
  Generated PDF binary churn was restored.
- `python3 experiments/check_reader_documents.py`: passed independently, with
  35 registry declarations found.
- `scripts/gates.sh NSFormalization.Section4.A04.H1RestartBeyond
  Contracts.V3.Continuation Bindings.ContinuationV3 Tests.ContinuationV3`:
  passed through `== gates OK`.
- `git diff --check`: passed after the final documentation update.

Commits use the required `[510-P21-B5]` prefix. No push, merge or rebase was
performed.
