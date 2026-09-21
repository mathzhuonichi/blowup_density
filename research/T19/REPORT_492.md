# Lane 492 — P1 prescribed-ball insertion

**Status: complete.** G36_FULL and Theorem 3.6 are Closed for every prescribed
positive-radius coordinate ball whose closure lies in the interior of the
fundamental cube. Inventory: **22 Closed / 5 Partial**, **30 contracts**.

## 1. Statements

`T15.placementDataAt center radius hρ hcube hK hf T hT` constructs the
placement at precisely the given centre and radius. Its `T`, `chartCenter`,
`chartRadius` and `x₀` projections have `rfl` lemmas. The threshold is

```lean
min (min (1 / 2) (T / 4))
  (radius / (2 * (placementRadius hK hf + 1)))
```

This factors the construction used by `T24.RegionsData.placement` without
changing that module or the existing fixed-ball `placementData`.

`T19.insertionDataAt` selects the registered packet, constructs the prescribed
placement and scaling, and supplies the correction with radius
`min (radius / 2) (1 / 4)`. `insertionDataAt_rawPremises` discharges the erased
packet support and sign fields. `T19.insertionAt` assembles the complete T18
record. The constructors and `exists_force_close_at` are exported from
`T19.At` to `T19`; the other prescribed-ball exports live in `T19.At` to avoid
collisions with the existing fixed-ball exports.

`T19.At` supplies the original force, lifespan, solution, blowup, mixed and
Sobolev exports, the all-subcritical Sobolev limit, and strict force closeness.
It additionally proves `history`, `velocityDifference_divFree`,
`velocityDifference_support`, `diffSupport_in_chart` and `energyRate` against
**the original `reference.velocity`**. `reference_slice` uses
`extendByZero_velocity_eqOn`; energy transport uses the existing
`energyENormT_congr_Ico`.

The support statement is

```lean
tsupport (fun x => velocity ε (t, x) - reference.velocity (t, x)) ∩
  fundamentalCube ⊆ Metric.ball center (ε * R)
```

for every admissible ε and `t ∈ Ico 0 T`, with `R > 0` independent of ε and
`ball center (ε * R) ⊆ ball center radius`. Thus its diameter is at most
`2 * R * ε`. `periodicSet_inter_cube` proves that no nonzero lattice translate
can meet the closed cube when the underlying set lies in its interior. This
reduces the record's periodic support to the required single chart; it does
not incorrectly bound the entire periodic lift by one Euclidean ball.

`T19.periodicInsertion_from_data` has only these inputs:

- positive viscosity;
- the prescribed centre, positive radius and interior-closure hypothesis;
- admissible datum and force;
- positive T and δ, and `ClassicalSolutionT ν a g (T + δ)`.

It chooses a positive threshold, force and velocity families, nonnegative
M, D, C, positive R, and mixed/Sobolev constants before all scale and norm
quantifiers. M and D are supplied by the selected packet's energy and
dissipation bounds; C is the constructed correction's energy constant.
Every ε in the common `Ioc 0 ε₀` satisfies:

1. force and force-difference membership, exact lifespan T, a classical
   solution pinned to the returned velocity, and the limsup blowup clause;
2. unchanged history on `0 ≤ t ≤ T - 2 * ε²`;
3. divergence-free difference and the single-chart shrinking support above;
4. the simultaneous Eclose, Fclose and Hsclose bounds, with the registered
   mixed/Sobolev path guards.

It also retains negative-order Sobolev convergence and path membership.
`Contracts.V2.PeriodicInsertion.periodicInsertionStatementV2` restates this
raw-data statement in registered vocabulary. The binding only transports
`ClassicalSolutionT` and its lifespan definition; all other clauses transfer
directly. V1 remains registered.

The non-vacuity probe applies the complete theorem to zero datum and force,
viscosity one and T = δ = 1, using the existing constant zero solution. It
instantiates both the centre `(1/2,1/2,1/2)` with radius `3/8`, and the
centre `(1/4,1/4,1/4)` with radius `1/8`; the latter's cube-containment proof
is explicit.

## 2. Files

New implementation:

- `formalization/NSFormalization/Section3/T15/PlacementAt.lean`
- `formalization/NSFormalization/Section3/T19/ThreadingAt.lean`
- `formalization/NSFormalization/Section3/T19/FromData.lean`

New acceptance interface:

- `verification/Contracts/V2/PeriodicInsertion.lean`
- `verification/Bindings/PeriodicInsertionV2.lean`
- `verification/Tests/PeriodicInsertionV2.lean`
- Registry entry `T03.periodic_insertion_v2`, retaining V1.

Research:

- `research/T19/probes/prescribed_ball_492.lean`
- `research/T19/axioms_492.lean` (all 33 implementation declarations)
- `research/T19/ATTEMPTS_492.md`
- P1 status in `research/T19/T19_SPLIT.md`
- This report.

Coverage, source entry points, result map, guide, README counts and closure
audit are updated. G36_FULL has `depends_on: ["G36"]`; the schema requires
`completion_from: []` on Closed nodes. The dependency graph and kernel audit
are regenerated, and both tracked PDFs are rebuilt. The reader checker now
expects five Partial labels. The coverage regression uses the still-Partial
C35_FULL fixture instead of the now-Closed G36_FULL, with the same mutation
and rejection assertion. Every existing-file edit is recorded in ATTEMPTS.

## 3. Gaps and error text

**No remaining mathematical or acceptance gap in the requested scope.**
No extra analytic input, admission, custom axiom, `native_decide`, or heartbeat
increase was introduced. All 33 implementation declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

Resolved elaboration errors and their fixes are recorded in ATTEMPTS:
projection reduction for the radius inequality, explicit geometry forwarding,
section-variable inclusion, pointwise rewriting below spatial derivatives and
supports, and contract namespace resolution.

Two initial packaging failures were corrected without weakening checks:

- `AssertionError: Current test roots differ from retained tests`: added the
  V2 test to `entrypoints.json.test_modules`.
- `AssertionError: AssertionError not raised` in the recolouring regression:
  switched its missing-clause fixture from G36_FULL to C35_FULL.

## 4. Commands and results

Lean commands used `. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`; direct
Lake commands ran from `verification/`. Full logs are under `tmp/lane492/`
and `tmp/article-audit/` (untracked).

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T19.ThreadingAt` | Passed, 10661 jobs after adding reference/support transport. |
| `lake build NSFormalization.Section3.T19.FromData Contracts.V2.PeriodicInsertion` | Canonical theorem passed; initial contract namespace errors resolved in the next build. |
| `lake build Tests.PeriodicInsertionV2` | Passed, 10704 jobs; three explicit axiom checks passed. |
| `lake env lean ../research/T19/probes/prescribed_ball_492.lean` | Passed, no output. |
| `lake env lean ../research/T19/axioms_492.lean` | Passed; all 33 declarations have exactly the standard three axioms. |
| `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` | Passed: 56 declarations, 27 article entries, zero forbidden-axiom results, no forbidden source tokens. Reviewed and copied `report.json` to `AXIOM_AUDIT.json`. |
| `python3 experiments/check_formalization_plan.py` | Passed; regenerated graph: 41 nodes, 27 mappings, 2244 source modules. |
| `make check` | Passed: 30 contracts and all 11 policy tests. |
| `make test` | Passed: 11006 jobs. |
| `make test-mutations` | Passed: refactor accepted; admitted proof, extra axiom and weakened hypothesis rejected. |
| `make paper` | Passed: both PDFs rebuilt; reader checks and both LaTeX build logs clean. |
| `git diff --check` | Passed. |

Commits before this report: `3100e812` (construction), `d0f39fa8` (raw theorem
and probes), `0a9d7116` (V2 contract), `df02cd6d` (coverage, audit and artifacts).
Work stayed on `erenup/492-T19-P1-prescribed-ball`; no push, merge or rebase.
