# Lane 468 — T24b Ub4 assembled classical solution

## 1. Statements

Ub4 is complete. `RegionsData.solution d` is an actual
`ClassicalSolutionT ν (0 : SpatialField) d.assembledForce d.T`, with velocity
and pressure definitionally equal to the prescribed finite component sums.
The three formula theorems, `solution_pin`, `force_mem`, and `rest` close
without additional inputs.

`component_nonoverlap` moves all components to the same floor-lattice
representative in the fundamental cube and applies `component_support` and
`regions_disjoint`. `crossTransport_eq_zero` then proves
`spatialDerivative (d.component j).velocity t x ((d.component i).velocity (t,x)) = 0`
for distinct indices and every `t ∈ Ico 0 d.T`, `x : Space`. When the
advecting velocity is nonzero, continuity gives a neighbourhood where it
stays nonzero; the other component vanishes on that neighbourhood, so its
Fréchet derivative is zero. When the advecting velocity is zero, the
continuous linear derivative sends it to zero directly.

The finite-sum derivative identities give divergence and all three linear
momentum terms. The advection double sum reduces to its diagonal, so the
registered residual is the sum of the component residuals. Smoothness and
periodicity are finite-sum proofs; the exact Sobolev-path and pressure-gradient
fields follow from smoothness of those sums using existing T11/T10 results.
Haar integrability of each smooth pressure permits `integral_finsetSum` and
the zero-mean gauge. `forceClassT_finset_sum` combines compact positive-time
carriers by finite unions; this force class has no mean-zero requirement.

## 2. Files

- `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean`:
  29 definitions/theorems, including the actual solution and all its fields.
- `research/T24/probes/assembled_closes.lean`: seven literal Ub4 field
  types from `Multiple.lean`, instantiated at `d`, each checked by `exact`.
- `research/T24/axioms_ub4.lean`: all 29 implementation declarations print
  exactly `[propext, Classical.choice, Quot.sound]`. The seven named probe
  declarations were separately audited with the same result.
- `research/T24/ATTEMPTS_UB4.md`: complete failed-elaboration diagnostics,
  fixes, and explanation of the nonzero-neighbourhood support argument.
- `research/T24/T24_SPLIT.md`: Ub4 completion entry.
- `research/T24/REPORT_468.md`: this report.

No existing Lean module was edited. The pre-existing untracked lane brief
was left untouched and is excluded from the commit.

## 3. Gaps with error text

No residual gap for Ub4. Ub5–Ub7 and the complete `MultipleRegionsAPI`
assembly remain outside this lane. No admission, additional axiom, placeholder,
named analytic input, or heartbeat override was introduced.

Resolved development errors include:
`Tactic rewrite failed: Did not find an occurrence of the pattern`,
`invalid declaration name pressure_smooth, structure ... has field pressure_smooth`,
`Unknown constant PiLp.sum_apply`, and cross-term index `Type mismatch`.
The full exact messages and contexts are preserved in `ATTEMPTS_UB4.md`.
The final module and probe elaborate with zero output.

## 4. Commands and results

All Lean runs sourced `. scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`,
and ran Lake from `verification/`.

- `lake build NSFormalization.Section3.T24.MultipleComponents` — passed,
  required closure built before implementation.
- `lake build NSFormalization.Section3.T24.MultipleAssembled` — passed,
  0 errors (10051 jobs; existing dependency warnings replayed).
- `lake env lean ../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean`
  — exit 0, zero output.
- `lake env lean ../research/T24/probes/assembled_closes.lean`
  — exit 0, zero output.
- `lake env lean ../research/T24/axioms_ub4.lean`
  — exit 0; all 29 entries exactly the three standard axioms.
- `lake env lean ../tmp/ub4_probe_axioms.lean`
  — exit 0; all seven probe entries exactly the three standard axioms.
- `make check` — passed; 50 registered contracts, 13 policy tests,
  and 45 work-item consistency checks.
- `lake test` from `verification/` (the `make test` target's test command)
  — passed, registered contract checks.
- `make test-mutations` — passed; implementation refactor accepted;
  admitted proof, extra axiom, and weakened hypothesis rejected as required.
- Forbidden-token/heartbeat scan of implementation and probe — no matches.
- `git diff --check` — clean.
