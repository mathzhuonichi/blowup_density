# Lane 217 report

## 1. Theorem proved

`shiftedLocalExtension : ShiftedLocalExtension` proves lane 215's exact target:
for ν>0, `w : ClassicalSolutionR ν a f T`, b∈[0,T), and
`w₂ : ClassicalSolutionR ν (fun x => w.velocity (b,x)) (timeShift b f) L`,

```lean
ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
```

No named hypothesis remains. The three new corollaries
`restartBeyond_of_memForceR'`, `extendsBeyond_of_memForceR'`, and
`lifespanInfiniteOfLocallyFinite_of_memForceR'` discharge the extension binder.
The first retains fixed-force/H⁷ quantifiers; the other two give the integral
continuation and infinite-lifespan conclusions under their stated solution
and finiteness hypotheses.

## 2. Lean implementation

New module `formalization/NSFormalization/Section4/A04/ShiftedExtension.lean`
contains 12 declarations. Its constructive core, `exists_shifted_glue`, produces
an actual classical solution on `[0,b+L)` when T<b+L. The complementary case
b+L≤T follows from the original solution and horizon monotonicity.

The proof uses A02's `velocity_unique_core` and `pressure_gauge_core` on
lane 215's shifted solution and the restarted solution. A02's existing
`normalizePressure` and `normalizePressure_gauge_invariant` make the two
pressures equal on the overlap. This replaces the proposed cutoff blend with
an interior paste of separately normalized pressures at c=(b+T)/2. No gauge
function is extended across T. The velocity also agrees with each chart on
its whole interval. Joint smoothness, initial data, divergence, momentum,
continuous Sobolev paths and L² pressure gradients are all proved.

Added ATTEMPTS, the complete declaration audit and this report; appended the
updated continuation status to COMPARISON. Existing Lean modules and contracts
were not changed.

## 3. Remaining gaps

None for `ShiftedLocalExtension` or the three requested corollaries. All
hypotheses concern the actual input solutions, viscosity, datum, force or
integral bounds; there is no replacement gluing or regularity hypothesis.
The construction applies to arbitrary actual nonzero solutions as well as
zero solutions. The conformance file exercises the genuine gluing branch
using `A04.zeroSol`, and applies the lifespan and integral-continuation results.

The old cross-force/H¹ restart statement remains a separate quantifier issue;
this lane does not claim it or modify any frozen contract. Pressure is
preserved up to its allowed spatially constant gauge, rather than literally
retaining the original pressure function.

## 4. Validation and delivery

Every Lean command sourced `scripts/lean-env.sh`; all Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- `lake -q --log-level=error build NSFormalization.Section4.A04.ShiftedExtension`:
  passed, zero output.
- `lake env lean ../formalization/NSFormalization/Section4/A04/ShiftedExtension.lean`:
  passed, zero output.
- `lake env lean ../research/A04/axioms_shifted_extension.lean`: passed;
  all 12 declarations have exactly `[propext, Classical.choice, Quot.sound]`,
  and all non-vacuity examples pass.
- Root `make check`: passed, including 13 contract-policy tests and the
  30-item work queue check.
- `lake test`: passed (registered contract tests).
- `python3 experiments/test_contract_mutations.py --skip-build`: passed.
- `git diff --check`: passed.

No proof placeholders, new axioms, native decision shortcuts or heartbeat
adjustments. Work stayed in this worktree. Changes are committed on
`erenup/217-A04-shifted-extension`; no push, merge or rebase was performed.
Raw logs are in worktree-local `tmp/*_217.log`.
