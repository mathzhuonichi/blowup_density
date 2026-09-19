# Lane 482 — T23 U3 triple and domain solution

## 1. Statements

U3 is complete with the supplier and U4 hypotheses explicitly threaded as
requested. The actual fields are defined for every real scale and spacetime
point, with all three formula lemmas proved by `rfl`. The common threshold is

```text
min (min place.ε₀ D.ε₀) (min scalingBound geometryBound).
```

Its positivity and four upper bounds are proved. The force and force difference
belong to the domain force class; velocity and normalized pressure satisfy the
actual open-neighborhood closed-slab convention. Initial data, incompressibility,
local momentum and global quiet history (including the closed endpoint) are
proved for the concrete triple.

Pressure normalization is peeled into finite positive real volume, integrable
slices, finite-order smoothness of the time integral, a smooth open time
neighborhood, zero mean, and invariance of the spatial gradient/residual.
The integral proof uses compact spatial closure and the proved domain
parameter-differentiation lemma, inductively at every finite order. No global
smoothness of the domain reference is assumed.

`InsertedTriple.classicalSolution` constructs all ten canonical solution fields.
Only no-slip comes from U4; the other analytic fields are the U3 proofs.
`InsertedTriple.solution` proves the exact API existential on the common scale
range. The implementation introduces no replacement records.

## 2. Files

- `formalization/NSFormalization/Section3/T23/PressureNormalization.lean`:
  pressure integral and gauge analysis.
- `formalization/NSFormalization/Section3/T23/Triple.lean`: the three fields,
  threshold, regularity, force classes, history, initial data, divergence and
  local residual computation. Includes packet regularity transport from the
  raw zero-past extensions.
- `formalization/NSFormalization/Section3/T23/Solution.lean`: pressure gauge,
  the ten-field constructor, and API solution witness.
- `research/T23/probes/T23-U3-triple-solution_closes.lean`: embeds the original
  `Spec.lean` byte-for-byte; fieldwise canonical/Spec conversions; `exact`
  consumers for all 18 fields and `solution`, plus each of the ten solution
  fields. The two named solution consumers also have guarded axiom audits.
- `research/T23/axioms_T23-U3-triple-solution.lean` and `.log`: all 42 production
  declarations, including definitions, print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T23/ATTEMPTS_T23-U3-triple-solution.md`: failed approaches and exact
  diagnostics, including resolved probe elaboration problems.
- U3 status in `research/T23/T23_SPLIT.md`, this report, and the compact
  validation log.

Skeleton checkpoint: `c15d260e`; incremental proof checkpoints are recorded in
branch history. No existing Lean module, registry, contract, generated task
card or other lane's module was edited. The pre-existing untracked lane brief
was left untouched. No push, merge or rebase was performed.

## 3. Gaps with error text

There is no residual U3 analytic goal or compiler error. This is not an
unconditional T23 construction or registration. The authorized assembly inputs
remain explicit:

1. The existing `LocalCorrectionCore reference.velocity u K place.x₀ r
   place.T δ D`, and `ball place.x₀ r ⊆ Ω` for force regularity. U9 must supply
   the actual matching correction family at this same `D`; no equality of
   independently chosen cutoffs or potentials is asserted.
2. The same-scale packet equation and divergence from I03, and packet
   velocity/pressure smoothness on `Iio place.T ×ˢ univ`. The latter can be
   discharged using the two proved raw zero-past regularity transport lemmas.
   Packet force smoothness and compact positive-time support, plus reference
   force membership, enter the force-class theorems.
3. Positive I03 and additional geometry bounds for threshold positivity;
   U4's no-slip equality on the resulting common interval for `solution`.

These are the permitted upstream fields/facts, not assumptions of the inserted
momentum, smoothness, pressure gauge or solution conclusion. U2b matching,
other U4–U8 fields, G0 registration decisions and G1 smooth-domain uniqueness
are not claimed here.

Resolved diagnostic examples:

```text
error: Failed to rewrite using equation theorems for `velocity`
error: internal exception #3
error: Unknown option `pp.width`
```

The first was resolved by exposing the concrete field before derivative
rewrites; the second by making the probe's no-slip hypothesis an explicit
theorem binder rather than a dependent section variable using local notation;
the third by removing the optional formatting setting. The final probe has
zero output and its two named declarations have only the three allowed axioms.
Every failed proof/check diagnostic is retained in ATTEMPTS.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh`; every Lake invocation ran
from `verification/` with `LEAN_NUM_THREADS=6`.

- Dependency closure first:
  `lake build NSFormalization.Section3.T23.Boundary
  NSFormalization.Section3.T23.LocalCorrectionBridge
  NSFormalization.Section3.T23.NoSlipEnergy
  NSFormalization.Section3.T23.DifferenceEnergy
  NSFormalization.Section3.T23.BoxIntegration` — exit 0, 10087 jobs.
  This closure includes Placement, LocalCorrection, SpatialExtension,
  StatementRepair and DomainSolution. ResidualStability was built before use.
- `lake build NSFormalization.Section3.T23.PressureNormalization
  NSFormalization.Section3.T23.Triple NSFormalization.Section3.T23.Solution`
  — exit 0, 10090 jobs; only existing dependency diagnostics replayed.
- `lake env lean` on each of the three new modules — exit 0, zero output each.
- `lake env lean ../research/T23/probes/T23-U3-triple-solution_closes.lean`
  — exit 0, zero output, including the guarded consumer axiom checks.
- `lake env lean ../research/T23/axioms_T23-U3-triple-solution.lean`
  — exit 0; 42 exact permitted axiom lists.
- `make check` — exit 0; 13 policy tests passed, 45 work items consistent.
  It still reports the historical `Paper1/BoundaryCorollary.lean` admission
  and `source_hashes_match: false`; these are repository-wide diagnostics,
  not additions to this lane's closure.
- `lake test` — exit 0, 11015 jobs.
- `make test-mutations` — exit 0; implementation refactor accepted; admission,
  extra axiom and weakened hypothesis rejected.
- Original Spec byte inclusion, exact-list audit, new-source forbidden-token
  scan, no heartbeat override, and `git diff --check` — passed.
- Comment-aware project/vendor import traversal: 1327 resolved source files;
  no unresolved project imports and no `Paper1.BoundaryCorollary` import.
