ACCEPT

## What the lane claims

The worker report lists five declarations in `NSFormalization.Section3.T22`: the
global smoothness theorem (`research/T22/REPORT_408.md:10-13`), compact support
(`:15-19`), `MemLp` (`:21-24`), square-integrable jets (`:26-29`), and the
all-real-orders datum existence theorem (`:31-34`).  The signatures in the
delivered module agree exactly: `contDiff_zeroExtension` is at
`formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean:26-29`,
`hasCompactSupport_zeroExtension` at `:47-51`, `memLp_zeroExtension` at
`:59-62`, `smoothJets_zeroExtension` at `:67-70`, and
`exists_datum_zeroExtension` at `:82-85`.

These are the U-B2 targets recorded in `research/T22/T22_SPLIT.md:86-97`.
The carrier is the canonical definition
`zeroExtension Ω z := Ω.indicator z` (`formalization/NSFormalization/Section3/T22/Domain.lean:46-48`),
and the paper's relevant bounded-domain statement is the zero-extension
comparison for smooth fields supported in a fixed compact interior set
(`paper/sections/03-torus.tex:608-625`), with uniform-support context at
`:626-630`.  The Lean hypotheses `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
`tsupport (zeroExtension Ω z) ⊆ K` are the explicit U-B2 formulation, not an
empty-interval or junk-value hypothesis.

## What is in Lean

The proof checks the indicator against `z` on an `Ω` neighborhood and against
the zero field on the complement of the closed support
(`ZeroExtRegularity.lean:30-44`).  Compact support is obtained from the same
support inclusion and `HasCompactSupport.intro` (`:51-56`); the subsequent
`MemLp` and all-jet claims use the continuous compact-support API
(`:63-78`).  The final constructor call is the existing D01 theorem
`exists_isSobolevDatum_of_contDiff_memLp` (`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:299-303`),
and the target predicate is the canonical all-order definition
`SmoothSquareIntegrableJets` (`formalization/NSFormalization/Section4/D01/DatumToJets.lean:116-120`).
No replacement or duplicated D01 datum definition was introduced.

The neighboring T22 files use the same indicator spelling and zero-off-support
lemma (`formalization/NSFormalization/Section3/T22/RestrictBridge.lean:39-44`)
and the same whole-space `MemLp` context for the indicator
(`formalization/NSFormalization/Section3/T22/OrderZero.lean:229-235`).  The
gluing idiom is also already used for a cutoff field in
`formalization/NSFormalization/Section3/T16/Assembly.lean:63-79`; no sibling
contract is contradicted.

The non-vacuity probe is substantive: it uses a `ContDiffBump` on
`ball 0 1`, supported in `closedBall 0 (1/2)`, and proves the zero extension is
nonzero at the origin (`research/T22/probes/zero_ext_regularity_closes.lean:13-35`),
then discharges the geometric support hypotheses and all five consequences
(`:37-98`).  Its typecheck passed with zero output.

The report's axiom audit is present at
`research/T22/axioms_ub2.lean:5-9`; each declaration printed exactly the
standard `[propext, Classical.choice, Quot.sound]` set.  The only apparently
unused parameters are the underscore-prefixed API parameters in
`contDiff_zeroExtension` (`ZeroExtRegularity.lean:27`) and
`hasCompactSupport_zeroExtension` (`:48-50`); they are the same hypotheses
required by the brief's public signatures, while `hK` is used by the compact
support proof at `:52`.

## Gaps

No mathematical or build gap was found.  A whole-tree search for the five
claimed zero-extension theorem names in `formalization/NSFormalization/Section4`
returned no matches, so there is no unreported D01 duplicate to replace or
reuse.  The worker's “no named input / no placeholder” claim is consistent with
the module: there is no new `def ... : Prop`, and the module contains no
`sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` token.

The required negative check is in the reviewer-only probe
`research/T22/probes/rev408_mutation.lean:17-26`: changing the support radius
from `1/2` to `2` while retaining `closedBall 0 2 ⊆ ball 0 1` makes the original
arithmetic proof fail.  Running it produced the expected substantive error:

```
../research/T22/probes/rev408_mutation.lean:25:27: error: unsolved goals
x : Space
hx : x ∈ revWidenedK
hxnorm : ‖x‖ ≤ 2
⊢ False
```

This is a widened-interval mutation, not an argument-deletion test.

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

* `lake build NSFormalization.Section3.T22.ZeroExtRegularity` — exit 0;
  exact final line: `Build completed successfully (9879 jobs).`  The output
  contains only replayed dependency linter/deprecation warnings; no warning is
  emitted from the new module.
* `lake env lean ../formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean`
  — exit 0, no output.
* `lake env lean ../research/T22/probes/zero_ext_regularity_closes.lean` — exit
  0, no output.
* `lake env lean ../research/T22/axioms_ub2.lean` — exit 0, exact output:

  ```
  'NSFormalization.Section3.T22.contDiff_zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.hasCompactSupport_zeroExtension' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T22.memLp_zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.smoothJets_zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.exists_datum_zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
* `lake test` from `verification/` — exit 0; all contract test modules replayed
  successfully (only pre-existing dependency warnings).
* `make check` — exit 0.  Exact final checks were:

  ```
  python3 experiments/test_contract_policy.py
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.049s

  OK
  python3 experiments/check_work_queue.py
  45 work items: ownership, contract registration and task cards consistent.
  ```

  The architecture check also reports the repository-wide pre-existing
  `BoundaryCorollary.lean:90` token and `source_hashes_match: false`, but exits
  successfully; neither is in the lane diff.
* `make test-mutations` — exit 0; exact final lines:

  ```
  implementation_refactor: accepted
  admitted_proof: rejected as required
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  ```
* `git diff --check` — exit 0.  `git diff --name-only
  origin/erenup/integration-section3...HEAD` lists only the new T22 module and
  its research records; no existing Lean module is modified.  Since no file
  under `verification/` was touched, the conditional `scripts/gates.sh` /
  `check_contracts.py --base-ref origin/erenup/integration-section3` gate is not
  applicable.
