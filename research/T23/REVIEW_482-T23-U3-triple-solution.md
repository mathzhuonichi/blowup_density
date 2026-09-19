ACCEPT

## 1. What the lane claims

The worker claims the complete T23 U3 contribution: the common threshold and
three concrete inserted fields, all 18 U3 API fields, pressure normalization,
the ten-field `ClassicalSolutionOmega` constructor, and the API `solution`
existential. The claim is stated in `research/T23/REPORT_482.md:5-29`; the lane
status repeats the same scope at `research/T23/T23_SPLIT.md:95-112`.

The mathematical target is faithful to the manuscript. The source paper defines
the scaled packet at `paper/sections/03-torus.tex:101-123`, the inserted triple
and pressure normalization at `paper/sections/03-torus.tex:313-319`, the exact
momentum/cross-term computation and history at
`paper/sections/03-torus.tex:321-339`, and the bounded-domain restriction and
no-slip preservation at `paper/sections/03-torus.tex:632-655`. The canonical
Lean interface spells out precisely the same U3 fields at
`formalization/NSFormalization/Section3/T23/Boundary.lean:168-259`, matching the
original spec at `research/T23/Spec.lean:723-814`.

The lead's cross-lane ruling is satisfied. The lane does not pretend to construct
U2/I03/U4 facts: it threads the existing `LocalCorrectionCore`, packet
regularity/equation/divergence facts, and U4 no-slip equality explicitly. These
are the approved upstream field types, not gaps and not named placeholder
propositions. In particular:

- `LocalCorrectionCore` is the existing concrete record, including the two
  exact cross-transport fields, at
  `formalization/NSFormalization/Section3/T23/LocalCorrection.lean:255-303`.
- The threaded packet equation and divergence at
  `formalization/NSFormalization/Section3/T23/Solution.lean:42-47,71-76` have the
  exact types of `ScalingAPI.scaledEquation` and `scaledDivergenceFree` at
  `verification/Contracts/V1/Scaling.lean:223-233`.
- The threaded scaled velocity/pressure regularity at
  `formalization/NSFormalization/Section3/T23/Solution.lean:38-41,67-70` is
  discharged from the raw packet extension fields at
  `verification/Contracts/V1/Packet.lean:290-300` by the proved transport
  lemmas at `formalization/NSFormalization/Section3/T23/Triple.lean:133-157`.
- The only U4 input is the exact no-slip field type at
  `formalization/NSFormalization/Section3/T23/Solution.lean:48-49,77-78`, matching
  `formalization/NSFormalization/Section3/T23/Boundary.lean:271-277` and
  `research/T23/Spec.lean:826-832`.

## 2. What is in Lean

### Statement fidelity

Every declaration claimed by the report exists with the claimed statement:

- The threshold is exactly
  `min (min place.ε₀ D.ε₀) (min scalingBound geometryBound)`; positivity and all
  four projections are proved at
  `formalization/NSFormalization/Section3/T23/Triple.lean:91-129`. The canonical
  API only exposes the required placement/cutoff projections at
  `formalization/NSFormalization/Section3/T23/Boundary.lean:168-179`.
- The velocity, normalized pressure, and force definitions and their literal
  formula theorems are at
  `formalization/NSFormalization/Section3/T23/Triple.lean:95-114`. They match the
  original fields at `research/T23/Spec.lean:736-766`; the probe checks the
  registered `scaledPacket` spelling fieldwise at
  `research/T23/probes/T23-U3-triple-solution_closes.lean:1200-1216`.
- Packet regularity, global quiet history, and initial data are proved at
  `formalization/NSFormalization/Section3/T23/Triple.lean:133-175`; velocity and
  pressure slab smoothness are proved with genuine open neighborhoods at
  `formalization/NSFormalization/Section3/T23/Triple.lean:177-196`. This is the
  exact convention defined at
  `formalization/NSFormalization/Section3/T23/DomainSolution.lean:16-26` and
  required by the paper at `paper/sections/03-torus.tex:638-642`.
- Force and force-difference membership are proved for the concrete force at
  `formalization/NSFormalization/Section3/T23/Triple.lean:198-251`. Their targets
  are exactly `Boundary.lean:213-223` / `Spec.lean:768-778`.
- Incompressibility and the exact local momentum equation are proved at
  `formalization/NSFormalization/Section3/T23/Triple.lean:253-342`. The proof
  uses the existing cross terms and the same-scale packet equation, then removes
  only the spatially constant pressure shift; it does not assume the inserted
  momentum conclusion.
- Pressure normalization is genuinely peeled: positive finite volume and slice
  integrability are at
  `formalization/NSFormalization/Section3/T23/PressureNormalization.lean:11-24`,
  zero mean at `:26-38`, gradient/residual invariance at `:40-54`, finite-order
  time smoothness at `:56-84`, and the open time neighborhood and normalized
  slab result at `:86-112`. The differentiation theorem actually used is proved
  at `formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:33-61,72-90`.
- The pressure gauge and fieldwise ten-field solution constructor are at
  `formalization/NSFormalization/Section3/T23/Solution.lean:19-60`; all ten target
  fields are the canonical fields at
  `formalization/NSFormalization/Section3/T23/DomainSolution.lean:104-140` and the
  original fields at `research/T23/Spec.lean:542-578`. The API existential is at
  `formalization/NSFormalization/Section3/T23/Solution.lean:62-87` and exactly
  matches `Boundary.lean:279-287` / `Spec.lean:834-842`.

The conformance probe really embeds all 1083 lines of `research/T23/Spec.lean`
contiguously starting at probe line 2, then checks all U3 fields at
`research/T23/probes/T23-U3-triple-solution_closes.lean:1200-1280`, the exact
solution existential at `:1284-1292`, and each solution-record field at
`:1294-1314`.

### Non-vacuity and hypothesis honesty

There is no hidden `⊤.toReal = 0` route: the only relevant `toReal` denominator
is domain volume, proved strictly positive at
`formalization/NSFormalization/Section3/T23/PressureNormalization.lean:11-15`
and used nontrivially at `:31-38`. The threshold is positive under the exact
upstream positivity fields at
`formalization/NSFormalization/Section3/T23/Triple.lean:116-117`.

The reviewer probe `research/T23/probes/rev482_nonvacuity.lean:8-15` exhibits
`threshold / 2` as an element of the actual `Ioc 0 threshold`; it compiles with
zero output. The solution horizon is also nonempty because the constructor uses
`place.time_pos` at
`formalization/NSFormalization/Section3/T23/Solution.lean:50-53`. No theorem has
an empty-interval or unused-binder escape that changes the claimed result.

All additional hypotheses are isolated and honest: domain openness/boundedness/
nonemptiness are used for the pressure gauge, `hball` is used for local force
regularity, `LocalCorrectionCore` supplies U2 facts, and the packet hypotheses
are exactly the I03/raw packet facts. There is no arbitrary `Prop` parameter and
no hypothesis whose type is an inserted U3 conclusion.

## 3. Gaps

There is no residual U3 gap and no statement drift. The worker's listed assembly
inputs at `research/T23/REPORT_482.md:60-79` are precisely the cross-lane inputs
the lead instructed the reviewer to accept. U2 matching, U4 no-slip, and the I03
same-scale facts remain for U9 to instantiate; this lane proves all U3 algebra
and packaging over those inputs.

The worker report makes no "not in the tree" claim for an unproved U3 lemma, so
the mandatory Section4 missing-lemma check is not applicable. I nevertheless
ran the scoped whole-tree check for the T23-specific declarations:

```text
$ grep -rnE 'LocalCorrectionCore|ClassicalSolutionOmega|BoundaryInsertionAPI|domainNormalizePressure|InsertedTriple' formalization/NSFormalization/Section4 --include='*.lean'
exit=1 lines=0 bytes=0
```

The broader G0 registration repair and U4-U8 work explicitly disclaimed at
`research/T23/REPORT_482.md:76-79` are outside U3 and are not defects in this
lane.

No fixes are required.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every `lake` invocation ran
from `verification/` with `LEAN_NUM_THREADS=6`, one at a time.

### Builds

```text
$ lake build NSFormalization.Section3.T23.Boundary
exit=0 lines=245 bytes=14814
Build completed successfully (10087 jobs).

$ lake build NSFormalization.Section3.T23.PressureNormalization
exit=0 lines=245 bytes=14814
Build completed successfully (10088 jobs).

$ lake build NSFormalization.Section3.T23.Triple
exit=0 lines=245 bytes=14814
Build completed successfully (10089 jobs).

$ lake build NSFormalization.Section3.T23.Solution
exit=0 lines=245 bytes=14814
Build completed successfully (10090 jobs).
```

The 244 preceding lines in each build are replayed pre-existing dependency
warnings; none names any reviewed T23 module. Per the raw-output limit, here are
the exact first and last excerpts from the final build:

```text
⚠ [8778/8925] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
[... 221 replay-warning lines omitted ...]
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10083/10090] Replayed NSFormalization.Source.BoundedViscosityUniqueness
warning: NSFormalization/Source/BoundedViscosityUniqueness.lean:21:28: This simp argument is unused:
  one_smul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul, h₂, smul_add, smul_sub]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (10090 jobs).
```

Thus the reviewed modules themselves are silent.

### Direct Lean checks and conformance probe

```text
$ lake env lean ../formalization/NSFormalization/Section3/T23/PressureNormalization.lean
exit=0 lines=0 bytes=0

$ lake env lean ../formalization/NSFormalization/Section3/T23/Triple.lean
exit=0 lines=0 bytes=0

$ lake env lean ../formalization/NSFormalization/Section3/T23/Solution.lean
exit=0 lines=0 bytes=0

$ lake env lean ../research/T23/probes/T23-U3-triple-solution_closes.lean
exit=0 lines=0 bytes=0
```

### Axiom audit

```text
$ lake env lean ../research/T23/axioms_T23-U3-triple-solution.lean
exit=0 lines=74 bytes=5077
'NSFormalization.Section3.T23.domain_volume_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.SmoothOnClosedSlab.integrableOn_slice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.domainNormalizePressure_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.pressureGradient_domainNormalizePressure' depends on axioms: [propext,
[... 58 output lines omitted ...]
'NSFormalization.Section3.T23.InsertedTriple.momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.InsertedTriple.pressure_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T23.InsertedTriple.classicalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T23.InsertedTriple.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An exact whitespace-normalized audit of that output returned:

```text
declarations= 42
propext= 42
Classical.choice= 42
Quot.sound= 42
bad= []
```

Hence every one of the 42 printed declarations has exactly
`[propext, Classical.choice, Quot.sound]`.

### Repository gate

```text
$ make check
exit=0 lines=67332 bytes=2795061
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 734,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
[... 67300 output lines omitted ...]
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.MultipleRegions"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The reported `BoundaryCorollary.lean:90` admission and
`source_hashes_match: false` are repository-wide diagnostics; the gate exited
zero and the reviewed closure does not import that module.

### Negative and non-vacuity checks

```text
$ lake env lean ../research/T23/probes/rev482_nonvacuity.lean
exit=0 lines=0 bytes=0

$ lake env lean ../research/T23/probes/rev482_mutation.lean
exit=1 lines=8 bytes=236
../research/T23/probes/rev482_mutation.lean:21:23: error: Application type mismatch: The argument
  ht
has type
  t ≤ place.T - eps ^ 2
but is expected to have type
  t ≤ place.T - 2 * eps ^ 2
in the application
  history C heps ht
```

This is a substantive widening of the main quiet-history interval, not an
argument deletion, and it fails for the expected mathematical reason.

### Hygiene and git scope

```text
$ rg -n -w 'sorry|admit|axiom|native_decide' PressureNormalization.lean Triple.lean Solution.lean
(no output; exit 1)

$ rg -n 'maxHeartbeats' PressureNormalization.lean Triple.lean Solution.lean T23-U3-triple-solution_closes.lean axioms_T23-U3-triple-solution.lean
(no output; exit 1)

$ rg -n 'Paper1\.BoundaryCorollary' PressureNormalization.lean Triple.lean Solution.lean T23-U3-triple-solution_closes.lean axioms_T23-U3-triple-solution.lean
(no output; exit 1)

$ git diff --check origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
exit=0
```

The required name-only command returned:

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using b9eab7ff49606d56f033a7e76c835bf2ecbcaa5c
NEXT_SESSION.md
formalization/NSFormalization/Section3/T23/Boundary.lean
formalization/NSFormalization/Section3/T23/Geometry.lean
formalization/NSFormalization/Section3/T23/PressureNormalization.lean
formalization/NSFormalization/Section3/T23/Solution.lean
formalization/NSFormalization/Section3/T23/Triple.lean
formalization/NSFormalization/Section3/T23/WholeSpaceCorrection.lean
research/T23/ATTEMPTS_T23-U3-triple-solution.md
research/T23/ATTEMPTS_UCAN.md
research/T23/REPORT_480.md
research/T23/REPORT_482.md
research/T23/SPEC_ISSUES.md
research/T23/T23_SPLIT.md
research/T23/axioms_T23-U3-triple-solution.lean
research/T23/axioms_T23-U3-triple-solution.log
research/T23/axioms_ucan.lean
research/T23/probes/T23-U3-triple-solution_closes.lean
research/T23/probes/boundary_api_on_canonical.lean
research/T23/validation_T23-U3-triple-solution.log
```

The multiple-base result includes the inherited lane-480 additions. All six
formalization paths are status `A`, not modifications of existing modules. From
lane 482's actual parent `bd2f3b47`, the exact formalization delta is only:

```text
A formalization/NSFormalization/Section3/T23/PressureNormalization.lean
A formalization/NSFormalization/Section3/T23/Solution.lean
A formalization/NSFormalization/Section3/T23/Triple.lean
```

`git diff --name-only origin/erenup/integration-section3...HEAD -- verification`
produced no paths (only the same multiple-merge-base warning). Therefore
`verification/` was not touched, and the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply to this lane.
