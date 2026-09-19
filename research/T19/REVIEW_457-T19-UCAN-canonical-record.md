ACCEPT

## 1. What the lane claims

The worker claims a statement-only canonical restatement of the four reconciled
T19 records, with field counts `3/3/4/3`, the four headline statement aliases,
and no residual field gap (`research/T19/REPORT_457.md:5`,
`research/T19/REPORT_457.md:43`).  It also claims that the five record fields
already proved in lane 388 and both U6 helper lemmas have their literal field or
consumer types (`research/T19/REPORT_457.md:12`).

Those claims are accurate:

- `PeriodicDensityAPI` has exactly `fixedInitialDensity`, `thresholdValue`, and
  `regularReferenceSingular`, followed by the expected headline alias
  (`formalization/NSFormalization/Section3/T19/Density.lean:71`,
  `formalization/NSFormalization/Section3/T19/Density.lean:97`).
- `MixedRegionAPI` has exactly `mixedDensity`, `mixedRegionArithmetic`, and
  `regionExamples`, followed by its headline alias
  (`formalization/NSFormalization/Section3/T19/Density.lean:110`,
  `formalization/NSFormalization/Section3/T19/Density.lean:134`).
- `StrongClosureAPI` has exactly the four reconciled fields, followed by its
  headline alias (`formalization/NSFormalization/Section3/T19/Density.lean:149`,
  `formalization/NSFormalization/Section3/T19/Density.lean:203`).
- `ProjectionAPI` has exactly the three reconciled fields, followed by its
  headline alias (`formalization/NSFormalization/Section3/T19/Density.lean:219`,
  `formalization/NSFormalization/Section3/T19/Density.lean:249`).

Statement fidelity is exact.  The Spec has the same density threshold and
exact-lifespan clauses (`research/T19/Spec.lean:207`,
`research/T19/Spec.lean:240`), the same mixed fields
(`research/T19/Spec.lean:281`, `research/T19/Spec.lean:301`,
`research/T19/Spec.lean:318`), the same four closure fields
(`research/T19/Spec.lean:352`, `research/T19/Spec.lean:370`,
`research/T19/Spec.lean:395`, `research/T19/Spec.lean:428`), and the same three
projection fields (`research/T19/Spec.lean:471`,
`research/T19/Spec.lean:492`, `research/T19/Spec.lean:508`).  The compiled probe
performs both fieldwise conversion directions for all four records
(`research/T19/probes/api_on_canonical.lean:357`,
`research/T19/probes/api_on_canonical.lean:378`,
`research/T19/probes/api_on_canonical.lean:400`,
`research/T19/probes/api_on_canonical.lean:412`,
`research/T19/probes/api_on_canonical.lean:425`,
`research/T19/probes/api_on_canonical.lean:452`,
`research/T19/probes/api_on_canonical.lean:481`,
`research/T19/probes/api_on_canonical.lean:497`) and proves equality of all four
headline propositions (`research/T19/probes/api_on_canonical.lean:556`,
`research/T19/probes/api_on_canonical.lean:573`,
`research/T19/probes/api_on_canonical.lean:590`,
`research/T19/probes/api_on_canonical.lean:604`).

The cited mathematics also agrees with the source.  The paper states fixed-`a`
density with `s<1/2` and breakdown by `T`
(`paper/sections/03-torus.tex:349`), while exact lifespan `T` is reserved for
the regular-reference case (`paper/sections/03-torus.tex:363`,
`paper/sections/03-torus.tex:589`).  It gives the strict mixed region and its
two examples (`paper/sections/03-torus.tex:528`,
`paper/sections/03-torus.tex:538`), the energy closure and simultaneous pair
convergence (`paper/sections/03-torus.tex:540`,
`paper/sections/03-torus.tex:546`), and the fixed-initial-data product-density
argument with quantifier order `forall a, exists f`
(`paper/sections/03-torus.tex:564`, `paper/sections/03-torus.tex:573`,
`paper/sections/03-torus.tex:579`).  The local trajectory, breakdown, and mixed
density definitions in Lean (`formalization/NSFormalization/Section3/T19/Density.lean:33`,
`formalization/NSFormalization/Section3/T19/Density.lean:40`,
`formalization/NSFormalization/Section3/T19/Density.lean:51`,
`formalization/NSFormalization/Section3/T19/Density.lean:57`) have the intended
paper meanings.

## 2. What is in Lean

All four records are `Prop`-valued and use the approved canonical vocabulary.
The only non-definitional seam is honest: the contract and canonical
`ClassicalSolutionT` types are distinct structures, transported fieldwise by
`toContract`/`ofContract` (`verification/Bindings/TorusLocalTheory.lean:198`,
`verification/Bindings/TorusLocalTheory.lean:216`), and lifespan equality is a
proved `iSup` transport rather than `rfl`
(`verification/Bindings/TorusLocalTheory.lean:270`).  The probe uses that bridge
at every lifespan-bearing conversion
(`research/T19/probes/api_on_canonical.lean:367`,
`research/T19/probes/api_on_canonical.lean:434`).

The seven lane-388 seam examples have the literal types used by the records or
their density proof branches (`formalization/NSFormalization/Section3/T19/Density.lean:268`,
`formalization/NSFormalization/Section3/T19/Density.lean:270`,
`formalization/NSFormalization/Section3/T19/Density.lean:276`,
`formalization/NSFormalization/Section3/T19/Density.lean:281`,
`formalization/NSFormalization/Section3/T19/Density.lean:287`,
`formalization/NSFormalization/Section3/T19/Density.lean:296`,
`formalization/NSFormalization/Section3/T19/Density.lean:300`).  Their sources
are the named Bookkeeping theorems
(`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:55`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:58`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:66`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:73`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:154`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:238`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:258`).

No hypothesis was silently added.  Positivity is present exactly where the
paper and Spec require it; distances stay in `ENNReal`; no `.toReal` is used to
collapse a norm; and the mixed region is not empty because the concrete
`(p,q)=(2,1)` and `(4/3,2)` inequalities are fields proved by the named theorem
(`formalization/NSFormalization/Section3/T19/Density.lean:126`,
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:66`).  The reviewer
probe additionally constructs simultaneous witnesses `a=0`, `g=0`,
`nu=T=r=1`, `s=0`, proving that the principal class, positivity, radius, and
subcritical hypotheses are inhabited
(`research/T19/probes/rev457_statement_checks.lean:22`,
`research/T19/probes/rev457_statement_checks.lean:30`,
`research/T19/probes/rev457_statement_checks.lean:41`).

## 3. Gaps

There is no correctness gap.  The worker explicitly declares no unrestated
field (`research/T19/REPORT_457.md:41`), so there is no missing-lemma claim to
accept or reject under the whole-Section4 grep rule.  As an additional check,
the whole-tree search for identically named T19 records and statement aliases
returned no matches; this confirms that the new canonical declarations are not
shadowing an existing Section4 declaration.

Hygiene is clean.  Against `origin/erenup/integration-section3`, the only Lean
module change is the newly added `Density.lean`; the other committed paths are
the requested research deliverables.  No changed/reviewer Lean file contains a
`sorry`, `admit`, `native_decide`, `axiom`/`opaque` declaration, or a
`maxHeartbeats` override.  The status edit is the requested U-CAN line
(`research/T19/T19_SPLIT.md:15`), and the worker report accurately records the
standard axiom footprint (`research/T19/REPORT_457.md:57`).

The negative test is substantive: it widens the main density threshold from
`s < 1/2` to `s < 3/5`, without dropping an argument
(`research/T19/probes/rev457_statement_checks.lean:50`).  Re-enabling the
unchanged conformance line at `:57` makes `rfl` fail with the expected type
mismatch.  The final probe keeps that expected-failure line commented and
otherwise elaborates with zero output.

## 4. Commands and results

All Lean commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Build and direct elaboration

```text
$ lake build NSFormalization.Section3.T19.Density
Build completed successfully (10043 jobs).
```

The unfiltered build also replayed pre-existing dependency warnings; it emitted
no warning from `NSFormalization/Section3/T19/Density.lean` and exited 0.  The
exact direct-module result was empty:

```text
$ lake env lean ../formalization/NSFormalization/Section3/T19/Density.lean
```

Exit 0, zero output.

### Spec/canonical probe

```text
$ lake env lean ../research/T19/probes/api_on_canonical.lean
'T19CanonicalProbe.criticalOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.alpha_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodicTorusMeasure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.torusLift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.initialClassT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.forceClassT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.forceSobolevENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.relativelyDenseT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.energyEssSupT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.energyENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixedSlicePath_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixedLebesgueENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.spaceTimeL2L2ENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.relativelyDenseMixedT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.limsupLeft_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.speedENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.maximalLifespanT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.regularThroughT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.breakdownSetT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.regularTrajectoryT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.singularTrajectoryT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.extendedBreakdownSetT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodicToCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodicOfCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixedToCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixedOfCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.strongToCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.strongOfCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.projectionToCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.projectionOfCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodic_roundTrip_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodic_roundTrip_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixed_roundTrip_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixed_roundTrip_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.strong_roundTrip_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.strong_roundTrip_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.projection_roundTrip_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.projection_roundTrip_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.regularTrajectoryT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.singularTrajectoryT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.periodicDensityStatement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.mixedRegionStatement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.strongClosureStatement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T19CanonicalProbe.projectionStatement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.  Every one of the 44 printed declarations has exactly the required
axiom list.

### Dedicated axiom audit

```text
$ lake env lean ../research/T19/axioms_ucan.lean
'NSFormalization.Section3.T19.RegularTrajectoryT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.SingularTrajectoryT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.extendedBreakdownSetT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.RelativelyDenseMixedT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.PeriodicDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.periodicDensityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.MixedRegionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.mixedRegionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.StrongClosureAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.strongClosureStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.ProjectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.projectionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.  All 12 declarations have exactly the required axiom list.

### Reviewer non-vacuity and negative mutation

With the expected-failure line commented:

```text
$ lake env lean ../research/T19/probes/rev457_statement_checks.lean
```

Exit 0, zero output.  With the `s < 3/5` mutation's `rfl` line enabled, the
exact decisive error was:

```text
../research/T19/probes/rev457_statement_checks.lean:56:72: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  widenedPeriodicDensityStatement = periodicDensityStatement
```

Exit 1 as expected.  (The saved, commented probe moved that line to `:57`.)

### Repository gates and hygiene

```text
$ make check
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.ConservativeForcing"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Exit 0.  The displayed block is the exact retained tail of the otherwise very
large contract-closure JSON; the unfiltered command was also run and exited 0.

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T19/Density.lean
research/T19/ATTEMPTS_UCAN.md
research/T19/REPORT_457.md
research/T19/T19_SPLIT.md
research/T19/axioms_ucan.lean
research/T19/probes/api_on_canonical.lean
```

Exit 0.  `git diff --check` exited 0 with zero output.  The forbidden-token
and `maxHeartbeats` scans returned no matches.  The whole-Section4 declaration
search returned no matches (exit 1, zero output).

`verification/` is absent from the diff above, so the brief's conditional
`scripts/gates.sh` and explicit
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply.  `make check` nevertheless ran the ordinary contract architecture
checker successfully.
