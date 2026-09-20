ACCEPT-WITH-NOTES

Exact one-line fixes before merge:

1. Insert `set_option linter.defProp false` immediately after the namespace declaration at `formalization/NSFormalization/Section3/T19/Assembly.lean:14`; the brief requires these four `Prop` packages to remain `def`s, and this makes the required direct-Lean gate produce zero output.
2. Replace `research/T19/REPORT_470.md:93-96` with the single line: `The required Prop-valued API defs use a module-local defProp-linter suppression, so direct elaboration and the lane's build/test output contain no Assembly warnings.`

## 1. What the lane claims

The worker claims one new V1 registration, `T03.density`, containing four
`Prop` records with 3/3/4/3 fields and four headline statements
(`research/T19/REPORT_470.md:3-54`).  The claimed statements are:

- fixed-initial density for every `a ∈ initialClassT`, `ν>0`, `T>0`, and
  `s<1/2` in the relative `L¹_t H^s_x` pseudometric
  (`research/T19/REPORT_470.md:9-15`);
- mixed-norm density when `1≤p,q` and `3/p+2/q>3`
  (`research/T19/REPORT_470.md:17-24`);
- epsilon-form closure of regular trajectories by finite-energy singular
  trajectories in `E_T` (`research/T19/REPORT_470.md:26-34`); and
- fixed-`a` product density together with projection onto all of
  `initialClassT` (`research/T19/REPORT_470.md:36-47`).

The worker also claims the auxiliary threshold, exact-lifespan,
mixed-arithmetic/examples, simultaneous-convergence, reference-finiteness,
finite-time embedding, and zero-initial projection fields
(`research/T19/REPORT_470.md:49-54`), a concrete zero-datum/zero-force
instance (`research/T19/REPORT_470.md:68-71`), and exactly the three standard
logical axioms (`research/T19/REPORT_470.md:114-119`).

## 2. What is in Lean

### Statement fidelity

All four headline statements exist with exactly the types printed in the
worker report.  Their canonical definitions are at
`formalization/NSFormalization/Section3/T19/Density.lean:97-101`,
`:134-139`, `:203-209`, and `:249-258`; the contract copies are at
`verification/Contracts/V1/Density.lean:98-102`, `:127-132`, `:183-189`, and
`:218-227`.  The four canonical closing theorems are present at
`formalization/NSFormalization/Section3/T19/Assembly.lean:41-57`, and the four
contract-spelling closing theorems are present at
`verification/Bindings/Density.lean:168-182`.  The public checks and aggregate
conjunction are exactly as claimed at `verification/Tests/Density.lean:20-51`.

The statements match the paper:

- `prop:density` quantifies `a,ν,T,s` and concludes
  `∀g∀ρ∃f` with strict norm distance and breakdown by `T` at
  `paper/sections/03-torus.tex:349-355`; Lean's `RelativelyDenseT` expands to
  precisely `∀ g∈Y, ∀ r>0, ∃ f∈S, ... < r` at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:321-325`, and
  `breakdownSetT` contains force membership plus lifespan `≤ ofReal T` at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:312-319`.
- `cor:mixed` states the same density in the region `1≤p,q≤∞` and
  `3/p+2/q>3` at `paper/sections/03-torus.tex:528-538`; the Lean field and
  headline use the same inequality and quantifier order at
  `formalization/NSFormalization/Section3/T19/Density.lean:110-139`.
- `cor:closure` defines the regular and singular trajectory classes and the
  `E_T` closure/concurrent force convergence at
  `paper/sections/03-torus.tex:540-561`; the Lean predicates are at
  `formalization/NSFormalization/Section3/T19/Density.lean:31-47`, and the
  four-field record is at `:149-199`.
- `prop:projection` defines the extended breakdown set, fixed-`a` density,
  full projection, and zero fibre at `paper/sections/03-torus.tex:564-576`,
  with the important `∀a∃f` warning at `:579-590`; Lean keeps `a` fixed in
  `formalization/NSFormalization/Section3/T19/Density.lean:219-258`.

The citations are current: the exact-time distinction really is at paper
line 590, the singleton remark at line 586, and the peaks remark starts at
line 591 (`paper/sections/03-torus.tex:586-597`).

The assembly fills all thirteen record fields by the named proved theorems at
`formalization/NSFormalization/Section3/T19/Assembly.lean:16-39`.  The source
theorem signatures agree field-for-field: arithmetic/embedding/finiteness at
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:55-76` and
`:154-160`; density fields at
`formalization/NSFormalization/Section3/T19/DensityEngine.lean:23-70`;
simultaneous convergence and closure at
`formalization/NSFormalization/Section3/T19/Closure.lean:64-85` and
`:141-148`; projection fields at
`formalization/NSFormalization/Section3/T19/Projection.lean:21-62`.

The contract uses the registered vocabulary, not a silent mirror.  Its mixed
norm and local definitions are guarded by `rfl` at
`verification/Bindings/Density.lean:30-46`.  The two trajectory predicates
are transported fieldwise at `verification/Bindings/Density.lean:48-74` using
the registered conversions defined at
`verification/Bindings/TorusLocalTheory.lean:198-225`; lifespan and regularity
use the non-definitional registered bridges at
`verification/Bindings/TorusLocalTheory.lean:270-282`.  Every occurrence in
the four records is handled at `verification/Bindings/Density.lean:90-166`.

No vacuity was found.  The headline fields retain positive `ν`, `T`, and
radius hypotheses; the relevant time/scale intervals are nonempty because
their endpoints are proved positive; and all closeness conclusions are
strict inequalities in `ℝ≥0∞`, so `⊤.toReal = 0` cannot discharge a norm
claim.  The mixed field is not empty: its two advertised points are proved at
`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:66-69`.  The
zero-data probe proves actual class membership and extracts a genuine force
witness at `ν=T=1`, `s=0`, radius `1` in
`research/T19/probes/assembly_closes.lean:22-58`; it contains no `True` proxy.
The auxiliary `referenceFiniteEnergy` proof deliberately does not use class
membership or viscosity positivity directly, but its conclusion still
depends on the supplied `ClassicalSolutionT` witness
(`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:154-172`), so
this is not a vacuous named premise.

Registration is honest: the entry is version 1 under T03 and names the new
spec/binding/test/declaration at `verification/contracts.json:544-552`; T19's
work item contains exactly `T03.density` at
`collaboration/work_items.json:392-399`.  The base has 50 contracts and this
branch has 51.  The three contract modules and the canonical Assembly module
are all absent from the base, so no pre-existing Lean module was modified.

### Hygiene and negative/non-vacuity checks

The lane diff contains no declaration-level `sorry`, `admit`, `axiom`, or
`native_decide`, and no `maxHeartbeats`.  `git diff --check` is empty.  The
only modified pre-existing files are registry/task/research records; every
Lean source in the lane diff is new.  The imports in
`verification/Contracts/V1/Density.lean:1-4` obey the contract import policy.

The substantive reviewer mutation is
`research/T19/probes/rev470_widened_threshold.lean:16-22`: it widens the main
range from `s<1/2` to `s<3/2` while keeping every argument.  Lean rejects it
at the changed conclusion, not because an argument was dropped:

```text
../research/T19/probes/rev470_widened_threshold.lean:22:2: error: Type mismatch
  periodicDensityStatement_holds
has type
  periodicDensityStatement
but is expected to have type
  ∀ a ∈ initialClassT,
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → ∀ s < 3 / 2, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
```

## 3. Gaps

There is no mathematical, registration, non-vacuity, or axiom gap.  The sole
merge note is output hygiene: direct elaboration of the assembly is not the
required zero-output command, and the same four warnings are replayed by the
build and test.  They originate at
`formalization/NSFormalization/Section3/T19/Assembly.lean:16`, `:22`, `:28`,
and `:35`.  Because the brief explicitly requires `def`, the exact fix is the
one module-local linter option stated above, not changing the declarations to
`theorem`.  The worker report's assertion that these are not build/test
warnings (`research/T19/REPORT_470.md:93-96`) is contradicted by the reproduced
`make test` output below and must be updated after the code fix.

The worker report declares no “not in the tree” proof gap
(`research/T19/REPORT_470.md:83-96`).  As a defensive check, whole-tree
searches under `formalization/NSFormalization/Section4` for
`CriticalRegularityT`, `peak`, and either ordering of
`TopologicalSpace.*initialClassT` returned no matches.  `non-density` has only
the unrelated Section4 R41 files
`formalization/NSFormalization/Section4/R41/NonDensity.lean:4`,
`NonDensityL1.lean:3`, and `NonDensityL2.lean:3`; generic `amplitude` matches
occur only in unrelated B02/I03 scaling files.  Thus none supplies an omitted
T19 field.

Exact relevant search output:

```text
$ grep -rn -E 'CriticalRegularityT|peak|TopologicalSpace.*initialClassT|initialClassT.*TopologicalSpace' formalization/NSFormalization/Section4
$ grep -rn -E 'non-density' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/R41/NonDensityL1.lean:3:/-! Theorem 4.1(ii), the non-density direction for q = 1.
formalization/NSFormalization/Section4/R41/NonDensityL2.lean:3:/-! Theorem 4.1(ii), the q = 2 non-density clause.
formalization/NSFormalization/Section4/R41/NonDensity.lean:4:/-! Theorem 4.1(ii), the non-density direction simultaneously for `q = 1, 2`.
```

## 4. Commands and results

All Lean/Lake commands used `. scripts/lean-env.sh`, set
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.

Closure build:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Projection NSFormalization.Section3.T19.Closure NSFormalization.Section3.T19.DensityEngine
Build completed successfully (10660 jobs).
```

The command exited 0; preceding output consisted only of replayed upstream
warnings.  Assembly build exited 0, with this exact lane-local tail:

```text
⚠ [10661/10661] Replayed NSFormalization.Section3.T19.Assembly
warning: NSFormalization/Section3/T19/Assembly.lean:16:0: Definition `periodicDensityAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
warning: NSFormalization/Section3/T19/Assembly.lean:22:0: Definition `mixedRegionAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
warning: NSFormalization/Section3/T19/Assembly.lean:28:0: Definition `strongClosureAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
warning: NSFormalization/Section3/T19/Assembly.lean:35:0: Definition `projectionAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
Build completed successfully (10661 jobs).
```

Direct module elaboration exited 0 but failed the zero-output requirement:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T19/Assembly.lean
../formalization/NSFormalization/Section3/T19/Assembly.lean:16:0: warning: Definition `periodicDensityAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
../formalization/NSFormalization/Section3/T19/Assembly.lean:22:0: warning: Definition `mixedRegionAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
../formalization/NSFormalization/Section3/T19/Assembly.lean:28:0: warning: Definition `strongClosureAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
../formalization/NSFormalization/Section3/T19/Assembly.lean:35:0: warning: Definition `projectionAPI` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
```

`make check` exited 0.  Exact final output:

```text
      "Tests.Scaling3"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

`make test` exited 0.  Exact T19 lines:

```text
warning: NSFormalization/Section3/T19/Assembly.lean:16:0: Definition `periodicDensityAPI` is a proposition; use `theorem` instead of `def`
warning: NSFormalization/Section3/T19/Assembly.lean:22:0: Definition `mixedRegionAPI` is a proposition; use `theorem` instead of `def`
warning: NSFormalization/Section3/T19/Assembly.lean:28:0: Definition `strongClosureAPI` is a proposition; use `theorem` instead of `def`
warning: NSFormalization/Section3/T19/Assembly.lean:35:0: Definition `projectionAPI` is a proposition; use `theorem` instead of `def`
info: Tests/Density.lean:24:0: Contract BlowupDensity.Tests.checkedPeriodicDensity: checked; standard logical axioms only
info: Tests/Density.lean:30:0: Contract BlowupDensity.Tests.checkedMixedRegion: checked; standard logical axioms only
info: Tests/Density.lean:36:0: Contract BlowupDensity.Tests.checkedStrongClosure: checked; standard logical axioms only
info: Tests/Density.lean:42:0: Contract BlowupDensity.Tests.checkedProjection: checked; standard logical axioms only
info: Tests/Density.lean:51:0: Contract BlowupDensity.Tests.checkedDensity: checked; standard logical axioms only
```

`make test-mutations` exited 0.  Exact tail:

```text
info: Tests/CriticalRegularityT.lean:25:0: Contract BlowupDensity.Tests.checkedCriticalRegularityT: checked; standard logical axioms only
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

Base compatibility exited 0:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3 | rg '"registered_contracts"|"base_compatibility_checked"|"scope"'
  "registered_contracts": 51,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

The non-vacuity probe exited 0 with exact output:

```text
'BlowupDensity.T19.AssemblyProbe.zeroInitial_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T19.AssemblyProbe.zeroForce_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T19.AssemblyProbe.zeroDensity_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T19.AssemblyProbe.densityForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T19.AssemblyProbe.densityForce_breaksByOne' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T19.AssemblyProbe.densityForce_closeToZero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The axiom file exited 0.  Every printed declaration had exactly the required
set; exact output:

```text
'NSFormalization.Section3.T19.periodicDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.mixedRegionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.strongClosureAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.projectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.periodicDensityStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.mixedRegionStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.strongClosureStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.projectionStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.RegularTrajectoryT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.SingularTrajectoryT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.extendedBreakdownSetT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.spaceTimeL2L2ENormT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.RelativelyDenseMixedT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.PeriodicDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.MixedRegionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.StrongClosureAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.ProjectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.periodicDensityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.mixedRegionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.strongClosureStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.Density.projectionStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.criticalOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.mixedLebesgueENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.spaceTimeL2L2ENormT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.relativelyDenseMixedT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.regularTrajectory_toCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Density.regularTrajectory_toContract' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.singularTrajectory_toCanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Density.singularTrajectory_toContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Density.extendedBreakdownSetT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.periodicDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.mixedRegionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.strongClosureAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.projectionAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.periodicDensityStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.Density.mixedRegionStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.strongClosureStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.Density.projectionStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedPeriodicDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedMixedRegion' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedStrongClosure' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full standard gate script was run as
`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T19.Assembly` and exited 0.  Its exact final section was:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

Final hygiene command
`git diff --check origin/erenup/integration-section3...HEAD`, the
declaration-level forbidden-token scan, and the `maxHeartbeats` scan all exited
0 with no output.  The pre-existing uncommitted modification to
`collaboration/briefs/470-T19-U15-assembly-registration.md` was present before
review and was left untouched; the only reviewer additions are this report and
`research/T19/probes/rev470_widened_threshold.lean`.

The exact committed lane file list used for the existing-module check was:

```text
collaboration/TASKS.md
collaboration/tasks/T19.md
collaboration/work_items.json
formalization/NSFormalization/Section3/T19/Assembly.lean
research/T19/ATTEMPTS_U15.md
research/T19/REPORT_470.md
research/T19/T19_SPLIT.md
research/T19/axioms_u15.lean
research/T19/probes/assembly_closes.lean
verification/Bindings/Density.lean
verification/Contracts/V1/Density.lean
verification/Tests/Density.lean
verification/contracts.json
```

`git cat-file -e origin/erenup/integration-section3:<path>` returned absent for
all four Lean modules in that list, and direct JSON counting printed:

```text
base_contracts=50
current_contracts=51
```
