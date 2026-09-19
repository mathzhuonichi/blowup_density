ACCEPT

## 1. What the lane claims

The worker claims the canonical T21 implementation of units N0--N10 and N12:
the eight theorem endpoints which, together with `K.hc`, populate the nine
fields of `NonDensityAPI`, five supporting endpoints, and the assembled
`nonDensityAPI` (`research/T21/REPORT_472.md:3-76`).  It claims no residual
mathematical or Lean goal in those units and leaves registration to its
separate lane (`research/T21/REPORT_472.md:100-103`).

That scope is faithful to the brief.  The paper states the positive critical
constant and its small-force global-regularity implication at
`paper/sections/03-torus.tex:383-389`, then proves non-density for every
`s >= 1/2` and `T > 0` by a nonempty relatively open ball, Sobolev
monotonicity, and disjointness at `paper/sections/03-torus.tex:506-520`.
The zero-datum breakdown set is exactly the paper's definition at
`paper/sections/02-preliminaries.tex:38-43`.  The canonical definitions and all
nine record fields occur at
`formalization/NSFormalization/Section3/T21/Definitions.lean:23-63` and match
the reconciled spec at `research/T21/Spec.lean:215-216,269-438`; the registered
shape probe closes every field by `exact` at
`research/T21/probes/nondensity_closes.lean:113-176`.

No silent premise or vacuity was found.  The parameter `K` is the actual T20
record, whose positive constant is declared at
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:139-150`
and whose global-regularity field is at the same file's `:365-368`; it is not a
named placeholder.  The ball radius is positive through `K.hc` and `hnu`, as
used at `formalization/NSFormalization/Section3/T21/NonDensity.lean:25-28`.
The locally unused paper hypotheses in the stronger helper proofs are honest:
ball membership itself gives the strict positive residual radius at
`formalization/NSFormalization/Section3/T21/Ball.lean:57-61`, while the
critical disjointness contradiction works for every finite `ENNReal.ofReal T`
at `formalization/NSFormalization/Section3/T21/Disjointness.lean:24-32`.
There is no `toReal` shortcut or empty-interval premise anywhere in the lane.

## 2. What is in Lean

Every declaration claimed in the worker report exists with the displayed
type:

| Claimed endpoint | Lean declaration |
|---|---|
| `criticalGlobalRegularity` | `formalization/NSFormalization/Section3/T21/CriticalBridge.lean:24-30` |
| `zeroMemBall` | `formalization/NSFormalization/Section3/T21/Zero.lean:33-38` |
| `ballRelativelyOpen` | `formalization/NSFormalization/Section3/T21/Ball.lean:52-77` |
| `sliceSobolevMonotone` | `formalization/NSFormalization/Section3/T21/OrderLowering.lean:54-66` |
| `forceSobolevMonotone` | `formalization/NSFormalization/Section3/T21/ForceMonotonicity.lean:20-23` |
| `criticalBallDisjoint` | `formalization/NSFormalization/Section3/T21/Disjointness.lean:20-32` |
| `ballDisjoint` | `formalization/NSFormalization/Section3/T21/Disjointness.lean:36-46` |
| `nonDensity` | `formalization/NSFormalization/Section3/T21/NonDensity.lean:20-32` |
| `reweightContraction` | `formalization/NSFormalization/Section3/T21/OrderLowering.lean:31-39` |
| `exists_orderLoweringDatum` | `formalization/NSFormalization/Section3/T21/OrderLowering.lean:43-51` |
| `zero_mem_forceClassT` | `formalization/NSFormalization/Section3/T21/Zero.lean:20-25` |
| `forceSobolevENormT_zero` | `formalization/NSFormalization/Section3/T21/Zero.lean:28-30` |
| `zeroInitialClass` | `formalization/NSFormalization/Section3/T21/Zero.lean:41-42` |
| `nonDensityAPI` | `formalization/NSFormalization/Section3/T21/Assembly.lean:16-27` |

The supplier claims are also accurate: the force triangle inequality is
`formalization/NSFormalization/Section3/T18/SobolevRate.lean:116-136`, its
order-lowering contraction is `:139-148`, force-norm monotonicity is
`formalization/NSFormalization/Section3/T15/Convergence.lean:42-55`, the zero
force norm is `formalization/NSFormalization/Section3/T19/Bookkeeping.lean:236-250`,
and zero initial data is
`formalization/NSFormalization/Section3/T20/CriticalEnergy.lean:402-407`.
The registered/canonical lifespan and breakdown-set seams cited in the report
exist at `verification/Bindings/TorusLocalTheory.lean:270-274,284-297`.

The closed package is non-vacuous.  The reviewer probe constructs
`Nonempty (NonDensityAPI criticalRegularityT.c)` and then exhibits a positive
viscosity and a nonzero admissible force lying in the critical ball with
infinite lifespan at
`research/T21/probes/rev472_nonvacuity.lean:13-27`.  This uses the concrete T20
nonzero witness proved at
`formalization/NSFormalization/Section3/T20/Assembly.lean:133-162`, not merely
the zero force.

The negative check substantively widens the conclusion from `s >= 1/2` to
`s >= 1/4` at `research/T21/probes/rev472_negative.lean:13-19`.  Reusing the
lane theorem fails for the expected changed constant:

```text
../research/T21/probes/rev472_negative.lean:19:2: error: Type mismatch
  nonDensity K
has type
  ∀ (ν : ℝ), 0 < ν → ∀ (s : ℝ), 1 / 2 ≤ s → ∀ (T : ℝ), 0 < T → ¬RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)
but is expected to have type
  ∀ (nu : ℝ),
    0 < nu → ∀ (s : ℝ), 1 / 4 ≤ s → ∀ (T : ℝ), 0 < T → ¬RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)
```

## 3. Gaps

There is no gap in the assigned N0--N10/N12 scope.  The worker's only remaining
item is registration, explicitly excluded from this lane by both the report
and status note (`research/T21/REPORT_472.md:102-103` and
`research/T21/T21_SPLIT.md:8-15`).  It does not claim that a mathematical lemma
is absent from the tree.

For completeness, the required whole-tree search was run over
`formalization/NSFormalization/Section4` for
`NonDensityAPI|nonDensityOfCritical|TorusNonDensity|criticalGlobalRegularity|zeroInitialClass`;
its exact output was empty.  Thus there is no overlooked Section 4 declaration
under any of the names relevant to the stated registration gap.

Hygiene is clean.  The forbidden-token/per-declaration-heartbeat scan over all
nine new modules, the delivered probes/audit, and both reviewer probes produced
no output.  There is no lane-local heartbeat override.  The requested
three-dot comparison marks every T21 Lean module `A`, never `M`; the only
modified pre-existing file is the permitted status record
`research/T21/T21_SPLIT.md`.  The base branch contains no T21 path.  The exact
Lean-module name-status output was:

```text
A formalization/NSFormalization/Section3/T21/Assembly.lean
A formalization/NSFormalization/Section3/T21/Ball.lean
A formalization/NSFormalization/Section3/T21/CriticalBridge.lean
A formalization/NSFormalization/Section3/T21/Definitions.lean
A formalization/NSFormalization/Section3/T21/Disjointness.lean
A formalization/NSFormalization/Section3/T21/ForceMonotonicity.lean
A formalization/NSFormalization/Section3/T21/NonDensity.lean
A formalization/NSFormalization/Section3/T21/OrderLowering.lean
A formalization/NSFormalization/Section3/T21/Zero.lean
```

`git diff --check origin/erenup/integration-section3...HEAD` produced no
output.  No file under `verification/` was touched.

## 4. Commands and results

Environment installation completed successfully with Lean
`v4.34.0-rc2`; its exact final line was:

```text
== OK
```

From `verification/`, the nine-target build command was:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T21.Definitions NSFormalization.Section3.T21.CriticalBridge NSFormalization.Section3.T21.OrderLowering NSFormalization.Section3.T21.ForceMonotonicity NSFormalization.Section3.T21.Zero NSFormalization.Section3.T21.Ball NSFormalization.Section3.T21.Disjointness NSFormalization.Section3.T21.NonDensity NSFormalization.Section3.T21.Assembly
```

It exited 0.  Lake replayed existing warnings from upstream files only; there
was no warning or error from a T21 module.  The exact final output line was:

```text
Build completed successfully (10689 jobs).
```

Each of the following was then run separately with
`LEAN_NUM_THREADS=6 lake env lean`; all exited 0 with exact output `(empty)`:

```text
../formalization/NSFormalization/Section3/T21/Definitions.lean
../formalization/NSFormalization/Section3/T21/CriticalBridge.lean
../formalization/NSFormalization/Section3/T21/OrderLowering.lean
../formalization/NSFormalization/Section3/T21/ForceMonotonicity.lean
../formalization/NSFormalization/Section3/T21/Zero.lean
../formalization/NSFormalization/Section3/T21/Ball.lean
../formalization/NSFormalization/Section3/T21/Disjointness.lean
../formalization/NSFormalization/Section3/T21/NonDensity.lean
../formalization/NSFormalization/Section3/T21/Assembly.lean
../research/T21/Spec.lean
../research/T21/probes/nondensity_closes.lean
../research/T21/probes/rev472_nonvacuity.lean
```

The deliberate negative probe exited 1 with the exact type mismatch pasted in
part 2.  The axiom audit exited 0 with exact output:

```text
'NSFormalization.Section3.T21.breakdownSetTZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.criticalBallT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.NonDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.criticalGlobalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.reweightContraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.exists_orderLoweringDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.sliceSobolevMonotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.forceSobolevMonotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.zero_mem_forceClassT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.forceSobolevENormT_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.zeroMemBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.memForceT_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.memForceT_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.memForceSobolevT_of_memForceT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.ballRelativelyOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.criticalBallDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.ballDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.zeroInitialClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensityAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensityOfCritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensityOfCritical_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T21.nonDensityStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` exited 0.  Its exact
concluding checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Finally,
`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T21.Assembly`
exited 0.  This also reran `make check`, the targeted build, `make test`, the
mutation suite, and the base-ref contract check.  Its exact final output was:

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

An explicit
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
also exited 0 and reported `"base_compatibility_checked": true`.  This was
extra coverage: the lane did not modify `verification/`.
