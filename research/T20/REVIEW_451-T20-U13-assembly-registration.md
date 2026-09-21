ACCEPT

## 1. What the lane claims

The worker claims a canonical inhabitant of the reconciled 23-field
`CriticalRegularityTAPI`, the existential statement form, a registered V1
contract/binding/test, and a genuine nonzero compactly time-supported
small-force instance.  The claimed constants are

```text
c          = criticalSmallnessH1
C₀         = criticalTrilinearConst
C₁         = h1TrilinearConst
CH1        = 2
Ccriterion = hTwoConst ^ 2 * CH1
```

The report also explains that the requested unsuffixed module names were
already occupied by the frozen whole-space contract.  This is correct:
`R43.critical_regularity` uses `Contracts.V1.CriticalRegularity`,
`Bindings.CriticalRegularity`, `Tests.CriticalRegularity`, and
`checkedCriticalRegularity` at `verification/contracts.json:324`, while the new
torus registration is `T03.critical_regularity` at
`verification/contracts.json:478`.  The additive `CriticalRegularityT` suffix
preserves V1 base compatibility and is not a defect.

## 2. What is in Lean

### Statement fidelity

The mathematical statement matches Proposition `prop:critical`.  The paper
selects one universal positive `c`, assumes
`g ∈ F` and `ρ < cν`, and concludes infinite maximal lifespan at zero
initial datum (`paper/sections/03-torus.tex:383`).  Its proof displays the mean
reduction and mean bound (`paper/sections/03-torus.tex:395`), untranslated
mean-free equation and both constant-transport properties
(`paper/sections/03-torus.tex:407`), critical energy and force integral
(`paper/sections/03-torus.tex:413`), bootstrap bound
(`paper/sections/03-torus.tex:446`), `H¹` energy estimate
(`paper/sections/03-torus.tex:467`), and continuation estimate
(`paper/sections/03-torus.tex:490`).  These are exactly the eleven mathematical
fields of the structure at
`verification/Contracts/V1/CriticalRegularityT.lean:215` through
`verification/Contracts/V1/CriticalRegularityT.lean:374`.

A byte comparison of the complete T20 definition/record block reported:

```text
Spec_vs_canonical_T20_block: True
Spec_vs_contract_T20_block: True
Block_bytes: 16567
```

Thus the definitions and record are token-for-token identical to the
reconciled source beginning at `research/T20/Spec.lean:905`; the structure
starts at `research/T20/Spec.lean:1015` and ends with the exact global theorem
field at `research/T20/Spec.lean:1241`.  The contract separately adds the
brief-required existential statement at
`verification/Contracts/V1/CriticalRegularityT.lean:377`.

The record has exactly twelve constant/certification fields followed by eleven
mathematical fields (`verification/Contracts/V1/CriticalRegularityT.lean:145`).
The implementation fills all 23 directly at
`formalization/NSFormalization/Section3/T20/Assembly.lean:27`:

- `c`, `C₀`, `C₁`, `CH1`, and `Ccriterion` are the claimed closed terms;
  `CH1` is definitionally `2` at
  `formalization/NSFormalization/Section3/T20/H1Energy.lean:357`,
  `criticalSmallnessH1` is the two-constant shrink at
  `formalization/NSFormalization/Section3/T20/H1Energy.lean:368`, and
  `Ccriterion` is defined at
  `formalization/NSFormalization/Section3/T20/Continuation.lean:388`.
- The two strict shrinkings are supplied by the named theorems at
  `formalization/NSFormalization/Section3/T20/H1Energy.lean:382` and
  `formalization/NSFormalization/Section3/T20/H1Energy.lean:389`.
- The eleven mathematical entries at
  `formalization/NSFormalization/Section3/T20/Assembly.lean:40` point to the
  landed declarations: `MeanReduction.lean:15,117,175`,
  `ConstantTransport.lean:58`, `TransportLambda.lean:52`,
  `CriticalEnergy.lean:518`, `BIntegral.lean:143`, `YBound.lean:370`,
  `H1Energy.lean:404`, `Continuation.lean:683`, and
  `GlobalRegularity.lean:114`, all under
  `formalization/NSFormalization/Section3/T20/`.
- `yBound` is honestly specialized via
  `yBound_of_le criticalSmallnessH1_le_half`, exactly as required
  (`formalization/NSFormalization/Section3/T20/Assembly.lean:47`).

The report's theorem claims exist with the stated types:

- `criticalRegularityT : CriticalRegularityTAPI` is at
  `formalization/NSFormalization/Section3/T20/Assembly.lean:27`.
- `criticalRegularityStatement_holds : criticalRegularityStatement` is at
  `formalization/NSFormalization/Section3/T20/Assembly.lean:53`.
- The non-vacuity theorem has the claimed nonzero-force, strict-smallness, and
  infinite-lifespan conclusion at
  `formalization/NSFormalization/Section3/T20/Assembly.lean:136`.
- The registered record and proposition theorem are at
  `verification/Bindings/CriticalRegularityT.lean:101` and
  `verification/Bindings/CriticalRegularityT.lean:151`; the registered
  non-vacuity theorem is at `verification/Bindings/CriticalRegularityT.lean:156`.
- The public checked declaration and the three requested conformance examples
  are at `verification/Tests/CriticalRegularityT.lean:22`,
  `verification/Tests/CriticalRegularityT.lean:27`,
  `verification/Tests/CriticalRegularityT.lean:34`, and
  `verification/Tests/CriticalRegularityT.lean:42`.

All seventeen T20-specific restated definitions have explicit `rfl` drift
guards (`verification/Bindings/CriticalRegularityT.lean:30` through
`verification/Bindings/CriticalRegularityT.lean:96`).  Fields involving the
separately restated `ClassicalSolutionT` use the fieldwise `ofContract`
conversion (`verification/Bindings/CriticalRegularityT.lean:115`), and the
global conclusion uses `maximalLifespanT_eq`
(`verification/Bindings/CriticalRegularityT.lean:145`).  The underlying
conversion and lifespan bridge are the established declarations at
`verification/Bindings/TorusLocalTheory.lean:217` and
`verification/Bindings/TorusLocalTheory.lean:270`.

### Non-vacuity and honest hypotheses

There is no `⊤.toReal = 0` shortcut.  The force is a nonzero spatially constant
bump supported strictly in positive time
(`formalization/NSFormalization/Section3/T20/Assembly.lean:58`), membership in
`forceClassT` is proved at line 69, and nonzeroness at `(2,0)` at line 82.  A
concrete half-order datum path proves `criticalRho g ≠ ⊤` at line 94.  Only
then does the proof use `ENNReal.ofReal_toReal` at line 154 to choose a positive
viscosity and establish strict smallness.  This is a substantive nonzero
instance, also checked in registered vocabulary at
`verification/Tests/CriticalRegularityT.lean:53`.

The positivity fields at
`verification/Contracts/V1/CriticalRegularityT.lean:151` through line 213 rule
out zero constants and empty smallness balls.  Time-domain fields quantify over
an actual `ClassicalSolutionT`, whose `horizon_pos : 0 < T` is part of the
structure (`verification/Contracts/V1/TorusLocalTheory.lean:151`), so the
`Ico`/`Ioo` clauses are not silently made vacuous by a nonpositive horizon.
There is no named proposition input or residual assumption in the assembly.

The positive review probe
`research/T20/probes/rev451_exact_and_nonvacuous.lean:12` checks the exact record
type, proposition, and five constants, while its full nonzero instance starts
at line 29.  It elaborates with zero output.

## 3. Gaps

No mathematical, statement, registration, axiom, hygiene, or build gap was
found.  In particular, the worker report makes no missing-lemma or "not in the
tree" claim, so the requested whole-`Section4` missing-lemma grep has no gap to
validate.  A corroborating search for `CriticalRegularityTAPI`,
`criticalRegularityStatement`, and `criticalRegularityT` under
`formalization/NSFormalization/Section4` returned no matches; this does not
affect the lane because the implementation is correctly in `Section3/T20`.

The substantive negative mutation widens the force ball from `c·ν` to
`2c·ν` in
`research/T20/probes/rev451_widen_smallness_mutation.lean:12`.  It fails at the
attempted application of the canonical theorem, rather than by dropping an
argument:

```text
../research/T20/probes/rev451_widen_smallness_mutation.lean:17:55: error: Application type mismatch: The argument
  hsmall
has type
  criticalRho g < ENNReal.ofReal (2 * criticalRegularityT.c * ν)
but is expected to have type
  criticalRho g < ENNReal.ofReal (criticalRegularityT.c * ν)
in the application
  criticalRegularityT.globalRegularity ν hν g hg hsmall
```

No fix is required.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

1. Build:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.Assembly Contracts.V1.CriticalRegularityT Bindings.CriticalRegularityT Tests.CriticalRegularityT
EXIT_CODE=0
✔ [10674/10675] Built Bindings.CriticalRegularityT (3.8s)
ℹ [10675/10675] Built Tests.CriticalRegularityT (2.4s)
info: Tests/CriticalRegularityT.lean:25:0: Contract BlowupDensity.Tests.checkedCriticalRegularityT: checked; standard logical axioms only
Build completed successfully (10675 jobs).
```

The omitted preceding build chatter consisted only of replayed warnings/info
from pre-existing `NSFormalization.Source`, `NSFormalization.Paper1`,
`NSFormalization.Paper3`, and `vendor/HeliCorgi` modules.  There was no warning
from a lane module.

2. Direct module elaboration:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T20/Assembly.lean
EXIT_CODE=0
OUTPUT_BYTES=0
```

3. Axiom audit:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T20/axioms_u13.lean
EXIT_CODE=0
'NSFormalization.Section3.T20.criticalRegularityT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalRegularityStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalNonvacuityForce_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalNonvacuityForce_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalNonvacuityRho_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalRegularityT_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.CriticalRegularityT.criticalRegularityT' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.CriticalRegularityT.criticalRegularityStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.CriticalRegularityT.criticalRegularity_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularityT' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Positive and negative review probes:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T20/probes/rev451_exact_and_nonvacuous.lean
EXIT_CODE=0
OUTPUT_BYTES=0

$ LEAN_NUM_THREADS=6 lake env lean ../research/T20/probes/rev451_widen_smallness_mutation.lean
EXIT_CODE=1
../research/T20/probes/rev451_widen_smallness_mutation.lean:17:55: error: Application type mismatch: The argument
  hsmall
has type
  criticalRho g < ENNReal.ofReal (2 * criticalRegularityT.c * ν)
but is expected to have type
  criticalRho g < ENNReal.ofReal (criticalRegularityT.c * ν)
in the application
  criticalRegularityT.globalRegularity ν hν g hg hsmall
```

5. Repository checks:

```text
$ make check
EXIT_CODE=0
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The architecture checker in that command reported
`"registered_contracts": 47` and `"base_compatibility_checked": false` (the
expected no-base invocation).  `check_formalization_plan.py --check` reported
45 tasks, no missing copied imports, and only the known copied-source
`Paper1/BoundaryCorollary.lean:90` token; it exited successfully.

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T20.Assembly Contracts.V1.CriticalRegularityT Bindings.CriticalRegularityT Tests.CriticalRegularityT
EXIT_CODE=0
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

The gate's `make test` section included the exact lane line:

```text
info: Tests/CriticalRegularityT.lean:25:0: Contract BlowupDensity.Tests.checkedCriticalRegularityT: checked; standard logical axioms only
```

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
EXIT_CODE=0
  "registered_contracts": 47,
  "base_compatibility_checked": true,
```

The base has 46 registrations and the lane has 47.

6. Hygiene and diff checks:

```text
$ rg -n '<forbidden-token/maxHeartbeats pattern>' <all new lane and review Lean files>
EXIT_CODE=1
<no output>

$ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'
EXIT_CODE=0
<no output>

$ git diff --check origin/erenup/integration-section3...HEAD
EXIT_CODE=0
<no output>

$ git diff --stat verification/contracts.json
EXIT_CODE=0
<no output: the worker commit is clean>

$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

The base diff contains only the allowed new Lean modules plus registry,
work-item, task-card, and T20 research records.  No existing `.lean` module was
modified.
