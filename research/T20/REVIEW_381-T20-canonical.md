ACCEPT

## What the lane claims

The worker claims that `CriticalRegularity.lean` is a canonical, statement-only
restatement of the T20 proposition: 17 helper definitions, a 23-field
`CriticalRegularityTAPI`, and `criticalRegularityStatement`, with no API witness
or field proof (`research/T20/REPORT_381.md:5-12`).  It also claims a complete
fieldwise structure bridge and `rfl` checks for the helpers
(`research/T20/REPORT_381.md:16-24`), and records the H¹-ball conclusion
(`research/T20/REPORT_381.md:28-36`).

## What is in Lean

The paper's proposition and proof displays are at `paper/sections/03-torus.tex:383-503`:
the zero datum and critical smallness condition are at `:383-390`, mean removal
and the mean-free equation at `:395-411`, the critical estimate and bootstrap at
`:420-458`, the H¹ estimate at `:467-484`, and the continuation calculation at
`:486-503`.  The module's 17 definitions are present at
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:34-122`;
they use canonical T10/T11/T12 names rather than copied definitions.  The
23 fields (12 scalar/positivity/shrinking fields and 11 estimate fields) are
exactly at `.../CriticalRegularity.lean:139-368`, and the existential statement
definition is at `.../CriticalRegularity.lean:372-374`.

The module imports only the canonical Section3 layers
(`.../CriticalRegularity.lean:1-7`).  The T11 continuation structures show the
distinction required by the brief: the manuscript H¹ package and the registered
H³ narrowing are separate at
`formalization/NSFormalization/Section3/T11/Assembly.lean:202-326`, while the
named H¹ predicates and the proved H³ package are at `.../Assembly.lean:328-394`.
No such package is silently inserted as a T20 API parameter; the T20 structure
has the statement-only shape copied from the Spec.

The probe copies the Spec T20 block token-for-token (341 declaration lines; a
direct normalized `diff` was empty), then proves all 17 helper equalities by
`rfl` (`research/T20/probes/api_on_canonical.lean:23-447`).  Its two 23-field
conversions and round trips are at `.../api_on_canonical.lean:449-507`; the
statement seam is proved by the two conversions at `.../api_on_canonical.lean:509-517`.
No API inhabitant is constructed.  The added non-vacuity probe gives a concrete
positive choice of all five scalar constants satisfying both shrinkings
(`research/T20/probes/rev381_nonvacuity.lean:7-12`).

The H¹ grep is complete: exactly `Spec.lean:402` (`restart`) and
`Spec.lean:437` (`restartBeyond`) contain `periodicSobolevENorm 1`
(`research/T20/H1_CHECK.md:3-14`).  The consumer analysis correctly keeps those
manuscript predicates open and routes a future T20 proof through the ball-free
criterion and `higherOrderBound` at order 3 (`research/T20/H1_CHECK.md:18-36`,
`research/T11/H1_GAP.md:81-91`).  A whole-Section4 grep found no declaration of
`PeriodicRestartH1` or `PeriodicRestartBeyondH1`; only explanatory H¹ comments
occur there, so no missing Section4 lemma is being overlooked.  The required
`grep -rnE 'PeriodicRestartH1|PeriodicRestartBeyondH1|restartH1|restartBeyondH1'
formalization/NSFormalization/Section4` returned no output.

## Gaps

No lane-specific statement, canonicalization, hygiene, or build gap was found.
The two H¹ manuscript fields remain explicitly unproved as documented, but they
are outside `CriticalRegularityTAPI` and are not silently replaced by H³
(`research/T20/H1_CHECK.md:13-14,18-36`).  The lane's changed paths contain no
pre-existing Lean module: `git diff --name-only origin/erenup/integration-section3...HEAD`
lists only the new T20 module/probe/records and the intended `COMPARISON.md`
status update.  There are no `maxHeartbeats` declarations and no forbidden
`sorry`, `admit`, `axiom`, or `native_decide` declarations in the lane Lean
code; the `#print axioms` audit file necessarily contains the audit command
itself (`research/T20/axioms_canonical.lean:12-30`).

The substantive negative probe changes the main shrinking from denominator 4 to
5 (`research/T20/probes/rev381_negative_constant.lean:5-9`).  It fails as
expected, not by dropping an argument:

```text
../research/T20/probes/rev381_negative_constant.lean:9:2: error: Type mismatch
  A.c_lt_C₀
has type
  A.c < 1 / (4 * A.C₀)
but is expected to have type
  A.c < 1 / (5 * A.C₀)
```

## Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with `lake` invoked
from `verification/` and `LEAN_NUM_THREADS=6` for the build.

`LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.CriticalRegularity`
returned exit 0 and `Build completed successfully (10591 jobs).`  The command
replayed 382 lines of pre-existing dependency linter output; the target itself
added no warning.  Exact build output head/tail (the middle 362 lines are
unchanged dependency replay) was:

```text
⚠ [8778/9116] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]
...
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [10521/10591] Replayed NSFormalization.Section4.A01.AprioriFamily
warning: NSFormalization/Section4/A01/AprioriFamily.lean:148:31: Variable name `ha` is not explicitly referenced.

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [10522/10591] Replayed NSFormalization.Section4.A01.MildGronwall
warning: NSFormalization/Section4/A01/MildGronwall.lean:150:31: Variable name `ha` is not explicitly referenced.

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (10591 jobs).
```

The direct module check was silent and returned exit 0:

```text
source ../scripts/lean-env.sh && lake env lean ../formalization/NSFormalization/Section3/T20/CriticalRegularity.lean
(no output)
```

`lake env lean ../research/T20/probes/api_on_canonical.lean` returned exit 0;
all 23 audited declarations printed exactly
`[propext, Classical.choice, Quot.sound]`:

```text
'NSFormalization.Section3.T20.criticalRegularityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanPathT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanFreeVelocity_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanFreeForce_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.constantTransportT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.constantTransportSpatialT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanForceIntegralT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalY_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalZ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalB_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalBIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalRho_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.gradientSqT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.laplacianSqT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.lTwoSqT_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanFreeForceLTwoSqIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.meanModeCriterionIntegral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.periodicPairing_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.toModuleAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.ofModuleAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.ofModuleAPI_toModuleAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.toModuleAPI_ofModuleAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'T20Probe.criticalRegularityStatement_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T20/axioms_canonical.lean` returned exit 0; every
module definition, structure, and statement printed the same standard triple
(`research/T20/axioms_canonical.lean:12-30`):

```text
'NSFormalization.Section3.T20.meanPathT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanFreeVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanFreeForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.constantTransportT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.constantTransportSpatialT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanForceIntegralT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalY' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalB' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalBIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalRho' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.gradientSqT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.laplacianSqT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.lTwoSqT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanFreeForceLTwoSqIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.meanModeCriterionIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.periodicPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.CriticalRegularityTAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.criticalRegularityStatement' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The non-vacuity probe returned exit 0 with no output.  The source Spec itself
also elaborated with exit 0.

`make check` returned exit 0 (46,316 lines, 1,910,832 bytes).  Its output
head/tail (the middle closure listing is omitted here) was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 608,
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
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
...
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The final exact lines are:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The architecture check reports the repository's pre-existing copied-source
tokens and `source_hashes_match: false`, but exits successfully; none is in the
new lane module.  `verification/` is absent from the lane diff, so the
conditional `scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates are not applicable.

Verdict: ACCEPT
Fixes: none.
