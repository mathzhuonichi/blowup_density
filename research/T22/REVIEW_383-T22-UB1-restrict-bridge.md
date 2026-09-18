ACCEPT-WITH-NOTES

Exact fixes before merge:

1. Delete `#print axioms restrictDatum_eq_restrictField` at `formalization/NSFormalization/Section3/T22/RestrictBridge.lean:57`.
2. Delete `#print axioms domainSobolevENorm_le_sobolevENorm` at `formalization/NSFormalization/Section3/T22/RestrictBridge.lean:58`.

Those commands belong only in `research/T22/axioms_ub1.lean`; their presence in the
production module is the sole reason the required direct module check is not zero-output.
No mathematical or axiom-set defect was found.

## 1. What the lane claims

The report claims the restriction identity and the quotient-norm left inequality
(`research/T22/REPORT_383.md:5`, `research/T22/REPORT_383.md:8`), exact canonical
vocabulary and structure conformance (`research/T22/REPORT_383.md:17`), a concrete
nonzero bump (`research/T22/REPORT_383.md:23`), and the standard three-axiom set
(`research/T22/REPORT_383.md:25`). All substantive claims are correct.

The mathematics matches the cited paper. The paper defines the domain norm as the
infimum over whole-space extensions at `paper/sections/03-torus.tex:601-605`, allows
all real orders at `paper/sections/03-torus.tex:606`, defines zero extension and states
the left inequality at `paper/sections/03-torus.tex:608-615`, and says explicitly that
the first inequality follows from the definition at `paper/sections/03-torus.tex:624-625`.

The reconciled Spec spells the test carrier and functional at
`research/T22/Spec.lean:48` and `research/T22/Spec.lean:56`, the restriction and
infimum at `research/T22/Spec.lean:62` and `research/T22/Spec.lean:72`, the physical
restriction and zero extension at `research/T22/Spec.lean:81` and
`research/T22/Spec.lean:89`, the cutoff graph at `research/T22/Spec.lean:99`, and the
three API fields at `research/T22/Spec.lean:114-167`.

## 2. What is in Lean

The canonical module has the same declarations at
`formalization/NSFormalization/Section3/T22/Domain.lean:25-77`. The conformance probe
proves every helper definition equal by `rfl` at
`research/T22/probes/api_on_canonical.lean:62-68`, and converts the structure in both
directions, field by field, with round trips at
`research/T22/probes/api_on_canonical.lean:70-90`. Thus the differing namespaces and
canonical D01 imports do not conceal statement drift.

The two claimed theorems exist with the requested statements at
`formalization/NSFormalization/Section3/T22/RestrictBridge.lean:25-28` and
`formalization/NSFormalization/Section3/T22/RestrictBridge.lean:48-51`. The bridge uses
the honest D01 predicate: `IsSobolevDatum` says exactly that every component pairs with
every Schwartz test as the physical integral
(`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:237-239`). The proof then
uses the `DomainTest` support condition to vanish outside the domain
(`formalization/NSFormalization/Section3/T22/RestrictBridge.lean:29-44`). It adds no
measurability, openness, nonemptiness, finiteness, or other hidden hypothesis.

The norm proof quantifies over every whole-space datum of the zero extension and maps
it to an admissible domain datum
(`formalization/NSFormalization/Section3/T22/RestrictBridge.lean:52-55`). There is no
`toReal`, no interval, no unused binder, and no named input. Although the universal
inequality is allowed to have right side `top`, the reviewer probe supplies a nonzero
compact bump (`research/T22/probes/rev383_nonvacuity.lean:16-44`) and proves that both
sides of the instantiated inequality are not `top`
(`research/T22/probes/rev383_nonvacuity.lean:46-73`).

Only new Lean modules/probes were added relative to the merge base; no existing Lean
module was modified. The exact name-status output was:

```text
A formalization/NSFormalization/Section3/T22/Domain.lean
A formalization/NSFormalization/Section3/T22/RestrictBridge.lean
A research/T22/axioms_ub1.lean
A research/T22/probes/api_on_canonical.lean
A research/T22/probes/restrict_bridge_closes.lean
```

The forbidden-declaration/heartbeat scan produced no output. The only hygiene defect
is the two production-module `#print` commands noted in the verdict: they do not add
axioms, but they break the explicit zero-output gate.

## 3. Gaps

U-B1 has no mathematical gap. The report's downstream gaps are accurately scoped at
`research/T22/REPORT_383.md:30-33`: the right comparison still needs the cutoff
multiplier, zero-extension regularity, and cutoff-datum identity, while `orderZero`
needs its separate analytic units. In particular, D01 explicitly says that the
order-zero norm identity is not proved there
(`formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean:40-53`).

As required for “not in the tree” claims, this whole-Section4 search returned no
matches:

```text
$ rg -n -i 'cutoffMultiplier|isCutoffDatum_realizes_zeroExtension|contDiff_zeroExtension|hasCompactSupport_zeroExtension|zeroExtensionComparison|orderZeroDatum_norm|orderZero.*eLpNorm' formalization/NSFormalization/Section4
<no output>
```

The concrete worker probe proves a bump is nonzero but does not itself prove norm
finiteness (`research/T22/probes/restrict_bridge_closes.lean:43-57`). The reviewer
therefore added `research/T22/probes/rev383_nonvacuity.lean`; it proves the zero
extension equals the bump and both displayed norms are finite. This is review evidence,
not a requested worker fix.

## 4. Commands and results

Environment for Lean commands: `. scripts/lean-env.sh`; all `lake` commands ran from
`verification/` with `LEAN_NUM_THREADS=6` for the build.

### Build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.RestrictBridge
[cached upstream replay warnings omitted here: 76 lines, no errors]
ℹ [9874/9874] Replayed NSFormalization.Section3.T22.RestrictBridge
info: NSFormalization/Section3/T22/RestrictBridge.lean:57:0: 'NSFormalization.Section3.T22.restrictDatum_eq_restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NSFormalization/Section3/T22/RestrictBridge.lean:58:0: 'NSFormalization.Section3.T22.domainSobolevENorm_le_sobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (9874 jobs).
```

Exit 0. The warnings are replayed upstream warnings; the two displayed lane-owned info
lines are precisely the zero-output note.

### Direct module and probe checks

```text
$ lake env lean ../formalization/NSFormalization/Section3/T22/Domain.lean
<no output>
```

Exit 0.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T22/RestrictBridge.lean
'NSFormalization.Section3.T22.restrictDatum_eq_restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.domainSobolevENorm_le_sobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit 0, but not zero-output. The two exact deletions at the top of this report fix it.

```text
$ lake env lean ../research/T22/probes/api_on_canonical.lean
'BlowupDensity.T22.Probe.DomainTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.DomainFunctional' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.restrictDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.domainSobolevENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.IsCutoffDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.BoundedDomainNormAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.BoundedDomainNormAPI.toCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.T22.Probe.BoundedDomainNormAPI.ofCanonical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.

```text
$ lake env lean ../research/T22/probes/restrict_bridge_closes.lean
'NSFormalization.Section3.T22.Probe.bridgeBump' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.Probe.bridgeField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.Probe.bridgeField_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.Probe.bridgeField_hasCompactSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.Probe.bridgeField_tsupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.Probe.bridgeField_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.Probe.concrete_left_conjunct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.

### Axiom audit

```text
$ lake env lean ../research/T22/axioms_ub1.lean
'NSFormalization.Section3.T22.DomainTest' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.DomainFunctional' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.restrictDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.domainSobolevENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.zeroExtension' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.IsCutoffDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.BoundedDomainNormAPI' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.restrictDatum_eq_restrictField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.domainSobolevENorm_le_sobolevENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exit 0. Every declaration has exactly the permitted three axioms.

### Negative mutation and non-vacuity

The negative probe flips the main inequality at
`research/T22/probes/rev383_negative.lean:15-18`; it does not drop an argument.

```text
$ lake env lean ../research/T22/probes/rev383_negative.lean
../research/T22/probes/rev383_negative.lean:18:2: error: Type mismatch
  domainSobolevENorm_le_sobolevENorm
has type
  domainSobolevENorm ?m.4 ?m.5 (restrictField ?m.4 ?m.6) ≤ sobolevENorm ?m.5 (zeroExtension ?m.4 ?m.6)
but is expected to have type
  sobolevENorm s (zeroExtension Ω z) ≤ domainSobolevENorm Ω s (restrictField Ω z)
```

Exit 1, the expected direction mismatch.

```text
$ lake env lean ../research/T22/probes/rev383_nonvacuity.lean
<no output>
```

Exit 0. The probe proves a nonzero field and that neither side is `top`.

### Repository gates and hygiene

```text
$ set -o pipefail; make check 2>&1 | tail -n 14
      "Tests.LocalPotential"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.286s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Exit 0.

```text
$ rg -n '(^|[[:space:]])(sorry|admit|axiom|native_decide)\b|set_option[[:space:]]+maxHeartbeats' formalization/NSFormalization/Section3/T22 research/T22/probes research/T22/axioms_ub1.lean
<no output>
```

Exit 1 from `rg` (no matches), as required.

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD -- verification
<no output>
```

Thus the conditional `scripts/gates.sh` / base-compatibility gate for a
`verification/` change does not apply. For completeness I ran it anyway. Its build,
test, and mutation phases passed, but the final base check stopped because this lane
predates a stable contract now present on the moving integration ref:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
Traceback (most recent call last):
  File "/data_8T/ping/blowup_density/.claude/worktrees/383-T22-UB1-restrict-bridge/experiments/check_contracts.py", line 153, in <module>
    print(json.dumps(check(base=args.base_ref), indent=2))
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/data_8T/ping/blowup_density/.claude/worktrees/383-T22-UB1-restrict-bridge/experiments/check_contracts.py", line 143, in check
    check_compatibility(root, base, contracts)
  File "/data_8T/ping/blowup_density/.claude/worktrees/383-T22-UB1-restrict-bridge/experiments/check_contracts.py", line 62, in check_compatibility
    assert (root / path).is_file(), f'Removed stable specification: {path}'
           ^^^^^^^^^^^^^^^^^^^^^^^
AssertionError: Removed stable specification: verification/Contracts/V1/Localization.lean
```

This is not caused by the lane: the three-dot diff above proves the lane touched no
`verification/` path. It is therefore not a blocking lane finding.

ACCEPT-WITH-NOTES — delete only `RestrictBridge.lean:57` and
`RestrictBridge.lean:58`; no mathematical fix is required.
