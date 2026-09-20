ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed commit `fc21ef3` on `erenup/293-T01-torus-data-contract` against
`origin/erenup/integration-section3`.  The worker claims registration of the
periodic data vocabulary through `IsPeriodicReweight`, plus `IsPeriodicOn`, and
the first ten fields of the canonical T10 probe (`research/T10/REPORT_293.md:5-29`).
It explicitly defers the solution-class layer (`research/T10/REPORT_293.md:60-64`)
and explicitly discloses that the binding uses five canonical theorems plus five
private proof copies because three canonical proof modules cannot coexist
(`research/T10/REPORT_293.md:66-82`).

Those scope claims agree with the contract module docstring
(`verification/Contracts/V1/TorusData.lean:7-24`) and the registry entry
(`verification/contracts.json:412-420`).  The entry is unique, has version 1,
parent `T01`, the correct modules/declaration, names all ten fields, and honestly
records both the deferral and the temporary private reproofs.

The mathematical sources support the selected vocabulary:

- The manuscript fixes the torus Sobolev weight, Fourier coefficient convention,
  vector norm, and homogeneous zero-mode convention at
  `paper/sections/01-introduction.tex:80-109`.
- It gives conjugate-reflection reality and the periodic Leray symbol, including
  identity at zero, at `paper/sections/02-preliminaries.tex:70-80`.
- It identifies all Section 3 spatial norms as torus norms at
  `paper/sections/03-torus.tex:1-4`, and its mean-removal calculation is exactly
  the constant/mean-zero split at `paper/sections/03-torus.tex:395-411`.
- The public physical carrier really is `Space -> Space` at
  `verification/Contracts/V1/Data.lean:95-104`; the upstream `Space` and
  `coordinateVector` are the three-dimensional Euclidean objects cited by that
  contract.

## 2. What is in Lean

### Statements and implementation

The API is byte-identical to the requested first ten probe fields: a direct
`diff` of `research/T10/probes/api_on_canonical.lean:34-162` against
`verification/Contracts/V1/TorusData.lean:239-367` produced no output.  In
particular, binder order, amendment-1 hypotheses, implications, norms, and
conclusions are unchanged.

Every claimed canonical declaration exists with the same type:

| Contract field | Contract | Canonical theorem |
|---|---:|---:|
| `datum_unique` | `verification/Contracts/V1/TorusData.lean:248` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:134` |
| `datum_real` | `verification/Contracts/V1/TorusData.lean:261` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:146` |
| `parseval_forward` | `verification/Contracts/V1/TorusData.lean:275` | `formalization/NSFormalization/Section3/T10/Parseval.lean:120` |
| `parseval_backward` | `verification/Contracts/V1/TorusData.lean:287` | `formalization/NSFormalization/Section3/T10/Parseval.lean:64` |
| `torusLift_injective` | `verification/Contracts/V1/TorusData.lean:300` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:65` |
| `torusLift_surjective` | `verification/Contracts/V1/TorusData.lean:312` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:74` |
| `mean_decomposition` | `verification/Contracts/V1/TorusData.lean:324` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:95` |
| `meanZero_datum` | `verification/Contracts/V1/TorusData.lean:339` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:155` |
| `leray_exists_contraction` | `verification/Contracts/V1/TorusData.lean:353` | `formalization/NSFormalization/Section3/T10/Leray.lean:178` |
| `leray_projector` | `verification/Contracts/V1/TorusData.lean:365` | `formalization/NSFormalization/Section3/T10/Leray.lean:260` |

The amended integrability conjuncts occur in both datum predicates at
`verification/Contracts/V1/TorusData.lean:125-129` and
`verification/Contracts/V1/TorusData.lean:189-194`; the separate physical
`MemLp 2` premise is in forward Parseval at
`verification/Contracts/V1/TorusData.lean:275-278`.  These exactly implement
the three amendments stated at `research/T10/RECONCILIATION.md:46-55` and avoid
the junk-value counterexamples at `research/T10/RECONCILIATION.md:30-44`.

The contract contains thirty declarations at
`verification/Contracts/V1/TorusData.lean:40-231`, and the binding contains
thirty corresponding definitional drift guards at
`verification/Bindings/TorusData.lean:41-153`.  All elaborate by `rfl`, except
the requested `PeriodicSobolev` bridge through `realPeriodicSubmodule`, whose
proof is exactly that equality (`verification/Bindings/TorusData.lean:79-85`).
Thus the five expanded TorusCube declarations and every copied T10 body are
definitionally the canonical objects.  Contract imports are only
`Contracts.V1.Data` and Mathlib (`verification/Contracts/V1/TorusData.lean:1-2`).

The final value uses the five import-compatible canonical facts and the five
private copies exactly as disclosed (`verification/Bindings/TorusData.lean:334-345`).
All four pre-existing conformance probes typecheck with zero output, so each
original theorem statement independently remains available even though the
modules cannot yet be imported together.

### Non-vacuity and hypothesis audit

There is no `.toReal` totalization in the contract, no interval endpoint to
empty, and the empty datum infima deliberately return `top`
(`verification/Contracts/V1/TorusData.lean:131-135` and
`verification/Contracts/V1/TorusData.lean:196-199`).  The review's zero-field
probe constructs an actual amended order-zero datum, proves the physical
`MemLp 2` premise, and invokes both Parseval directions
(`research/T01/probes/rev293_nonvacuity.lean:14-27`).  It elaborates silently.

Two hypotheses are logically redundant but neither is dishonest or vacuity-
inducing.  `datum_real` does not need its `IsPeriodicDatum` premise because
`PeriodicSobolev` is already the conjugate-reflection submodule; the canonical
proof ignores that premise (`formalization/NSFormalization/Section3/T10/DatumBasics.lean:146-151`).
`mean_decomposition` does not use periodicity once integrability of the lift is
given (`formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:95-110`).
Both hypotheses are verbatim from the lead-approved probe and accurately mark
the physical domain; they do not make the premise empty.

### Negative check

`research/T01/probes/rev293_parseval_constant_mutation.lean:14-21` retains every
binder and hypothesis and substantively changes the forward Parseval conclusion
from `norm = eLpNorm` to `norm = 2 * eLpNorm`.  The original proof fails with the
expected changed-constant type mismatch; exact output is in Part 4.

## 3. Gaps and required notes

1. **Low, one-line build-hygiene fix.**  Direct checking of the contract is
   silent, but direct checking of the binding emits a lane-owned `defProp`
   warning at `verification/Bindings/TorusData.lean:333-334`.  Because the brief
   explicitly requested `def torusData`, insert
   `set_option linter.defProp false in` immediately before the declaration (or,
   if the lead releases the `def` spelling, change `def` to `theorem`).

2. **Low, one-line axiom-audit fix.**  Eleven of twelve `#print axioms` commands
   print exactly `[propext, Classical.choice, Quot.sound]`.  The pure type-alias
   bridge `periodicFrequency_eq` correctly has *no* axioms, so
   `research/T10/axioms_contract.lean:17` violates the review requirement that
   every printed declaration have exactly the three-item list.  Delete that one
   `#print` line.  The substantive `torusData` and `checkedTorusData` declarations
   already print exactly the required list (`research/T10/axioms_contract.lean:27-28`).

3. **Low, one-line documentation fix.**  The sentence at
   `verification/Bindings/TorusData.lean:333` says all ten canonical theorems are
   transported only by definitional equality, but lines 337-341 are five private
   proof copies.  Replace it with: “The ten T10 fields, using five canonical
   declarations and five collision-safe private proof copies over definitionally
   equal vocabulary.”  The longer module docstring and registry are already
   honest (`verification/Bindings/TorusData.lean:14-21`,
   `verification/contracts.json:419`).

4. **Record-output correction.**  The worker's build excerpt omits the lane-owned
   warning, and its axiom excerpt omits the first ten `#print` results
   (`research/T10/REPORT_293.md:93-108`).  Label those blocks “selected output”
   or replace them with the exact replay below.  The report's mathematical axiom
   claim about `checkedTorusData` is nevertheless true.

5. **Declared architectural follow-up, not a theorem gap.**  The report does not
   claim a missing Section 4 lemma.  Its only implementation gap is the anonymous
   instance collision, independently reproduced by
   `research/T01/probes/rev293_import_collision.lean:1-5`.  The colliding local
   declarations are visible at `formalization/NSFormalization/Section3/T10/DatumBasics.lean:21-24`,
   `formalization/NSFormalization/Section3/T10/Parseval.lean:21-23`, and
   `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:22-24`.
   A separately authorized maintenance lane should name the shared instances
   once and replace the private copies with all ten named theorem references.
   Until then, the registered statements remain proved with no extra axioms.

The requested whole-tree check

```text
rg -n "IsPeriodicSobolevPath|forceSobolevENormT|initialClassT|MemForceT|forceClassT|PressureGaugeT|ClassicalSolutionT|maximalLifespanT|breakdownSetT|RelativelyDenseT|energyENormT|parseval_forward|parseval_backward|torusLift_injective|torusLift_surjective|mean_decomposition" formalization/NSFormalization/Section4
```

produced no output.  This does **not** establish a missing-lemma claim: the report
only says the solution-class declarations are absent from this contract, and
their T10 definitions in fact continue after the selected data layer in
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:212-429`.  Their
deferral is exactly the lane scope.

Hygiene otherwise passes: no `sorry`, `admit`, `axiom` declaration, or
`native_decide`; no `maxHeartbeats`; no modified pre-existing module under
`formalization/`, `verification/Contracts/`, or `verification/Tests/`.  The only
contract/test entries are new files.  There are no REJECT-level statement,
proof, axiom, or gate failures.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, ran from `verification/`, and were sequential.  The full
`make check`/contract-closure JSON is hundreds of kilobytes, so exact decisive
tails and lane-owned diagnostics are pasted rather than duplicating the closure
inventory.

### Build and direct module checks

```text
$ cd verification
$ . ../scripts/lean-env.sh
$ LEAN_NUM_THREADS=6 lake build Contracts.V1.TorusData Bindings.TorusData Tests.TorusData
...
warning: Bindings/TorusData.lean:333:0: Definition `torusData` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
Build completed successfully (9363 jobs).
[exit 0]
```

The omitted build lines are replayed diagnostics from inherited dependencies;
the displayed warning is the only diagnostic owned by this lane.

```text
$ LEAN_NUM_THREADS=6 lake env lean Contracts/V1/TorusData.lean
[exit 0; exactly 0 output]

$ LEAN_NUM_THREADS=6 lake env lean Bindings/TorusData.lean
Bindings/TorusData.lean:333:0: warning: Definition `torusData` is a proposition; use `theorem` instead of `def`

Note: This linter can be disabled with `set_option linter.defProp false`
[exit 0]
```

The four original field probes all exited 0 with exactly zero output:

```text
datum_basics_closes.lean: exit 0, output ""
leray_closes.lean: exit 0, output ""
parseval_closes.lean: exit 0, output ""
physical_bridge_closes.lean: exit 0, output ""
```

### Axioms

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_contract.lean
'BlowupDensity.Bindings.periodicFrequency_eq' does not depend on any axioms
'BlowupDensity.Bindings.periodicTorus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicTorusMeasure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.torusLift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicFourierCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.realPeriodicSubmodule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicSobolev_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicHomogeneousDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicReweight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.torusData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedTorusData' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

### Repository gates

`make check` exited 0.  Its exact terminal checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Independent `make test` exited 0 and included:

```text
warning: Bindings/TorusData.lean:333:0: Definition `torusData` is a proposition; use `theorem` instead of `def`
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
```

Independent `make test-mutations` exited 0 with this exact tail:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

The full gate invocation exited 0.  Its exact final sections were:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh Contracts.V1.TorusData Bindings.TorusData Tests.TorusData
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
[exit 0]
```

The explicit compatibility check exited 0; its decisive exact lines were:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
  "registered_contracts": 38,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
[exit 0]
```

### Hygiene and scope

```text
$ rg -n "^[[:space:]]*(sorry|admit|axiom)\\b|\\bnative_decide\\b" <lane Lean files>
[exit 0; 0 output]
$ rg -n "set_option maxHeartbeats" <lane Lean files>
[exit 0; 0 output]
$ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- formalization verification/Contracts verification/Tests
[exit 0; 0 output]
$ git diff --name-status origin/erenup/integration-section3...HEAD -- formalization verification/Contracts verification/Tests
A verification/Contracts/V1/TorusData.lean
A verification/Tests/TorusData.lean
```

```text
$ git diff --stat origin/erenup/integration-section3...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

### Reviewer probes

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T01/probes/rev293_nonvacuity.lean
[exit 0; exactly 0 output]
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T01/probes/rev293_parseval_constant_mutation.lean
../research/T01/probes/rev293_parseval_constant_mutation.lean:21:2: error: Type mismatch
  torusData.parseval_forward z A hA hz
has type
  ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = 2 * eLpNorm (torusLift z) 2 periodicTorusMeasure
[exit 1, expected]
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T01/probes/rev293_import_collision.lean
../research/T01/probes/rev293_import_collision.lean:1:0: error: import NSFormalization.Section3.T10.Parseval failed, environment already contains 'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1' from NSFormalization.Section3.T10.DatumBasics
[exit 1, expected]
```

Required fixes before treating the lane as warning-clean: insert the one-line
`linter.defProp` scope, remove the zero-axiom `#print`, correct the inaccurate
one-line binding docstring, and label/correct the abbreviated worker-report
outputs.  The separately authorized instance-deduplication follow-up should then
restore direct assembly from all ten canonical theorem names.
