# Lane 296 report — deduplicate T10 measure instances and restore the direct binding

## 1. What changed

The import collision among `PhysicalBridge`, `DatumBasics`, and `Parseval` is
resolved.  `PeriodicData` now owns the single explicitly named
`periodicTorusMeasure_isProbabilityMeasure` instance.  It proves directly
that the explicit three-factor Haar product has mass one, so the duplicated
local circle `MeasureSpace` and probability helpers could be deleted from all
three consumers.  `Leray` needed no edit.  No definition in `PeriodicData`
and no theorem statement in any proof module changed.

`Bindings/TorusData.lean` now imports all four canonical proof modules and
constructs `torusData` directly from these ten public theorems:

1. `datum_unique`
2. `datum_real`
3. `parseval_forward`
4. `parseval_backward`
5. `torusLift_injective`
6. `torusLift_surjective`
7. `mean_decomposition`
8. `meanZero_datum`
9. `leray_exists_contraction`
10. `leray_projector`

All private physical-bridge and Parseval re-proofs from lane 293 are deleted.
Every existing definitional drift guard is byte-identical over its complete
declaration block.  Following the lane-293 review, the proposition-valued
binding is now `theorem torusData`, its docstring describes direct four-module
assembly, and the zero-axiom `#print axioms periodicFrequency_eq` line was
removed.  The registry declaration remains
`BlowupDensity.Tests.checkedTorusData`.

## 2. Files

Modified:

- `formalization/NSFormalization/Section3/T10/PeriodicData.lean`: added the one
  named product-measure probability instance; no definition changed.
- `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean`: deleted its
  two local instance helpers.
- `formalization/NSFormalization/Section3/T10/DatumBasics.lean`: deleted its two
  local instance helpers.
- `formalization/NSFormalization/Section3/T10/Parseval.lean`: deleted its two
  local instance helpers and corrected the instance-source sentence.
- `verification/Bindings/TorusData.lean`: direct imports and direct ten-theorem
  assembly; all private proof copies removed.
- `research/T10/axioms_contract.lean`: removed only the definitional alias's
  zero-axiom print.

Added:

- `research/T10/probes/all_four_import.lean`
- `research/T10/ATTEMPTS_DEDUPE.md`
- `research/T10/REPORT_296.md`

Unchanged: `Leray.lean`, every file under `verification/Contracts/`, every file
under `verification/Tests/`, and `verification/contracts.json`.  The protected
file hashes before and after the work are:

```text
9ce0a3b755b523b1b322bc62ae4597aad73c4d88f4bf8144adcd63ff015a9ce4  verification/Contracts/V1/TorusData.lean
bcbf7dcd0f3635055e733388c47da0e38fa98cf32f65865c189f3bffc3c6b6da  verification/Tests/TorusData.lean
ec7cae7bd19e0d45f61e4b2d436ba8e9005b4f10c711c532d7f7c6061cc2bead  verification/contracts.json
```

## 3. Gaps and exact error text

There is no remaining implementation or contract gap in this lane.  Before
the fix, after compiling the source modules, the combined import failed with:

```text
../research/T10/probes/all_four_import.lean:1:0: error: import NSFormalization.Section3.T10.DatumBasics failed,
environment already contains
'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1'
from NSFormalization.Section3.T10.PhysicalBridge
```

After the fix that probe has exit code 0 and no output.  The only initial
setup diagnostic was a missing `PhysicalBridge.olean` before this worktree's
first module build; rebuilding the requested targets resolved that cache miss
and exposed the collision above.

The solution-class layer remains outside `T01.torus_data`, exactly as reported
by lane 293; this maintenance lane neither extends nor changes that contract.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran through the `verification/` workspace.

Canonical-module build:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData NSFormalization.Section3.T10.PhysicalBridge NSFormalization.Section3.T10.DatumBasics NSFormalization.Section3.T10.Parseval NSFormalization.Section3.T10.Leray
✔ Built NSFormalization.Section3.T10.PeriodicData
✔ Built NSFormalization.Section3.T10.PhysicalBridge
✔ Built NSFormalization.Section3.T10.Parseval
✔ Built NSFormalization.Section3.T10.DatumBasics
✔ Built NSFormalization.Section3.T10.Leray
Build completed successfully (9358 jobs).
[exit 0; 0 errors]
```

Import and field probes:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/all_four_import.lean
[exit 0; output ""]
$ for probe in ../research/T10/probes/*_closes.lean; do
    LEAN_NUM_THREADS=6 lake env lean "$probe" || exit 1
  done
[exit 0; output ""]
```

Binding, test, and axiom audit:

```text
$ LEAN_NUM_THREADS=6 lake env lean Bindings/TorusData.lean
[exit 0; output ""]
$ LEAN_NUM_THREADS=6 lake build Bindings.TorusData Tests.TorusData
✔ Built Bindings.TorusData
ℹ Built Tests.TorusData
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
Build completed successfully (9365 jobs).
[exit 0]
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_contract.lean
'BlowupDensity.Bindings.torusData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedTorusData' depends on axioms: [propext, Classical.choice, Quot.sound]
[the other nine printed bridge declarations have the same three-item list; exit 0]
```

Repository gates:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh
== make check
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
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

Explicit base compatibility:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
{
  "registered_contracts": 38,
  ...
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
[exit 0]
```

Proof-module diffs show only the intended helper deletions and one docstring
correction:

```text
$ git diff -- formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
-local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
-local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
-  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

$ git diff -- formalization/NSFormalization/Section3/T10/DatumBasics.lean
-local instance unitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
-  ⟨AddCircle.haarAddCircle⟩
-local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
-  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

$ git diff -- formalization/NSFormalization/Section3/T10/Parseval.lean
-The local Haar instances are the same ones used in `Paper1.TorusCube`.
+The normalized product Haar instance is declared once in `PeriodicData`.
-local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
-local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
-  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

$ git diff -- formalization/NSFormalization/Section3/T10/Leray.lean
[no output]
```

Final diff statistic (no `Contracts/`, `Tests/`, or `contracts.json` entry):

```text
$ git diff HEAD --stat
 .../NSFormalization/Section3/T10/DatumBasics.lean  |   5 -
 .../NSFormalization/Section3/T10/Parseval.lean     |   6 +-
 .../NSFormalization/Section3/T10/PeriodicData.lean |   8 +
 .../Section3/T10/PhysicalBridge.lean               |   4 -
 research/T10/ATTEMPTS_DEDUPE.md                    |  65 +++++++
 research/T10/REPORT_296.md                         | 207 ++++++++++++++++++++
 research/T10/axioms_contract.lean                  |   1 -
 research/T10/probes/all_four_import.lean           |   4 +
 verification/Bindings/TorusData.lean               | 212 ++-------------------
 9 files changed, 298 insertions(+), 214 deletions(-)
```
