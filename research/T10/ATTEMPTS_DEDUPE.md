# T10 torus-measure instance deduplication attempts

Lane 296, 2026-09-17.

## Pre-fix reproduction

The first run of the new four-module import probe happened before this
worktree had built the canonical modules and therefore only reported the
missing `PhysicalBridge.olean`.  After building the four unchanged modules,
the same probe reproduced the actual environment collision:

```text
$ cd verification
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/all_four_import.lean
../research/T10/probes/all_four_import.lean:1:0: error: import NSFormalization.Section3.T10.DatumBasics failed,
environment already contains
'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1'
from NSFormalization.Section3.T10.PhysicalBridge
[exit 1]
```

`PhysicalBridge.lean`, `DatumBasics.lean`, and `Parseval.lean` each installed
a local Haar `MeasureSpace UnitAddCircle` and a local anonymous
`IsProbabilityMeasure (volume : Measure UnitAddCircle)`.  Although the
instance attributes are local, Lean still serializes their declarations, and
the anonymous probability proofs received the same generated declaration
name in the shared `NSFormalization.Section3.T10` namespace.

## Instance choice

An import of `PeriodicData` already synthesizes Mathlib's default
`MeasureSpace UnitAddCircle`, but it does not synthesize
`IsProbabilityMeasure periodicTorusMeasure`.  The proof modules only need the
latter fact.  To stay within the lane's one-declaration allowance for
`PeriodicData.lean`, the final change declares exactly

```lean
instance periodicTorusMeasure_isProbabilityMeasure :
    IsProbabilityMeasure periodicTorusMeasure
```

and proves its `measure_univ` field directly using `Measure.pi_univ` for the
explicit product of `AddCircle.haarAddCircle`.  Thus the six per-module circle
helpers are deleted rather than promoted to additional global instances.
There are no remaining module-specific instance helpers.

## Post-fix checks

The five canonical modules build together.  The combined import probe and all
four field-closing probes elaborate with exactly zero output:

```text
$ cd verification
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/all_four_import.lean
[exit 0; output ""]
$ for probe in ../research/T10/probes/*_closes.lean; do
    LEAN_NUM_THREADS=6 lake env lean "$probe" || exit 1
  done
[exit 0; output ""]
```

With the import collision removed, `Bindings/TorusData.lean` imports all four
modules and its ten API fields elaborate directly from the ten public theorem
names.  No private proof copy, `sorry`, `admit`, `axiom`, or `native_decide`
remains or was introduced.
