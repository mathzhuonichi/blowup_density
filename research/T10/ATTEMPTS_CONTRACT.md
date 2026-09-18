# T01.torus_data contract-registration attempts

Lane 293, 2026-09-17.

## Result

The V1 contract restates the T10 vocabulary through `IsPeriodicReweight` plus
`IsPeriodicOn`, and its API contains exactly the first ten proved fields from
`probes/api_on_canonical.lean`.  Every restated declaration has an `rfl` drift
guard.  No solution-class declaration is included.

## Definitional bridges

The contract copy of `torusLift` expands the canonical `toSpace` abbreviation,
as required because `Paper1.TorusCube` is outside the contract allowlist.  The
bridge is nevertheless `rfl`.  `PeriodicSobolev s` is bridged through the
equality of the two `realPeriodicSubmodule` definitions.  Three polymorphic
bridges are pointwise rather than bare function equalities:

- `isPeriodicSpatial_eq`, because `E` and `[Add E]` are implicit;
- `isPeriodicOn_eq`, because `E` is implicit;
- `torusLift_eq`, because its codomain `E` is implicit.

All remaining bridges elaborate as direct `rfl` equalities after their explicit
arguments are fixed.  The phantom `s` must be passed explicitly on the canonical
side of `isSolenoidalPeriodicDatum_eq` and `isPeriodicLerayDatum_eq`, because the
carrier ignores that index definitionally.

## Canonical-module import collision

The initially requested four-way import in `Bindings/TorusData.lean` failed
before any binding declaration was elaborated.  Exact output:

```text
Bindings/TorusData.lean:1:0: error: import NSFormalization.Section3.T10.Parseval failed,
environment already contains
'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1'
from NSFormalization.Section3.T10.DatumBasics
```

Pairwise probes showed:

```text
Parseval PhysicalBridge -> 1
environment already contains
'NSFormalization.Section3.T10.instMeasureSpaceUnitAddCircle_nSFormalization'
from NSFormalization.Section3.T10.Parseval

DatumBasics PhysicalBridge -> 1
environment already contains
'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1'
from NSFormalization.Section3.T10.DatumBasics

DatumBasics Parseval -> 1
environment already contains
'NSFormalization.Section3.T10.instIsProbabilityMeasureUnitAddCircleVolume_nSFormalization._proof_1'
from NSFormalization.Section3.T10.DatumBasics
```

Cause: the three proof modules declare anonymous local `MeasureSpace` and/or
`IsProbabilityMeasure` instances inside the same namespace.  Lean 4.34.0-rc2
assigns colliding generated global declaration names to those local instances.
`DatumBasics + Leray` is compatible.

The ground rules forbid changing any `formalization/` module.  The binding
therefore imports `DatumBasics` and `Leray`, using their five canonical theorems
directly (`datum_unique`, `datum_real`, `meanZero_datum`,
`leray_exists_contraction`, `leray_projector`).  It repeats the already proved
arguments from `Parseval` and `PhysicalBridge` under private binding-local names
for the other five fields.  These are proof copies over definitions connected
by `rfl`, not new assumptions or transports; the checked declaration still has
only the standard logical axioms.

No `sorry`, `admit`, `axiom`, placeholder proposition, or `Formal.*` import was
introduced.
