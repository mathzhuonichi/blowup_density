# Lane 485 attempts

Dependency closure built successfully before proof development (10087 jobs).
The path-infimum / slice-integral distinction is retained; no equality is assumed.

## A1: norm coercion
```text
NormBridge.lean:38:5: error(lean.unknownIdentifier): Unknown identifier `enorm_le_enorm`
```
Use explicit nnnorm / ENNReal coercion instead.

## A2: coercion lemma names
```text
NormBridge.lean:39:55: error(lean.unknownIdentifier): Unknown identifier `nnnorm_le_nnnorm_iff`
NormBridge.lean:39:6: error: Type mismatch: After simplification, term
  Section4.R41.lowerVectorL_norm_le r s hsr A
 has type
  ‖(lowerVectorL r s hsr) A‖ ≤ ‖A‖
but is expected to have type
  ‖(lowerVectorL r s hsr) A‖₊ ≤ ‖A‖₊
```
Resolved with `enorm_le_iff_norm_le.mpr`. A discovery probe also reported:
```text
Unknown identifier `enorm_eq_ofReal`
Unknown constant `ENNReal.lintegral_add_le`
Unknown identifier `MeasureTheory.lintegral_add_le`
```
The triangle proof uses measurable paths and `eLpNorm_add_le` instead.
