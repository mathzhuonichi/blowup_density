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

## A3: inferred infimum witness timed out
```text
NormBridge.lean:25:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```
Resolved without raising heartbeats: give the intermediate norm inequality and
infimum binder explicit types. The preceding checkpoint contained this failure;
the next commit repairs it and the declaration checks with zero output.

## A4: quotient realization spelling
```text
NormBridge.lean:51:93: error: unsolved goals
Ω : Set Space
s r : ℝ
hsr : s ≤ r
z : T22.DomainFunctional Ω
A : Paper3.RealVectorSobolev r
hA : T22.restrictDatum Ω r A = z
i : Fin 3
ψ : T22.DomainTest Ω
⊢ ((Paper3.angularRealization r)
        ↑(↑(ContinuousLinearMap.proj i ∘SL
                ↑(PiLp.continuousLinearEquiv 2 ℝ fun x => ↥(Source.RealSobolev.RealSobolevHilbert r)))
            A))
      ↑ψ =
    T22.restrictDatum Ω r A i ψ
```
The residual is definitional; `rfl` closes it.

## A5: addition-side convention
```text
Rates.lean:58:30: error: Application type mismatch: The argument
  add_le_add_left (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (LT.lt.le hε.left) ?m.249)) ?m.250
has type
  C * ε ^ ?m.249 + ?m.250 ≤ max C 0 * ε ^ ?m.249 + ?m.250
but is expected to have type
  (M + E) * ε ^ (1 / 2) + C * ε ^ (3 / 2) ≤ (M + E) * ε ^ (1 / 2) + energyConst C * ε ^ (3 / 2)
in the application
  ENNReal.ofReal_le_ofReal
    (add_le_add_left (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg (LT.lt.le hε.left) ?m.249)) ?m.250)
```
Resolved with `add_le_add le_rfl`.
