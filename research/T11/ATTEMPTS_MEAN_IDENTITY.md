# U7 mean identity — lane 316

## Paths and outcome

Read CLAUDE.md, T11_SPLIT §0–§4, RECONCILIATION §0–§3,
IMPLEMENTATION_CANDIDATES, and the first 40 LESSONS lines. FourierCalculus is present.
The prescribed grep -rn inventory covered Paper1/Periodic*.lean, Section3,
Section4/{A01,A02,A04,D01}, and vendor/HeliCorgi/Formal (local log
`tmp/mean_inventory.log`). The older candidate survey predates U3.

U3/GalileanClasses already proves the full integrated momentum argument:
private `cubeIntegral_laplacian_component_eq_zero`,
`cubeIntegral_pressure_component_eq_zero`,
`cubeIntegral_advection_component_eq_zero`, `velocityMean_hasDerivAt`,
and `velocityMean_eq_galileanMean`, consumed by public `transformed_mean_zero`.
We use that public theorem, undo Haar translation and constant subtraction,
and obtain the exact mean formula. FTC differentiates its data-defined right
side; equality on Ico gives eventual equality at each interior time.
There is no circular import: MeanIdentity imports GalileanClasses, never conversely.

Because existing modules must remain unchanged, the elementary translation and
smooth-mean adapters are reproduced in namespace `T11.MeanIdentity`, with
attribution in the module. No mangled private identifiers are referenced.
No instance declarations and no heartbeat overrides were introduced.

## Actual failed checks and fixes

1. Inference of the periodic field from `have hp := w.velocity_periodic t ht`:
```
Application type mismatch: The argument
  hp
has type
  ∀ (x : Space) (i : Fin 3), w.velocity (t, x + coordinateVector i) = w.velocity (t, x)
but is expected to have type
  IsPeriodicSpatial ?m.86
```
Fixed by explicitly typing hp as `IsPeriodicSpatial (fun x ↦ w.velocity (t, x))`.

2. Simplification of the FTC derivative under `simpa [galileanMeanT]`:
```
Type mismatch: After simplification, term
  HasDerivAt.const_add (meanT a) ...
has type
  HasDerivAt (fun x => ∫ (x : ℝ) in 0..x, forceMeanT f x) (forceMeanT f t) t
but is expected to have type
  HasDerivAt (galileanMeanT a f) (forceMeanT f t) t
```
Fixed with `exact`, using definitional equality directly.

3. Initial witness probe lacked a built dependency:
```
error: object file '.../NSFormalization/Section3/T11/CriterionBridge.olean' of module NSFormalization.Section3.T11.CriterionBridge does not exist
```
Built CriterionBridge before rerunning the probe.

## Residual input

None. Both target statements are unchanged. The non-vacuity example constructs
a constant nonzero velocity at viscosity 1 on [0,1), with zero pressure and
zero force; all class and solution hypotheses hold simultaneously.
All eight new named declarations have guarded exact dependency lists
`[propext, Classical.choice, Quot.sound]`.
