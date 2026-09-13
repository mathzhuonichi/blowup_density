import Euler.LpCylinderRectangular
import Euler.LpCylinderCoefficients

/-!
# Removing the coefficient product rule's heartbeat override

This standalone copy of `LpCylinderCoefficientTime.lean` uses a separate namespace
and the original imports, so it checks the replacement without importing the
original theorem or modifying the original file. No heartbeat override is needed.

## Recommended change

In `supportedProduct_hasDerivWithinAt`, retain the construction of `hd` using
`clm_apply`, then replace both `change` steps and the final `rwa` with:

```
  dsimp only [extendPath] at hd
  simp only [projIcc_of_mem hT t.property] at hd
  exact hd
```

`dsimp` exposes the clamped time argument, `simp only` removes the clamp at `t`,
and `exact` checks the remaining definitional equalities of the multiplier maps.
The statement, hypotheses, and endpoint behavior are unchanged.

## Measurements

With the repository's Lean v4.34.0-rc2 and current dependencies, command-level
`#count_heartbeats in` measured approximately:

* Original proof: 223,000 heartbeats; removing its override alone times out at
  the default limit of 200,000.
* Replacing only the final `rwa` with
  `simpa only [projIcc_of_mem hT t.property] using hd`: 190,000 heartbeats.
* The replacement below: 120,500 heartbeats.

Tactic profiling attributes about 35,100 and 34,700 heartbeats to the original
two `change` steps and 33,300 to the final `rwa`. The one-line `simpa only`
alternative costs about 413. Splitting `rwa` into its components shows that
the rewrite itself accounts for almost all of its cost.

To reproduce counts, temporarily import `Mathlib.Util.CountHeartbeats` and put
`#count_heartbeats in` between `include hA in` and the product theorem's docstring.
That profiling command disables the limit while counting; the actual acceptance
check below uses the normal default limit, with no profiling wrapper:

```
lake env lean -DautoImplicit=false -DwarningAsError=true -DElab.async=false \
  Euler/LpCylinderCoefficientTimeInvestigation.lean
```
-/

noncomputable section

namespace EulerLpCylinderRectangular.CoefficientTimeInvestigation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients
  EulerVolterraConvolution
open scoped BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

section Square

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (S : Set Space) (hS : MeasurableSet S)

/-- The two literal constructions are the same actual supported L² operator. -/
theorem supportedOperator_eq_square (A : Space →ᵇ V →L[ℝ] V) :
    supportedOperatorMap period S hS A = liftedOperator period S hS A := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period A)
      (u : CylinderL2 period V),
    EulerLpSupportedMultiplier.full_ae (liftMeasure period) (fieldLift period A)
      (u : CylinderL2 period V)] with x hl hr
  exact hl.trans hr.symm

theorem supportedPath_eq_square (T : ℝ) (A : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)) :
    supportedPathMap period S hS A = liftedOperatorPath period S hS T A := by
  apply ContinuousMap.ext
  intro t
  exact supportedOperator_eq_square period S hS (A t)

end Square

section Time

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (S : Set Space) (hS : MeasurableSet S) (T : ℝ) (hT : 0 ≤ T)
  (A A₁ : C(Icc (0 : ℝ) T,Space →ᵇ E →L[ℝ] F))

private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Supported period E S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period F S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period F S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period E S hS →L[ℝ] Supported period F S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS →L[ℝ] Supported period F S hS) := inferInstance

variable (hA : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
  HasDerivWithinAt (fun s => extendPath T hT A s x)
    (extendPath T hT A₁ t x) (Icc (0 : ℝ) T) t)

include hA in
/-- The true derivative of the actual supported coefficient operator. -/
theorem supportedPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (supportedPathMap period S hS A))
      (supportedPathMap period S hS A₁ t) (Icc (0 : ℝ) T) t := by
  have hfield := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT A A₁ hA t t.property
  have hlinear : HasFDerivAt
      (fun B : Space →ᵇ E →L[ℝ] F => supportedOperatorMap period S hS B)
      (supportedOperatorMap period S hS) (extendPath T hT A t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space →ᵇ E →L[ℝ] F)
      (F := Supported period E S hS →L[ℝ] Supported period F S hS)
      (supportedOperatorMap period S hS)
  have hd := hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => supportedOperatorMap period S hS (A (projIcc 0 T hT s)))
    (supportedOperatorMap period S hS (A₁ t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => supportedOperatorMap period S hS (A (projIcc 0 T hT s)))
    (supportedOperatorMap period S hS (A₁ (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd

include hA in
/-- The product rule is a genuine within-time statement, including the interval endpoints. -/
theorem supportedProduct_hasDerivWithinAt
    (u u₁ : C(Icc (0 : ℝ) T,Supported period E S hS))
    (hu : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT u) (u₁ t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (supportedMultiplierMap period S hS A u))
      (supportedMultiplierMap period S hS A₁ u t + supportedMultiplierMap period S hS A u₁ t)
      (Icc (0 : ℝ) T) t := by
  have hd := (supportedPath_hasDerivWithinAt period S hS T hT A A₁ hA t).clm_apply (hu t)
  dsimp only [extendPath] at hd
  simp only [projIcc_of_mem hT t.property] at hd
  exact hd

end Time

end EulerLpCylinderRectangular.CoefficientTimeInvestigation
