import NSFormalization.Section3.T19.Assembly
import NSFormalization.Section3.T21.Zero

/-!
# T21 main theorem: density threshold at the zero datum

This module proves units N11 and N13--N15.  The non-density conclusion is
threaded with its exact field type, with `breakdownSetTZero` unfolded, so that
this lane remains independent of the parallel construction of `NonDensityAPI`.
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19 (criticalOrder)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ENNReal

/-- Local expansion of lane 472's canonical `breakdownSetTZero`.  Keeping this
notation local avoids a duplicate declaration while the two lanes are built
independently. -/
local notation "breakdownSetTZero" =>
  (fun nu T => breakdownSetT nu (fun _ : Space ↦ 0) T)

/-- The five canonical fields of `thm:main`. -/
structure MainTheoremAPI : Prop where
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2
  zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T)
  zeroInitialDensityIff : ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T) ↔ s < 1 / 2
  zeroInitialNonDensity : ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)

/-- N11: the torus threshold is the critical order at time exponent one. -/
theorem thresholdValue : criticalOrder 1 = (1 : ℝ) / 2 :=
  NSFormalization.Section3.T19.thresholdValue

/-- N13: the fixed-initial-datum density field, with its `a`-first binders. -/
theorem fixedInitialDensity
    (D : NSFormalization.Section3.T19.PeriodicDensityAPI) :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T) :=
  D.fixedInitialDensity

/-- N14: zero-datum density holds exactly below the critical order.

The negative half is threaded in the exact binder order of
`NonDensityAPI.nonDensity` while that API is built in the parallel lane. -/
theorem zeroInitialDensityIff
    (D : NSFormalization.Section3.T19.PeriodicDensityAPI)
    (nonDensity : ∀ nu : ℝ, 0 < nu → ∀ s : ℝ, 1 / 2 ≤ s →
      ∀ T : ℝ, 0 < T →
        ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) :
    ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T) ↔ s < 1 / 2 := by
  intro nu hnu T hT s
  constructor
  · intro hdense
    by_contra hs
    exact nonDensity nu hnu s (le_of_not_gt hs) T hT hdense
  · intro hs
    exact fixedInitialDensity D (fun _ : Space ↦ 0) zeroInitialClass nu hnu T hT s hs

/-- N15: the threaded non-density conclusion with the main theorem's binders. -/
theorem zeroInitialNonDensity
    (nonDensity : ∀ nu : ℝ, 0 < nu → ∀ s : ℝ, 1 / 2 ≤ s →
      ∀ T : ℝ, 0 < T →
        ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) :
    ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, 1 / 2 ≤ s →
        ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T) := by
  intro nu hnu T hT s hs
  exact nonDensity nu hnu s hs T hT

set_option linter.defProp false in
/-- Conditional canonical package for `thm:main`.

The second argument is literally the final field of `NonDensityAPI`; after the
parallel lane lands, final assembly supplies it as `N.nonDensity`. -/
def mainTheoremAPI
    (D : NSFormalization.Section3.T19.PeriodicDensityAPI)
    (nonDensity : ∀ nu : ℝ, 0 < nu → ∀ s : ℝ, 1 / 2 ≤ s →
      ∀ T : ℝ, 0 < T →
        ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) :
    MainTheoremAPI where
  thresholdValue := thresholdValue
  zeroInitialClass := zeroInitialClass
  fixedInitialDensity := fixedInitialDensity D
  zeroInitialDensityIff := zeroInitialDensityIff D nonDensity
  zeroInitialNonDensity := zeroInitialNonDensity nonDensity

/-- The conditional `mainOfDensityAndNonDensity` assembly, expressed over the
exact `NonDensityAPI.nonDensity` field until the parallel API declaration is
available. -/
theorem mainOfDensityAndNonDensity_holds
    (D : NSFormalization.Section3.T19.PeriodicDensityAPI)
    (nonDensity : ∀ nu : ℝ, 0 < nu → ∀ s : ℝ, 1 / 2 ≤ s →
      ∀ T : ℝ, 0 < T →
        ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) :
    MainTheoremAPI :=
  mainTheoremAPI D nonDensity

end NSFormalization.Section3.T21
