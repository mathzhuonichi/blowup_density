import NSFormalization.Section3.T21.Main

noncomputable section

namespace NSFormalization.Section3.T21.MainCloses

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19 (PeriodicDensityAPI periodicDensityAPI criticalOrder)
open NSFormalization.Section3.T21
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ENNReal

local notation "breakdownSetTZero" =>
  (fun nu T => breakdownSetT nu (fun _ : Space ↦ 0) T)

variable (D : PeriodicDensityAPI)
variable (nonDensity : ∀ nu : ℝ, 0 < nu → ∀ s : ℝ, 1 / 2 ≤ s →
  ∀ T : ℝ, 0 < T →
    ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T))

example : criticalOrder 1 = (1 : ℝ) / 2 := by
  exact thresholdValue

example : (fun _ : Space ↦ 0) ∈ initialClassT := by
  exact zeroInitialClass

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T) := by
  exact fixedInitialDensity D

example : ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T) ↔ s < 1 / 2 := by
  exact zeroInitialDensityIff D nonDensity

example : ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T) := by
  exact zeroInitialNonDensity nonDensity

example : MainTheoremAPI := by
  exact mainTheoremAPI periodicDensityAPI nonDensity

example : MainTheoremAPI := by
  exact mainOfDensityAndNonDensity_holds periodicDensityAPI nonDensity

end NSFormalization.Section3.T21.MainCloses
