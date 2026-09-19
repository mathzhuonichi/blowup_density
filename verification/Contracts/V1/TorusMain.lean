import Contracts.V1.TorusNonDensity
import Contracts.V1.Density
import Contracts.V1.CriticalRegularityT

/-!
# Contract: the main torus density threshold

This is `thm:main` from `03-torus.tex:6-16`, proved at `:522-524`.  It fixes
the time exponent at one and records no nonzero-datum converse at or above the
critical order, in accordance with the scope remark at `:525`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TorusMain
set_option linter.defProp false

open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity

/-- **`thm:main`, `03-torus.tex:6-16`, proof `:522-524`.** -/
structure MainTheoremAPI : Prop where
  thresholdValue : criticalOrder 1 = (1 : ℝ) / 2
  zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT
  fixedInitialDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
  zeroInitialDensityIff : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2
  zeroInitialNonDensity : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ s : ℝ, 1 / 2 ≤ s →
      ¬ RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T)

/-- **`thm:main` in the paper's order, `03-torus.tex:6-16`.** -/
def mainStatement : Prop :=
  (∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
    (∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2)

/-- `03-torus.tex:523`: the main theorem consumes density and non-density. -/
def mainOfDensityAndNonDensity : Prop :=
  ∀ c : ℝ,
    BlowupDensity.Contracts.V1.Density.PeriodicDensityAPI →
      NonDensityAPI c → MainTheoremAPI

/-- The registered T19/T20 two-input form of the final assembly. -/
def mainOfInputs : Prop :=
  BlowupDensity.Contracts.V1.Density.PeriodicDensityAPI →
    BlowupDensity.Contracts.V1.CriticalRegularityT.CriticalRegularityTAPI →
      MainTheoremAPI

end BlowupDensity.Contracts.V1.TorusMain
