import NSFormalization.Section4.R41.NonDensity
import Bindings.MaximalPartial
import Bindings.Thresholds

open scoped ENNReal
namespace NonDensityConformance
open NSFormalization.Section4
open BlowupDensity.Contracts.V1

/-! ## Implementation axiom audit -/

#print axioms R41.RMainThresholds
#print axioms R41.rMainThresholds
#print axioms R41.nonDensityZero_of_q
#print axioms R41.not_breakdownDenseR_zero_of_q
#print axioms R41.RMainNonDensity

/-! ## Threshold and Data vocabulary bridges -/

/-- Every frozen threshold-contract value gives the identical local record. -/
def toRMainThresholds (thresholds : ThresholdAPI) : R41.RMainThresholds where
  exponent := thresholds.exponent
  formula := thresholds.formula
  positive := thresholds.positive
  l1 := thresholds.l1
  l2 := thresholds.l2
  negativeIndex := thresholds.negativeIndex
  energy := thresholds.energy

/-- The local canonical exponent and the registered exponent are definitionally
equal: both are `Paper3.forceExponent q s = 2 / q - 3 / 2 - s`. -/
theorem rMainThresholds_exponent_eq :
    R41.rMainThresholds.exponent = BlowupDensity.Bindings.thresholds.exponent := rfl

example : R41.forceClassR = Data.forceClassR := rfl

theorem breakdownSetIn_eq : R41.breakdownSetIn = Data.breakdownSetIn := by
  funext Y ν a T
  unfold R41.breakdownSetIn Data.breakdownSetIn
  simp only [BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq]

theorem breakdownSetR_eq : R41.breakdownSetR = Data.breakdownSetR := by
  funext ν a T
  exact congrFun (congrFun (congrFun (congrFun breakdownSetIn_eq R41.forceClassR) ν) a) T

theorem breakdownSetRZero_eq : R41.breakdownSetRZero = Data.breakdownSetRZero := by
  funext ν T
  exact congrFun (congrFun (congrFun breakdownSetR_eq ν) (fun _ => 0)) T

example : R41.RelativelyDense = Data.RelativelyDense := rfl

theorem BreakdownDenseR_eq : R41.BreakdownDenseR = Data.BreakdownDenseR := by
  funext ν a T q s
  unfold R41.BreakdownDenseR Data.BreakdownDenseR
  rw [breakdownSetR_eq]
  rfl

#print axioms toRMainThresholds
#print axioms rMainThresholds_exponent_eq
#print axioms breakdownSetIn_eq
#print axioms breakdownSetR_eq
#print axioms breakdownSetRZero_eq
#print axioms BreakdownDenseR_eq

/-! ## Contract-vocabulary conclusions -/

/-- The combined lower-bound theorem in the frozen `ThresholdAPI` and
`Contracts.V1.Data` vocabulary. -/
theorem nonDensityZero_of_q (thresholds : ThresholdAPI) :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
          ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ Data.breakdownSetRZero ν T,
            ENNReal.ofReal ρ ≤ Data.forceSobolevENorm (ENNReal.ofReal q) s f := by
  intro q hq ν T hν hT s hs
  obtain ⟨ρ, hρ, hbound⟩ :=
    R41.nonDensityZero_of_q (toRMainThresholds thresholds) q hq ν T hν hT s hs
  refine ⟨ρ, hρ, fun f hf => hbound f ?_⟩
  rw [breakdownSetRZero_eq]
  exact hf

/-- The combined non-density theorem in the frozen `ThresholdAPI` and
`Contracts.V1.Data` vocabulary. -/
theorem not_breakdownDenseR_zero_of_q (thresholds : ThresholdAPI) :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, thresholds.exponent q 0 ≤ s →
          ¬ Data.BreakdownDenseR ν (fun _ => 0) T (ENNReal.ofReal q) s := by
  intro q hq ν T hν hT s hs
  rw [← BreakdownDenseR_eq]
  exact R41.not_breakdownDenseR_zero_of_q
    (toRMainThresholds thresholds) q hq ν T hν hT s hs

/-- The requested field instantiated with the registered threshold witness. -/
theorem registered_nonDensityZero :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, BlowupDensity.Bindings.thresholds.exponent q 0 ≤ s →
          ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ Data.breakdownSetRZero ν T,
            ENNReal.ofReal ρ ≤ Data.forceSobolevENorm (ENNReal.ofReal q) s f :=
  nonDensityZero_of_q BlowupDensity.Bindings.thresholds

#print axioms nonDensityZero_of_q
#print axioms not_breakdownDenseR_zero_of_q
#print axioms registered_nonDensityZero

example : ¬ Data.BreakdownDenseR 1 (fun _ => 0) 1
    (ENNReal.ofReal (1 : ℝ)) (1 / 2) :=
  not_breakdownDenseR_zero_of_q BlowupDensity.Bindings.thresholds 1 (Or.inl rfl)
    1 1 (by norm_num) (by norm_num) (1 / 2)
    (by norm_num [BlowupDensity.Bindings.thresholds, NSFormalization.Paper3.forceExponent])

example : ¬ Data.BreakdownDenseR 1 (fun _ => 0) 1
    (ENNReal.ofReal (2 : ℝ)) (-1 / 2) :=
  not_breakdownDenseR_zero_of_q BlowupDensity.Bindings.thresholds 2 (Or.inr rfl)
    1 1 (by norm_num) (by norm_num) (-1 / 2)
    (by norm_num [BlowupDensity.Bindings.thresholds, NSFormalization.Paper3.forceExponent])

end NonDensityConformance
