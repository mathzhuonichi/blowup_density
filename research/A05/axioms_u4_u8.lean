import NSFormalization.Section4.R43.ShiftedData
import NSFormalization.Section4.A04.ZeroSolution

/-!
# Axiom and satisfiability audit for lane 191 (A05 U4/U8)

The printed declarations must depend on exactly
`[propext, Classical.choice, Quot.sound]`.  The examples check both the zero
instance requested by the lane and a genuinely nonzero compact-smooth
(therefore componentwise Schwartz) field.  Its `MemHInfty` and order-`3/2`
datum hypotheses are restrictions of the tree's standard compact-smooth
regularity and homogeneous-datum existence theorems.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open NSFormalization.Section4.A05
open NSFormalization.Section4.R43
open scoped ContDiff ENNReal

namespace Lane191AxiomAudit

local notation "zB" =>
  (fun x : Space => (Cut.bump x) • (coordinateVector 0 : Space))

theorem bumpField_smooth : ContDiff ℝ ∞ zB :=
  Cut.bump_smooth.smul contDiff_const

theorem bumpField_compact : HasCompactSupport zB := by
  exact Cut.bump_cs.comp_left
    (g := fun c : ℝ => c • (coordinateVector 0 : Space)) (by simp)

theorem bumpField_memHInfty :
    NSFormalization.Section4.A02.MemHInfty zB := by
  apply memHInfty_of_contDiff_memLp bumpField_smooth
  intro n
  exact (bumpField_smooth.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
    (bumpField_compact.iteratedFDeriv n)

theorem bumpField_ne_zero : zB ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Space)
  have hb : Cut.bump (0 : Space) = 1 := Cut.bump_one (by simp)
  have hc := congrArg (fun v : Space => v 0) h0
  simp [hb, coordinateVector] at hc

theorem bumpField_has_threeHalf_datum :
    ∃ Z : RealVectorSobolev (3 / 2),
      IsHomogeneousSliceDatum (3 / 2) zB Z :=
  (isHomogeneousSliceDatum_compact (s := (3 / 2 : ℝ))
    (by norm_num) bumpField_smooth bumpField_compact).1

/-- The two named inputs of `shiftedCriticalData_of_memHInfty` are genuinely
satisfiable for a nonzero field with Schwartz components. -/
theorem nonvac_shiftedCriticalData :
    zB ≠ 0 ∧ ∃ Z : RealVectorSobolev (3 / 2),
      IsHomogeneousSliceDatum (3 / 2) zB Z ∧
        Nonempty (ShiftedCriticalData zB Z) := by
  obtain ⟨Z, hZ⟩ := bumpField_has_threeHalf_datum
  exact ⟨bumpField_ne_zero, Z, hZ,
    ⟨shiftedCriticalData_of_memHInfty zB bumpField_memHInfty Z hZ⟩⟩

example :
    ShiftedCriticalData (0 : SpatialField)
      (0 : RealVectorSobolev (3 / 2)) :=
  shiftedCriticalData_of_memHInfty 0
    NSFormalization.Section4.A04.zero_mem_initialClassR.1 0
    (isHomogeneousSliceDatum_zero (3 / 2))

example :
    zB ≠ 0 ∧ ∃ Z : RealVectorSobolev (3 / 2),
      IsHomogeneousSliceDatum (3 / 2) zB Z ∧
        Nonempty (ShiftedCriticalData zB Z) :=
  nonvac_shiftedCriticalData

end Lane191AxiomAudit

-- Every exported declaration of the two new modules.
#print axioms derivativeSymbol
#print axioms derivativeSymbol_measurable
#print axioms derivativeSymbol_memLp
#print axioms derivativeSymbolLp
#print axioms derivativeSymbolLp_ae
#print axioms derivativeSymbol_conj_neg
#print axioms rieszFrequencyL2
#print axioms rieszFrequencyL2_ae
#print axioms rieszPhysicalL2C
#print axioms fourier_rieszPhysicalL2C
#print axioms translationPhase
#print axioms translationPhase_continuous
#print axioms translationPhase_norm
#print axioms translationPhaseLp
#print axioms translationPhaseLp_ae
#print axioms translationPhaseMultiplier
#print axioms translationPhaseMultiplier_ae
#print axioms fourier_translation
#print axioms rieszPhysicalL2C_translation
#print axioms complexifyFiber
#print axioms complexifyLp
#print axioms realifyFiber
#print axioms realifyLp
#print axioms complexifyFiber_apply
#print axioms realifyFiber_complexifyFiber
#print axioms complexifyLp_ae
#print axioms realifyLp_ae
#print axioms realifyLp_complexifyLp
#print axioms complexifyLp_isReal
#print axioms complexifyLp_realifyLp_of_isReal
#print axioms complexifyLp_translation
#print axioms realifyLp_translation
#print axioms conjugateSymmetric_ae
#print axioms rieszFrequencyL2_conjugateSymmetric
#print axioms rieszPhysicalL2C_isReal
#print axioms rieszPhysicalL2
#print axioms complexifyLp_rieszPhysicalL2
#print axioms rieszPhysicalL2_translation
#print axioms coordinates_fourier
#print axioms componentLp_smoothField
#print axioms fourier_directionalField_component_ae
#print axioms sourceSmoothField
#print axioms rieszLambdaL2
#print axioms rieszLambdaL2_smoothOrbit
#print axioms rieszLambda
#print axioms rieszLambda_toLp
#print axioms rieszLambdaMemLp
#print axioms rieszLambda_memHInfty
#print axioms riesz_symbol_derivative_sum
#print axioms fourier_rieszLambdaL2_component_ae
#print axioms angularFourierDistribution_lp
#print axioms isSliceDistribution_componentLp
#print axioms homogeneousDatum_angularFourier_ae
#print axioms fourier_rieszLambda_component_ae
#print axioms angular_rieszLambda_component_ae
#print axioms rieszLambda_halfDatum
#print axioms derivativeFourierDatum
#print axioms derivativeFourierDatum_ae
#print axioms derivativeFourierDatum_realSymmetry
#print axioms derivativeHalfComponent
#print axioms derivativeHalfComponent_coe
#print axioms derivativeHalfDatum
#print axioms derivativeHalfDatum_symbol
#print axioms angularCoordinateLinearSymbol
#print axioms angularCoordinateLinearSymbol_temperate
#print axioms angularCoordinateTest
#print axioms angularCoordinateTest_apply
#print axioms angularFourierDistribution_lineDeriv
#print axioms isSliceDistribution_dirDeriv
#print axioms isHomogeneousDatum_derivativeHalf
#print axioms derivativeHalfDatum_isDatum
#print axioms shiftedCriticalData_of_memHInfty
#print axioms criticalAdvectionLpBridge_shifted

-- Nonzero satisfiability witness.
#print axioms Lane191AxiomAudit.bumpField_smooth
#print axioms Lane191AxiomAudit.bumpField_compact
#print axioms Lane191AxiomAudit.bumpField_memHInfty
#print axioms Lane191AxiomAudit.bumpField_ne_zero
#print axioms Lane191AxiomAudit.bumpField_has_threeHalf_datum
#print axioms Lane191AxiomAudit.nonvac_shiftedCriticalData
