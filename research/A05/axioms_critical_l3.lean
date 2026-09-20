import NSFormalization.Section4.A05.CriticalL3
import NSFormalization.Section4.D01.OrderZeroSymbol

/-!
# Axiom and non-vacuity audit for lane 165 A05

Every theorem exported by `Section4/A05/CriticalL3.lean`, together with the
nonzero compact-smooth witness below, must print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open NSFormalization.Section4.A05
open scoped ContDiff ENNReal

namespace Lane165AxiomAudit

local notation "zB" =>
  (fun x : Space => (Cut.bump x) • (coordinateVector 0 : Space))

/-- The compact bump field used for non-vacuity is smooth. -/
theorem bumpField_smooth : ContDiff ℝ ∞ zB :=
  Cut.bump_smooth.smul contDiff_const

/-- The compact bump field used for non-vacuity has compact support. -/
theorem bumpField_compact : HasCompactSupport zB := by
  exact Cut.bump_cs.comp_left
    (g := fun c : ℝ => c • (coordinateVector 0 : Space)) (by simp)

/-- The compact bump field belongs to the datum-form `H^∞` class. -/
theorem bumpField_memHInfty : NSFormalization.Section4.A02.MemHInfty zB := by
  apply memHInfty_of_contDiff_memLp bumpField_smooth
  intro n
  exact (bumpField_smooth.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
    (bumpField_compact.iteratedFDeriv n)

/-- The compact bump field is genuinely nonzero. -/
theorem bumpField_ne_zero : zB ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Space)
  have hb : Cut.bump (0 : Space) = 1 := Cut.bump_one (by simp)
  have hc := congrArg (fun v : Space => v 0) h0
  simp [hb, coordinateVector] at hc

/-- Nonzero non-vacuity: `velocityCriticalL3` applies to a concrete
compactly-supported smooth field. -/
theorem nonvac_velocityCriticalL3 :
    zB ≠ 0 ∧
      eLpNorm zB 3 volume ≤
        ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) zB :=
  ⟨bumpField_ne_zero, velocityCriticalL3 zB bumpField_memHInfty⟩

example :
    zB ≠ 0 ∧
      eLpNorm zB 3 volume ≤
        ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) zB :=
  nonvac_velocityCriticalL3

end Lane165AxiomAudit

-- Module exports.
#print axioms cyclesHomogeneousDatum_norm
#print axioms cyclesHomogeneousDatum_ae
#print axioms u2_normalizedMultiplier_cyclesDatum
#print axioms u1_dotHomogeneousENorm_eq
#print axioms scalarCriticalConst_pos
#print axioms u3_fourier_criticalInputFromDatum
#print axioms u3_norm_criticalInputFromDatum
#print axioms u6_normalizedCriticalRealization_norm_le
#print axioms u6_normalizedCriticalRealization_toDistribution
#print axioms u6_scalar_eLpNorm_le
#print axioms u7_targetExponent_half
#print axioms criticalL3Const_pos
#print axioms u7_norm_le_sum_coordinates
#print axioms u7_memLp_components_of_memHInfty
#print axioms u7_component_eLpNorm_le
#print axioms u7_vector_eLpNorm_le_components
#print axioms u7_component_sum_le
#print axioms u7_vector_eLpNorm_le_of_datum
#print axioms velocityCriticalL3

-- Nonzero non-vacuity witness.
#print axioms Lane165AxiomAudit.bumpField_smooth
#print axioms Lane165AxiomAudit.bumpField_compact
#print axioms Lane165AxiomAudit.bumpField_memHInfty
#print axioms Lane165AxiomAudit.bumpField_ne_zero
#print axioms Lane165AxiomAudit.nonvac_velocityCriticalL3
