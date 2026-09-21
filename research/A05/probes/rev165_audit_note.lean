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

example : ∃ G : NSFormalization.Paper3.RealVectorSobolev (1 / 2 : ℝ), IsHomogeneousSliceDatum (1 / 2 : ℝ) zB G := (isHomogeneousSliceDatum_compact (s := (1 / 2 : ℝ)) (by norm_num) bumpField_smooth bumpField_compact).1

end Lane165AxiomAudit

