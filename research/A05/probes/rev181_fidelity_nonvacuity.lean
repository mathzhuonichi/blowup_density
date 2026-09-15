import Tests.GradientL6V2
import NSFormalization.Section4.D01.OrderZeroSymbol

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
open scoped ContDiff ENNReal

namespace Review181

/- The two implementation bridges and their composite are all definitional;
no simplification or unfolding is needed. -/
example :
    NSFormalization.Section4.A05.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm := rfl

example :
    NSFormalization.Section4.D01.dotHomogeneousENorm =
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm := rfl

example :
    NSFormalization.Section4.A05.dotHomogeneousENorm =
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm := rfl

example (v : BlowupDensity.Contracts.V1.Data.SpatialField) :
    BlowupDensity.Contracts.V1.Data.MemHInfty v =
      NSFormalization.Section4.A02.MemHInfty v := rfl

local notation "zB" =>
  (fun x : Space => (Cut.bump x) • (coordinateVector 0 : Space))

theorem bumpField_smooth : ContDiff ℝ ∞ zB :=
  Cut.bump_smooth.smul contDiff_const

theorem bumpField_compact : HasCompactSupport zB := by
  exact Cut.bump_cs.comp_left
    (g := fun c : ℝ => c • (coordinateVector 0 : Space)) (by simp)

theorem bumpField_memHInfty :
    BlowupDensity.Contracts.V1.Data.MemHInfty zB := by
  change NSFormalization.Section4.A02.MemHInfty zB
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

theorem bumpField_has_half_datum :
    ∃ G : NSFormalization.Paper3.RealVectorSobolev (1 / 2 : ℝ),
      IsHomogeneousSliceDatum (1 / 2 : ℝ) zB G :=
  (isHomogeneousSliceDatum_compact (s := (1 / 2 : ℝ))
    (by norm_num) bumpField_smooth bumpField_compact).1

theorem bumpField_registered_norm_ne_top :
    BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
      (1 / 2) zB ≠ ⊤ := by
  change NSFormalization.Section4.D01.dotHomogeneousENorm (1 / 2) zB ≠ ⊤
  exact dotHomogeneousENorm_ne_top bumpField_has_half_datum

theorem bumpField_registered_rhs_ne_top :
    ENNReal.ofReal
        (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) *
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
        (1 / 2) zB ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top bumpField_registered_norm_ne_top

example :
    zB ≠ 0 ∧
      BlowupDensity.Contracts.V1.Data.MemHInfty zB ∧
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
        (1 / 2) zB ≠ ⊤ ∧
      ENNReal.ofReal
          (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) *
        BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
          (1 / 2) zB ≠ ⊤ ∧
      eLpNorm zB 3 volume ≤
        ENNReal.ofReal
            (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) *
          BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm
            (1 / 2) zB :=
  ⟨bumpField_ne_zero, bumpField_memHInfty,
    bumpField_registered_norm_ne_top, bumpField_registered_rhs_ne_top,
    BlowupDensity.Tests.checkedGradientL6V2.velocityCriticalL3
      zB bumpField_memHInfty⟩

end Review181
