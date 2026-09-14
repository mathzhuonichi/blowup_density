import NSFormalization.Section4.A01.CarrierWords

noncomputable section
namespace Probe153Sigs

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerLiftedGradientSpace
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- product a.e. swap
#check @MeasureTheory.Measure.ae_ae_comm
#check @MeasureTheory.Measure.ae_ae_of_ae_prod
-- integral translation invariance (to_additive name)
#check @integral_add_left_eq_self
-- memLp map measure
#check @MeasureTheory.memLp_map_measure_iff
-- integral prod right measurability
#check @MeasureTheory.StronglyMeasurable.integral_prod_right
#check @MeasureTheory.AEStronglyMeasurable.integral_prod_right'
-- measurableSet eq fun
#check @measurableSet_eq_fun
-- integral const with prob measure
#check @MeasureTheory.integral_const
-- Lp strongly measurable rep
#check @MeasureTheory.Lp.aestronglyMeasurable
#check @MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk
#check @MeasureTheory.AEStronglyMeasurable.ae_eq_mk
-- MemLp congr / toLp
#check @MeasureTheory.MemLp.ae_eq
#check @MeasureTheory.MemLp.coeFn_toLp
#check @MeasureTheory.Lp.memLp
-- ordinaryLift facts
#check @EulerMeanOrdinaryLift.ordinaryLift_ae
#check @EulerMeanOrdinaryLift.ordinaryProjection_measurePreserving
-- map_eq for measure preserving
#check @MeasureTheory.MeasurePreserving.map_eq
-- Lp.ext
#check @MeasureTheory.Lp.ext
-- IsProbabilityMeasure on AddCircle volume
example : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
  constructor; simp [AddCircle.measure_univ]

end Probe153Sigs
