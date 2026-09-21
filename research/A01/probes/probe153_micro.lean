import NSFormalization.Section4.A01.CarrierWords

noncomputable section
namespace Probe153Micro

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerLiftedGradientSpace
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
instance : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
  constructor; simp [AddCircle.measure_univ]

example (g0 : LiftDomain (1:ℝ) → Space) (hg0 : StronglyMeasurable g0) :
    MeasurableSet {z : AddCircle (1:ℝ) × LiftDomain (1:ℝ) | g0 z.2 = g0 (z.2 + ((0:Vector3), z.1))} := by
  have hm : Measurable (fun z : AddCircle (1:ℝ) × LiftDomain (1:ℝ) => z.2 + ((0:Vector3), z.1)) :=
    measurable_snd.add (measurable_const.prodMk measurable_fst)
  exact measurableSet_eq_fun (hg0.measurable.comp measurable_snd) (hg0.measurable.comp hm)

end Probe153Micro
