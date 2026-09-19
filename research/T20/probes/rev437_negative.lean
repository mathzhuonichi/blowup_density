import NSFormalization.Section3.T20.Continuation
noncomputable section
namespace NSFormalization.Section3.T20.Rev437
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11 NSFormalization.Section3.T12 NSFormalization.Section3.T20
open scoped ContDiff ENNReal BigOperators
theorem mutated_split {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    torusSobolevNormAt 2 w.velocity t ^ 2 =
      2 * ‖meanPathT g t‖ ^ 2 +
        torusSobolevNormAt 2 (meanFreeVelocity g w.velocity) t ^ 2 := by
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) :=
    classical_velocity_slice_contDiff w ht
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t ht
  have hreg := reductionRegular ν hν g hg T w t ht
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  obtain ⟨A, hA⟩ := smooth_periodic_datum (2 : ℝ) hus hup
  obtain ⟨B, hB⟩ := smooth_periodic_datum (2 : ℝ) hvSP.1 hvSP.2
  have hsu : HasSum (fun k ↦ freqEnergyT 2 w.velocity k t) (‖A‖ ^ 2) :=
    hasSum_freqEnergyT hA
  have hsv : HasSum (fun k ↦ freqEnergyT 2 (meanFreeVelocity g w.velocity) k t)
      (‖B‖ ^ 2) := hasSum_freqEnergyT hB
  have hsm : HasSum
      (fun k : PeriodicFrequency ↦ if k = 0 then ‖meanPathT g t‖ ^ 2 else 0)
      (‖meanPathT g t‖ ^ 2) := hasSum_ite_eq 0 _
  have hsum : HasSum (fun k ↦ freqEnergyT 2 w.velocity k t)
      (‖B‖ ^ 2 + ‖meanPathT g t‖ ^ 2) :=
    (hsv.add hsm).congr_fun fun k ↦ freqEnergyT_two_split hν hg w ht k
  have huniq : ‖A‖ ^ 2 = ‖B‖ ^ 2 + ‖meanPathT g t‖ ^ 2 := hsu.unique hsum
  rw [torusSobolevNormAt_eq hA, torusSobolevNormAt_eq hB, huniq]
  ring

end NSFormalization.Section3.T20.Rev437
