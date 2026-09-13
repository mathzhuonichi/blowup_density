import NSFormalization.Paper1.PeriodicTestForceNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Finite Sobolev time gauges for every smooth periodic test force

Integer-order Parseval and compactness give a uniform Sobolev bound on the
compact time support. Comparison with a dominating integer order handles
any real exponent. Strong measurability and a compact-support indicator
then prove full-line time integrability. No component integrability or
profile bound is assumed for the test-force conclusions.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicTestForceFiniteness

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceTopology
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicTestForceNorm
open scoped ContDiff ENNReal Topology

/-- A strongly measurable profile supported and bounded on a compact set is
integrable on the full time line. -/
theorem memLp_of_compact_support_bound
    {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume)
    {K : Set ℝ} (hK : IsCompact K)
    (hzero : ∀ t ∉ K, g t = 0) {C : ℝ}
    (hbound : ∀ t ∈ K, ‖g t‖ ≤ C) :
    MemLp g 1 volume := by
  let μK : Measure ℝ := volume.restrict K
  have : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hgK : AEStronglyMeasurable g μK := hg.mono_measure Measure.restrict_le_self
  have hboundK : ∀ᵐ t ∂μK, ‖g t‖ ≤ C := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
    exact hbound t ht
  have hmemK : MemLp g 1 μK := MemLp.of_bound hgK C hboundK
  have hmemI : MemLp (K.indicator g) 1 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).2 hmemK
  have hEq : K.indicator g =ᵐ[volume] g := by
    filter_upwards [] with t
    by_cases ht : t ∈ K
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht, hzero t ht]
  exact hmemI.congr_norm hg (hEq.mono (fun _ ht => congrArg norm ht))

/-- Smooth periodic scalar fields with compact time support have finite
`L¹_t H^s_x` gauge for every real `s`. -/
theorem memLp_periodicSobolevNorm_time (s : ℝ) {F : SpaceTime → ℂ}
    (hF : ContDiff ℝ ∞ F) (hp : UnitSpatialPeriodsOn univ F)
    {K : Set ℝ} (hK : IsCompact K)
    (hzero : ∀ t ∉ K, ∀ x : Space, F (t, x) = 0) :
    MemLp (fun t => periodicSobolevNorm s (fun x => F (t, x))) 1 volume := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have hcont := Real.continuous_sqrt.comp (continuous_periodicIntegerEnergy_time n hF)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hsmooth (t : ℝ) : ContDiff ℝ ∞ (fun x : Space => F (t, x)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hperiodic (t : ℝ) : UnitPeriods (fun x : Space => F (t, x)) :=
    hp t (mem_univ _)
  apply memLp_of_compact_support_bound
    (stronglyMeasurable_periodicSobolevNorm_time s hF.continuous).aestronglyMeasurable hK
    (C := C)
  · intro t ht
    have hz : (fun x : Space => F (t, x)) = 0 := funext (hzero t ht)
    rw [hz]
    simp [periodicSobolevNorm, periodicSobolevSq, periodicFourierCoeff_eq_cube, cubeIntegral]
  · intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ periodicSobolevNorm s (fun x => F (t, x)) from Real.sqrt_nonneg _)]
    calc
      periodicSobolevNorm s (fun x => F (t, x)) ≤
          periodicSobolevNorm (n : ℝ) (fun x => F (t, x)) :=
        periodicSobolevNorm_mono_smooth (hsmooth t) (hperiodic t) hn
      _ = Real.sqrt (periodicIntegerEnergy n (fun x => F (t, x))) := by
        rw [periodicSobolevNorm, periodicSobolevSq_nat n
          ((hsmooth t).of_le (by simp)) (hperiodic t)]
      _ ≤ ‖Real.sqrt (periodicIntegerEnergy n (fun x => F (t, x)))‖ :=
        le_abs_self _
      _ ≤ C := hC t ht

/-- Each actual component of an abstract manuscript test force has finite
Sobolev time gauge at every real order. -/
theorem memLp_component_of_testForce {F : VelocityField} (hF : IsTestForce F)
    (s : ℝ) (i : Fin 3) :
    MemLp (fun t => periodicSobolevNorm s
      (fun x => coordinateForce F i (t, x))) 1 volume := by
  obtain ⟨K, hK, _, hKF⟩ := hF.time_support
  apply memLp_periodicSobolevNorm_time s (coordinateForce_smooth hF.smooth i)
    (fun t ht x j => congrArg (fun v : Space => (v i : ℂ))
      (hF.periodic t ht x j)) hK
  intro t ht x
  have hz : F (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro htx
    exact ht (hKF htx).1
  simp [coordinateForce, hz]

/-- Full-line integrability of the actual difference profile follows solely
from membership in the manuscript smooth test-force class. -/
theorem memLp_forceProfile_of_testForces_all_s
    {F G : VelocityField} (hF : IsTestForce F) (hG : IsTestForce G) (s : ℝ) :
    MemLp (forceProfile s F G) 1 volume :=
  memLp_forceProfile_of_testForces hF hG s
    (fun i => memLp_component_of_testForce (isTestForce_sub hF hG) s i)

/-- The gauge is finite between any two smooth periodic test forces at every
real Sobolev order. No component `MemLp` or uniform-bound premise remains. -/
theorem forceDistance_lt_top_of_testForces_all_s
    {F G : VelocityField} (hF : IsTestForce F) (hG : IsTestForce G) (s : ℝ) :
    forceDistance s F G < (⊤ : ℝ≥0∞) :=
  (memLp_forceProfile_of_testForces_all_s hF hG s).eLpNorm_lt_top

end NSFormalization.Paper1.PeriodicTestForceFiniteness
