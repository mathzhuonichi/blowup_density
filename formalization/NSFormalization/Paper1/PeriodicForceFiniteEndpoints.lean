import NSFormalization.Paper1.PeriodicForceTopology
import NSFormalization.Paper1.PeriodicScalarForceEndpoints

/-!
# Finite endpoint gauges for concrete periodized compact forces

The abstract `IsTestForce` class records smoothness, periodicity, and compact
positive-time support, but those facts alone are intentionally not used to
assert that every Sobolev time gauge is finite.  This file supplies the
finite endpoint result for the concrete fields actually obtained by
periodizing a smooth compact spacetime force.  The proof uses the endpoint
identities already established in `PeriodicScalarForceEndpoints` and the
compact time support supplied by `PeriodicBridge.time_support_periodize`.
-/

noncomputable section
namespace NSFormalization.Paper1.PeriodicForceFiniteEndpoints

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization NavierStokes.PeriodicIntegration
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicBridge
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicForceTopology
open NSFormalization.Paper1.PeriodicScalarForceEndpoints
open scoped ContDiff ENNReal Topology

private theorem memLp_periodized_scalar_endpoint
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (s : ℝ) (hprofile : Continuous
      (fun t => periodicSobolevNorm s (fun x => periodize F (t, x)))) :
    ∀ q : ℝ≥0∞, MemLp
      (fun t => periodicSobolevNorm s (fun x => periodize F (t, x))) q volume := by
  intro q
  apply hprofile.memLp_of_hasCompactSupport
  apply HasCompactSupport.intro
    ((hc : IsCompact (tsupport F)).image continuous_fst)
  intro t ht
  have hz : (fun x : Space => F (t, x)) = 0 := by
    funext x
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact ht ⟨(t, x), htx, rfl⟩
  have hp : (fun x : Space => periodize F (t, x)) = 0 := by
    funext x
    apply periodize_eq_zero_of_timeSlice
    intro y
    exact congrFun hz y
  rw [hp]
  unfold periodicSobolevNorm periodicSobolevSq
  congr 1
  have heq : (fun k : PeriodicFrequency =>
      periodicFrequencyWeight k ^ s *
        ‖periodicFourierCoeff (0 : Space → ℂ) k‖ ^ 2) =
      (fun _ => (0 : ℝ)) := by
    funext k
    rw [periodicFourierCoeff_eq_cube]
    have hcub : cubeIntegral (fun _ : Space => (0 : ℂ)) = 0 := by
      simp [cubeIntegral]
    simp [hcub]
  rw [heq, tsum_zero]
  simp

theorem memLp_periodized_scalar_zero
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (q : ℝ≥0∞) : MemLp
      (fun t => periodicSobolevNorm 0 (fun x => periodize F (t, x))) q volume :=
  memLp_periodized_scalar_endpoint hS hr hF hc 0
    (continuous_periodized_zero_time hS hr hF hc) q

theorem memLp_periodized_scalar_one
    {r : ℝ} {F : SpaceTime → ℂ} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (q : ℝ≥0∞) : MemLp
      (fun t => periodicSobolevNorm 1 (fun x => periodize F (t, x))) q volume :=
  memLp_periodized_scalar_endpoint hS hr hF hc 1
    (continuous_periodized_one_time hS hr hF hc) q

theorem isTestForce_periodize
    {r : ℝ} {F : VelocityField} (hS : SupportedInCube r F)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hpos : tsupport F ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :
    IsTestForce (periodize F) := by
  refine ⟨contDiff_periodize hS hF, unitSpatialPeriodsOn_periodize F univ,
    ?_⟩
  refine ⟨Prod.fst '' tsupport F, (hc : IsCompact (tsupport F)).image continuous_fst,
    ?_, ?_⟩
  · intro t ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact (hpos hz).1
  · intro z hz
    exact ⟨time_support_periodize hc hz, mem_univ _⟩

theorem forceDistance_lt_top_periodized_zero
    {r : ℝ} {F : VelocityField} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hpos : tsupport F ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :
    forceDistance 0 (periodize F) 0 < (⊤ : ℝ≥0∞) := by
  let htest : IsTestForce (periodize F) := isTestForce_periodize hS hF hc hpos
  apply forceDistance_lt_top_of_testForces htest isTestForce_zero 0
  intro i
  have hcoord : (fun z => coordinateForce (periodize F) i z) =
      periodize (coordinateForce F i) := by
    have hp := periodize_comp hS hr
      (fun v : Space => (v i : ℂ)) (by simp)
    funext z
    exact congrFun hp z
  have hS_i : SupportedInCube r (coordinateForce F i) :=
    supported_comp hS (fun v : Space => (v i : ℂ)) (by simp)
  have hF_i : ContDiff ℝ ∞ (coordinateForce F i) := coordinateForce_smooth hF i
  have hc_i : HasCompactSupport (coordinateForce F i) := coordinateForce_compact hc i
  have hm := memLp_periodized_scalar_zero hS_i hr hF_i hc_i 1
  rw [← hcoord] at hm
  simpa [Pi.sub_apply, coordinateForce] using hm

theorem forceDistance_lt_top_periodized_one
    {r : ℝ} {F : VelocityField} (hS : SupportedInCube r F)
    (hr : r < 1 / 2) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hpos : tsupport F ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space)) :
    forceDistance 1 (periodize F) 0 < (⊤ : ℝ≥0∞) := by
  let htest : IsTestForce (periodize F) := isTestForce_periodize hS hF hc hpos
  apply forceDistance_lt_top_of_testForces htest isTestForce_zero 1
  intro i
  have hcoord : (fun z => coordinateForce (periodize F) i z) =
      periodize (coordinateForce F i) := by
    have hp := periodize_comp hS hr
      (fun v : Space => (v i : ℂ)) (by simp)
    funext z
    exact congrFun hp z
  have hS_i : SupportedInCube r (coordinateForce F i) :=
    supported_comp hS (fun v : Space => (v i : ℂ)) (by simp)
  have hF_i : ContDiff ℝ ∞ (coordinateForce F i) := coordinateForce_smooth hF i
  have hc_i : HasCompactSupport (coordinateForce F i) := coordinateForce_compact hc i
  have hm := memLp_periodized_scalar_one hS_i hr hF_i hc_i 1
  rw [← hcoord] at hm
  simpa [Pi.sub_apply, coordinateForce] using hm

end NSFormalization.Paper1.PeriodicForceFiniteEndpoints
