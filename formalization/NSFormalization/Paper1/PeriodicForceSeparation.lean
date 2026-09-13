import NSFormalization.Paper1.PeriodicForceTopology
import NSFormalization.Paper1.PeriodicSmoothSobolev
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Separation interface for the periodic force gauge

At order zero, smooth periodic force profiles are continuous in time.  On the
real line, equality almost everywhere between continuous profiles upgrades to
pointwise equality.  Consequently a zero `forceDistance` profile at order zero
is pointwise zero.  This file deliberately stops at the profile level; an
identification of zero periodic Sobolev norm with a zero spacetime force is a
separate Fourier/Parseval bridge.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicForceSeparation

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicForceTopology
open scoped ContDiff ENNReal Topology

/-- The order-zero profile of smooth periodic forces is continuous in time. -/
theorem continuous_forceProfile_zero
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂) :
    Continuous (forceProfile 0 f₁ f₂) := by
  have hsub : ContDiff ℝ ∞ (f₁ - f₂) := h₁.smooth.sub h₂.smooth
  have hE (i : Fin 3) : Continuous (fun t : ℝ =>
      periodicIntegerEnergy 0
        (fun x => coordinateForce (f₁ - f₂) i (t, x))) :=
    continuous_periodicIntegerEnergy_time 0 (coordinateForce_smooth hsub i)
  have hsum : Continuous (fun t : ℝ => ∑ i : Fin 3,
      periodicIntegerEnergy 0
        (fun x => coordinateForce (f₁ - f₂) i (t, x))) :=
    continuous_finsetSum _ (fun i _ => hE i)
  have hrepr : forceProfile 0 f₁ f₂ = (fun t : ℝ => Real.sqrt (∑ i : Fin 3,
      periodicIntegerEnergy 0
        (fun x => coordinateForce (f₁ - f₂) i (t, x)))) := by
    funext t
    unfold forceProfile periodicVectorSobolevNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hp : UnitPeriods (fun x => coordinateForce (f₁ - f₂) i (t, x)) := by
      intro x j
      dsimp [coordinateForce]
      have h₁p := h₁.periodic t (Set.mem_univ _) x j
      have h₂p := h₂.periodic t (Set.mem_univ _) x j
      simpa [Complex.ofReal_sub] using
        congrArg₂ (fun a b : Space => ((a i : ℝ) : ℂ) - ((b i : ℝ) : ℂ)) h₁p h₂p
    have hc : Continuous (fun x : Space => coordinateForce (f₁ - f₂) i (t, x)) :=
      ((coordinateForce_smooth hsub i).comp
        (contDiff_const.prodMk contDiff_id)).continuous
    simpa [periodicIntegerEnergy] using (periodicSobolevSq_zero hc)
  rw [hrepr]
  exact Real.continuous_sqrt.comp hsum

/-- Almost-everywhere zero order-zero profile is pointwise zero. -/
theorem forceProfile_zero_of_ae_zero
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂)
    (hzero : forceProfile 0 f₁ f₂ =ᵐ[volume] 0) :
    forceProfile 0 f₁ f₂ = 0 := by
  apply Measure.eq_of_ae_eq hzero
  · exact continuous_forceProfile_zero h₁ h₂
  · exact continuous_const

/-- Separation of the order-zero gauge at the profile level. -/
theorem forceDistance_zero_iff_profile_zero
    {f₁ f₂ : VelocityField} (h₁ : IsTestForce f₁) (h₂ : IsTestForce f₂) :
    forceDistance 0 f₁ f₂ = 0 ↔ forceProfile 0 f₁ f₂ =ᵐ[volume] 0 := by
  constructor
  · intro h
    rw [forceDistance_eq_profile] at h
    exact (eLpNorm_eq_zero_iff
      (stronglyMeasurable_forceProfile_of_testForces h₁ h₂ 0).aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≠ 0)).1 h
  · exact forceDistance_eq_zero_of_testForces_of_ae_zero h₁ h₂

end NSFormalization.Paper1.PeriodicForceSeparation
