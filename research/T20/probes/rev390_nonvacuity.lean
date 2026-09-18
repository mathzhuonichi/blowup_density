import NSFormalization.Section3.T20.BIntegral
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T11.Transport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
Reviewer non-vacuity probe for lane 390.  The force is a nonzero single
spatial Fourier mode times a smooth compactly supported positive-time bump.
An explicit strongly measurable half-order datum path also proves that its
`criticalRho` is not `top`.
-/

noncomputable section

namespace Rev390Nonvacuity

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T20
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open scoped ContDiff ENNReal

def profile : ContDiffBump (2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def mode : PeriodicFrequency := fun i ↦ if i = 0 then 1 else 0

def spatialMode : SpatialField := fun x ↦
  (NSFormalization.Paper1.periodicCharacter mode x).re • coordinateVector 1

def force : SpaceTimeField := fun z ↦ profile z.1 • spatialMode z.2

theorem profile_positive_support : tsupport (profile : ℝ → ℝ) ⊆ Ioi 0 := by
  rw [profile.tsupport_eq]
  intro t ht
  have h : |t - 2| ≤ 1 / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, profile] using ht
  have := (abs_le.mp h).1
  change 0 < t
  linarith

theorem spatialMode_smooth : ContDiff ℝ ∞ spatialMode :=
  (Complex.reCLM.contDiff.comp
    (NSFormalization.Paper1.periodicCharacter_smooth mode)).smul contDiff_const

theorem spatialMode_periodic : IsPeriodicSpatial spatialMode := by
  intro x j
  dsimp [spatialMode]
  rw [NSFormalization.Paper1.periodicCharacter_periodic mode x j]

theorem force_mem : force ∈ forceClassT := by
  unfold force
  exact memForceT_time_smul profile.contDiff profile.hasCompactSupport
    profile_positive_support spatialMode_smooth spatialMode_periodic

theorem force_nonzero : force (2, 0) ≠ 0 := by
  have h : profile 2 = 1 := profile.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]
    exact profile.rIn_pos.le)
  simp only [force, spatialMode, h, NSFormalization.Paper1.periodicCharacter,
    map_zero, Complex.exp_zero, Complex.one_re, one_smul]
  intro hz
  have hz' := congrArg (fun x : Space ↦ x 1) hz
  norm_num [coordinateVector] at hz'

theorem criticalRho_ne_top : criticalRho force ≠ ⊤ := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum (1 / 2) spatialMode_smooth spatialMode_periodic
  let G : ℝ → PeriodicSobolev (1 / 2) := fun t ↦ profile t • A
  have hpath : IsPeriodicSobolevPath (1 / 2) force G := by
    intro t _ht
    change IsPeriodicDatum (1 / 2) (fun x ↦ profile t • spatialMode x) (profile t • A)
    exact NSFormalization.Section3.T11.Transport.isPeriodicDatum_smul hA (profile t)
  have hcont : Continuous G := profile.continuous.smul continuous_const
  have hcompact : HasCompactSupport G := by
    apply HasCompactSupport.intro profile.hasCompactSupport
    intro t ht
    have hz : profile t = 0 := image_eq_zero_of_notMem_tsupport ht
    simp [G, hz]
  have hmem : MemLp G 1 forceTimeMeasure :=
    (hcont.memLp_of_hasCompactSupport (μ := volume) (p := 1) hcompact).mono_measure
      Measure.restrict_le_self
  have hstrong : StronglyMeasurable G := by
    change StronglyMeasurable (fun t ↦ profile t • A)
    exact profile.continuous.stronglyMeasurable.smul stronglyMeasurable_const
  let Gsub : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) force H ∧
        AEStronglyMeasurable H forceTimeMeasure} :=
    ⟨G, hpath, hstrong.aestronglyMeasurable⟩
  have hle : (⨅ H : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) force H ∧
        AEStronglyMeasurable H forceTimeMeasure},
      eLpNorm H.1 1 forceTimeMeasure) ≤ eLpNorm G 1 forceTimeMeasure :=
    iInf_le (fun H : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) force H ∧
        AEStronglyMeasurable H forceTimeMeasure} ↦ eLpNorm H.1 1 forceTimeMeasure) Gsub
  unfold criticalRho forceSobolevENormT
  exact ne_top_of_le_ne_top hmem.eLpNorm_ne_top hle

example : criticalBIntegral (meanFreeForce force) ≤ criticalRho force :=
  bIntegral force force_mem

end Rev390Nonvacuity
