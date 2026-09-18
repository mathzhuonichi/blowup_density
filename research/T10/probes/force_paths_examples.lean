import NSFormalization.Section3.T10.ForcePaths
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal

example : MemForceT (0 : SpaceTimeField) :=
  (memForceT_iff_isTestForce _).mpr NSFormalization.Paper1.PeriodicForceSpace.isTestForce_zero

example (m : ℕ) (q : ℝ≥0∞) : forceSobolevENormT q (m : ℝ) 0 ≠ ⊤ :=
  forceSobolevENormT_ne_top
    ((memForceT_iff_isTestForce _).mpr NSFormalization.Paper1.PeriodicForceSpace.isTestForce_zero) m q

namespace ForcePathsExamples

def profile : ContDiffBump (2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def mode : PeriodicFrequency := fun i ↦ if i = 0 then 1 else 0

def force : SpaceTimeField := fun z ↦
  profile z.1 • ((NSFormalization.Paper1.periodicCharacter mode z.2).re • coordinateVector 1)

theorem profile_positive_support : tsupport (profile : ℝ → ℝ) ⊆ Ioi 0 := by
  rw [profile.tsupport_eq]
  intro t ht
  have h : |t - 2| ≤ 1 / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, profile] using ht
  have := (abs_le.mp h).1
  change 0 < t
  linarith

theorem force_mem : MemForceT force := by
  unfold force
  apply memForceT_time_smul (v := fun x ↦
    (NSFormalization.Paper1.periodicCharacter mode x).re • coordinateVector 1)
    profile.contDiff profile.hasCompactSupport profile_positive_support
  · exact (Complex.reCLM.contDiff.comp
      (NSFormalization.Paper1.periodicCharacter_smooth mode)).smul contDiff_const
  · intro x j
    dsimp
    rw [NSFormalization.Paper1.periodicCharacter_periodic mode x j]

theorem force_nonzero : force (2, 0) ≠ 0 := by
  have h : profile 2 = 1 := profile.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]
    exact profile.rIn_pos.le)
  simp only [force, h, NSFormalization.Paper1.periodicCharacter, map_zero,
    Complex.exp_zero, Complex.one_re, one_smul]
  intro hz
  have hz' := congrArg (fun x : Space ↦ x 1) hz
  norm_num [coordinateVector] at hz'

example (m : ℕ) : ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPath (m : ℝ) force G ∧ Continuous G ∧ StronglyMeasurable G := by
  obtain ⟨G, _, hc, _, hm, hp, _⟩ := force_coefficient_path force_mem m
  exact ⟨G, hp, hc, hm⟩

example (m : ℕ) : forceSobolevENormT 1 (m : ℝ) force ≠ ⊤ ∧
    forceSobolevENormT 2 (m : ℝ) force ≠ ⊤ :=
  ⟨forceSobolevENormT_ne_top force_mem m 1, forceSobolevENormT_ne_top force_mem m 2⟩

example (T : ℝ) : energyENormT T force = coefficientEnergyENormT T force :=
  energyENormT_eq T force
    (fun _ _ ↦ force_mem.1.comp (contDiff_const.prodMk contDiff_id))
    (fun t _ ↦ force_mem.2.1 t (mem_univ _))

example : mode ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [mode] at this

end ForcePathsExamples
