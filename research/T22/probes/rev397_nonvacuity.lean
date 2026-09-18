import NSFormalization.Section3.T22.CutoffMultiplier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source (angularFourier)
open NavierStokes.R3ConvolutionYoung (scalarConvolution)
open scoped ContDiff ENNReal
open NSFormalization.Section3.T22

def rev397Bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, by norm_num⟩

def rev397Chi : Space → ℝ := (rev397Bump : Space → ℝ)

def rev397A : Space → ℂ :=
  (Metric.ball (0 : Space) 1).indicator (fun _ ↦ (1 : ℂ))

theorem rev397A_zero : rev397A 0 = 1 := by
  simp [rev397A]

theorem rev397A_ne_zero : rev397A ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [rev397A_zero] at h0
  exact one_ne_zero h0

theorem rev397A_memLp : MemLp rev397A 2 volume :=
  memLp_indicator_const 2 measurableSet_ball (1 : ℂ) (Or.inr measure_ball_ne_top)

def rev397G (s : ℝ) : Space → ℂ :=
  fun η ↦ (besselW (-s) η : ℝ) • rev397A η

theorem rev397_weighted_profile (s : ℝ) :
    (fun η : Space ↦ (besselW s η : ℝ) • rev397G s η) = rev397A := by
  funext η
  simp only [rev397G, smul_smul]
  rw [show besselW s η * besselW (-s) η = 1 by
    unfold besselW
    rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring,
      Real.rpow_zero], one_smul]

theorem rev397_weighted_memLp (s : ℝ) :
    MemLp (fun η : Space ↦ (besselW s η : ℝ) • rev397G s η) 2 volume := by
  rw [rev397_weighted_profile]
  exact rev397A_memLp

example :
    eLpNorm (fun ξ : Space ↦ (besselW (1 / 2 : ℝ) ξ : ℝ) •
        scalarConvolution (angularFourier (fun x ↦ (rev397Chi x : ℂ)))
          (rev397G (1 / 2)) ξ) 2 volume ≤
      ENNReal.ofReal (cutoffMultiplierConst (1 / 2) rev397Chi) *
        eLpNorm (fun η : Space ↦
          (besselW (1 / 2 : ℝ) η : ℝ) • rev397G (1 / 2) η) 2 volume :=
  eLpNorm_cutoff_multiplier_le rev397Bump.contDiff rev397Bump.hasCompactSupport
    (1 / 2) (rev397G (1 / 2)) (rev397_weighted_memLp (1 / 2))
