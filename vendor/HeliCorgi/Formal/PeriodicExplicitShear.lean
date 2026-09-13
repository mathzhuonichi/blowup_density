import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert

noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace ExplicitShear

def amplitude (ν a k t : ℝ) : ℝ := a * Real.exp (-ν * k^2 * t)
def profile (ν a k t y : ℝ) : ℝ := amplitude ν a k t * Real.sin (k*y)

theorem amplitude_hasDerivAt (ν a k t : ℝ) :
    HasDerivAt (amplitude ν a k) (-ν * k^2 * amplitude ν a k t) t := by
  unfold amplitude
  convert! (((hasDerivAt_id t).const_mul (-ν * k^2)).exp.const_mul a) using 1
  simp only [id, mul_one]
  ring

theorem profile_time_hasDerivAt (ν a k t y : ℝ) :
    HasDerivAt (fun s => profile ν a k s y) (-ν * k^2 * profile ν a k t y) t := by
  simpa [profile, mul_comm, mul_left_comm, mul_assoc] using
    (amplitude_hasDerivAt ν a k t).mul_const (Real.sin (k*y))

theorem profile_space_hasDerivAt (ν a k t y : ℝ) :
    HasDerivAt (profile ν a k t) (amplitude ν a k t * (Real.cos (k*y) * k)) y := by
  unfold profile
  convert! (((hasDerivAt_id y).const_mul k).sin.const_mul (amplitude ν a k t)) using 1
  simp

theorem profile_space_deriv (ν a k t : ℝ) :
    deriv (profile ν a k t) = fun y => amplitude ν a k t * (Real.cos (k*y) * k) := by
  funext y
  exact (profile_space_hasDerivAt ν a k t y).deriv

theorem profile_space_second_deriv (ν a k t y : ℝ) :
    deriv (deriv (profile ν a k t)) y = -k^2 * profile ν a k t y := by
  rw [profile_space_deriv]
  have h := (((hasDerivAt_id y).const_mul k).cos.mul_const k).const_mul (amplitude ν a k t)
  convert h.deriv using 1 <;> simp [profile, pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem profile_heat_equation (ν a k t y : ℝ) :
    deriv (fun s => profile ν a k s y) t = ν * deriv (deriv (profile ν a k t)) y := by
  rw [(profile_time_hasDerivAt ν a k t y).deriv, profile_space_second_deriv]
  ring

theorem profile_periodic (ν a t y : ℝ) :
    profile ν a (2 * Real.pi) t (y + 1) = profile ν a (2 * Real.pi) t y := by
  simp only [profile]
  congr 1
  convert Real.sin_add_two_pi (2 * Real.pi * y) using 1
  congr 1
  ring

theorem profile_contDiff (ν a k : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => profile ν a k z.1 z.2) := by
  unfold profile amplitude
  exact (contDiff_const.mul ((contDiff_const.mul contDiff_fst).exp)).mul
    ((contDiff_const.mul contDiff_snd).sin)

theorem profile_abs_le (ν a k t y : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    |profile ν a k t y| ≤ |a| := by
  have hprod : 0 ≤ ν * k ^ 2 * t := mul_nonneg (mul_nonneg hν (sq_nonneg k)) ht
  have hexp : Real.exp (-ν * k ^ 2 * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simpa only [neg_mul] using neg_nonpos.mpr hprod
  rw [profile, amplitude, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |a| * Real.exp (-ν * k ^ 2 * t) * |Real.sin (k * y)|
        ≤ |a| * Real.exp (-ν * k ^ 2 * t) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
        (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    _ ≤ |a| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (abs_nonneg a)

theorem profile_initial (ν a k y : ℝ) :
    profile ν a k 0 y = a * Real.sin (k * y) := by
  simp [profile, amplitude]

theorem profile_initial_nonzero (ν a : ℝ) (ha : a ≠ 0) :
    profile ν a (2 * Real.pi) 0 (1 / 4) ≠ 0 := by
  rw [profile_initial]
  have harg : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  simpa only [harg, Real.sin_pi_div_two, mul_one] using ha

#print axioms profile_heat_equation
#print axioms profile_contDiff
#print axioms profile_abs_le
#print axioms profile_initial_nonzero
end ExplicitShear
