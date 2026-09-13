import NSFormalization.Paper3.SpatiallyCompactTime
import Euler.CompactParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! An actual smooth integral representation of temporal difference quotients. -/
noncomputable section
namespace NSFormalization.Paper3
open Set Filter MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal Topology

/-- The actual ambient temporal directional derivative. -/
def spacetimeTimeDerivative (F : ℝ × Space → ℂ) (z : ℝ × Space) : ℂ :=
  fderiv ℝ F z (1, 0)

 theorem spacetimeTimeDerivative_smooth {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spacetimeTimeDerivative F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

 theorem spacetimeTimeDerivative_support {F : ℝ × Space → ℂ} {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) :
    ∀ t x, x ∉ K → spacetimeTimeDerivative F (t, x) = 0 :=
  family_derivative_support hK hz (1, 0)

 theorem hasDerivAt_time_slice {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Space) :
    HasDerivAt (fun r => F (r, x)) (spacetimeTimeDerivative F (t, x)) t := by
  have h := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp t
    ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t))
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
    spacetimeTimeDerivative] using h.hasDerivAt

/-- The average of the actual temporal derivative along the segment from `a`
to `t`. At `t=a` it equals the temporal derivative, and away from `a` it is the
difference quotient. -/
def averagedTimeDerivative (a : ℝ) (F : ℝ × Space → ℂ) (z : ℝ × Space) : ℂ :=
  ∫ r in (0 : ℝ)..1, spacetimeTimeDerivative F (a + r * (z.1 - a), z.2)

 theorem averagedTimeDerivative_smooth {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (a : ℝ) :
    ContDiff ℝ ∞ (averagedTimeDerivative a F) := by
  have hi : ContDiff ℝ ∞ (fun z : (ℝ × Space) × ℝ =>
      spacetimeTimeDerivative F (a + z.2 * (z.1.1 - a), z.1.2)) :=
    (spacetimeTimeDerivative_smooth hF).comp (by fun_prop)
  exact EulerCompactParameterIntegral.integral_contDiff 0 1 (by norm_num) _ hi

 theorem averagedTimeDerivative_support {F : ℝ × Space → ℂ} {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a : ℝ) :
    ∀ t x, x ∉ K → averagedTimeDerivative a F (t, x) = 0 := by
  intro t x hx
  simp [averagedTimeDerivative, spacetimeTimeDerivative_support hK hz _ x hx]

 theorem averagedTimeDerivative_at (F : ℝ × Space → ℂ) (a : ℝ) (x : Space) :
    averagedTimeDerivative a F (a, x) = spacetimeTimeDerivative F (a, x) := by
  simp [averagedTimeDerivative]

/-- Fundamental theorem of calculus for the original function, with no
Banach-valued derivative assumed. -/
theorem time_difference_eq_smul_average {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F)
    (a t : ℝ) (x : Space) :
    F (t, x) - F (a, x) = (t - a) • averagedTimeDerivative a F (t, x) := by
  have hd (r : ℝ) : HasDerivAt (fun q => F (a + q * (t - a), x))
      ((t - a) • spacetimeTimeDerivative F (a + r * (t - a), x)) r := by
    have h := (hasDerivAt_time_slice hF (a + r * (t - a)) x).scomp r
      (((hasDerivAt_id r).mul_const (t - a)).const_add a)
    simpa only [Function.comp_def, id_eq, one_mul] using h
  have hpath : Continuous (fun r : ℝ => (a + r * (t - a), x)) := by fun_prop
  have hc : Continuous (fun r : ℝ => (t - a) • spacetimeTimeDerivative F (a + r * (t - a), x)) :=
    (continuous_const : Continuous (fun _ : ℝ => t - a)).smul
      ((spacetimeTimeDerivative_smooth hF).continuous.comp hpath)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun r _ => hd r) (hc.intervalIntegrable 0 1)
  have har : a + 1 * (t - a) = t := by ring
  simpa only [intervalIntegral.integral_smul, har, zero_mul, add_zero,
    averagedTimeDerivative] using hi.symm

end NSFormalization.Paper3
