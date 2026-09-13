import NSFormalization.Paper3.SobolevTimeRegularity
import NSFormalization.Paper3.TimeDifferenceQuotient
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Smoothness of the actual Sobolev-valued trajectory, proved by a genuine
Banach-valued difference quotient and then iterated on temporal derivatives. -/
noncomputable section
namespace NSFormalization.Paper3
open Set Filter MeasureTheory NavierStokes.ProblemStatement
open scoped ContDiff ENNReal Topology

/-- The actual Sobolev-vector difference is the time increment multiplied by
the actual Sobolev vector of the averaged physical temporal derivative. -/
theorem sobolevTimeSlice_sub_eq_smul_average (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a t : ℝ) :
    sobolevTimeSlice s F hF hK hz t - sobolevTimeSlice s F hF hK hz a =
      (t - a) • sobolevTimeSlice s (averagedTimeDerivative a F)
        (averagedTimeDerivative_smooth hF a) hK (averagedTimeDerivative_support hK hz a) t := by
  unfold sobolevTimeSlice compactFourierLp
  rw [← map_sub, ← map_smul]
  congr 1
  ext x
  exact time_difference_eq_smul_average hF a t x

/-- The derivative of the actual Sobolev trajectory is the actual Sobolev
vector of the physical time derivative, at every real Sobolev order. -/
theorem hasDerivAt_sobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a : ℝ) :
    HasDerivAt (sobolevTimeSlice s F hF hK hz)
      (sobolevTimeSlice s (spacetimeTimeDerivative F) (spacetimeTimeDerivative_smooth hF)
        hK (spacetimeTimeDerivative_support hK hz) a) a := by
  let G := averagedTimeDerivative a F
  have hG := averagedTimeDerivative_smooth hF a
  have hzG := averagedTimeDerivative_support hK hz a
  have hc := (continuous_sobolevTimeSlice s hG hK hzG).continuousAt (x := a)
  have he : slope (sobolevTimeSlice s F hF hK hz) a =ᶠ[𝓝[≠] a]
      sobolevTimeSlice s G hG hK hzG := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hta : t - a ≠ 0 := sub_ne_zero.mpr ht
    rw [slope_def_module, sobolevTimeSlice_sub_eq_smul_average s hF hK hz a t,
      smul_smul, inv_mul_cancel₀ hta, one_smul]
  have hv : sobolevTimeSlice s G hG hK hzG a =
      sobolevTimeSlice s (spacetimeTimeDerivative F) (spacetimeTimeDerivative_smooth hF)
        hK (spacetimeTimeDerivative_support hK hz) a := by
    unfold sobolevTimeSlice compactFourierLp
    congr 1
    ext x
    exact averagedTimeDerivative_at F a x
  apply hasDerivAt_iff_tendsto_slope.mpr
  rw [← hv]
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

/-- Every finite time regularity order holds in the genuine weighted Fourier
L² Banach space; this inducts on actual physical temporal derivatives. -/
theorem contDiff_sobolevTimeSlice_nat (n : ℕ) (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) :
    ContDiff ℝ n (sobolevTimeSlice s F hF hK hz) := by
  induction n generalizing F with
  | zero =>
    exact (contDiff_zero).mpr (continuous_sobolevTimeSlice s hF hK hz)
  | succ n ih =>
    have hd : deriv (sobolevTimeSlice s F hF hK hz) =
        sobolevTimeSlice s (spacetimeTimeDerivative F) (spacetimeTimeDerivative_smooth hF)
          hK (spacetimeTimeDerivative_support hK hz) := by
      funext a
      exact (hasDerivAt_sobolevTimeSlice s hF hK hz a).deriv
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun a => (hasDerivAt_sobolevTimeSlice s hF hK hz a).differentiableAt, by simp, ?_⟩
    rw [hd]
    exact ih (spacetimeTimeDerivative_smooth hF) (spacetimeTimeDerivative_support hK hz)

/-- A jointly smooth uniformly spatially compact physical family defines a
C∞ trajectory in the genuine Sobolev representation at every real order. -/
theorem contDiff_sobolevTimeSlice (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) :
    ContDiff ℝ ∞ (sobolevTimeSlice s F hF hK hz) :=
  contDiff_infty.mpr (fun n => contDiff_sobolevTimeSlice_nat n s hF hK hz)

end NSFormalization.Paper3
