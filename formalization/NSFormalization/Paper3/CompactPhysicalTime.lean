import NSFormalization.Paper3.CompactFourierTime
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Actual physical time profiles and Fourier time integrability at nonpositive
inhomogeneous Sobolev orders. -/

noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- Compact spacetime support gives continuity of the actual spatial norm-power
integral, on the entire real time axis. -/
theorem continuous_integral_norm_pow_time {F : ℝ × Space → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (n : ℕ) (hn : n ≠ 0) :
    Continuous (fun t => ∫ x : Space, ‖F (t, x)‖ ^ n) := by
  let K := Prod.snd '' tsupport F
  have hK : IsCompact K := (hc : IsCompact (tsupport F)).image continuous_snd
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hK
  · exact (hF.norm.pow n).continuousOn
  · intro t x _ hx
    have hz : F (t, x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := F)
      intro htx
      exact hx ⟨(t, x), htx, rfl⟩
    simp [hz, hn]

 theorem compact_integral_norm_pow_time {F : ℝ × Space → ℂ}
    (hc : HasCompactSupport F) (n : ℕ) (hn : n ≠ 0) :
    HasCompactSupport (fun t => ∫ x : Space, ‖F (t, x)‖ ^ n) := by
  apply HasCompactSupport.intro ((hc : IsCompact (tsupport F)).image continuous_fst)
  intro t ht
  have hz (x : Space) : F (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := F)
    intro htx
    exact ht ⟨(t, x), htx, rfl⟩
  simp [hz, hn]

 theorem uniform_integral_norm_pow_time {F : ℝ × Space → ℂ}
    (hF : Continuous F) (hc : HasCompactSupport F) (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, (∫ x : Space, ‖F (t, x)‖ ^ n) ≤ C := by
  obtain ⟨C, hC⟩ := (compact_integral_norm_pow_time hc n hn).exists_bound_of_continuous
    (continuous_integral_norm_pow_time hF hc n hn)
  refine ⟨C, (norm_nonneg _).trans (hC 0), ?_⟩
  intro t
  exact (le_abs_self _).trans (hC t)

/-- Parseval identifies the zero-order Fourier time norm with the physical L²
norm, making its continuity a compact parameter-integral theorem. -/
theorem continuous_fourierSobolev_zero_time {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (fun t => NSFormalization.Source.fourierSobolevNorm 0 (fun x => F (t, x))) := by
  have heq (t : ℝ) : NSFormalization.Source.fourierSobolevNorm 0 (fun x => F (t, x)) =
      Real.sqrt (∫ x : Space, ‖F (t, x)‖ ^ 2) := by
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
      (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
    have h := SchwartzMap.integral_norm_sq_fourier φ
    unfold NSFormalization.Source.fourierSobolevNorm NSFormalization.Source.fourierSobolevSq
    simp only [Real.rpow_zero, one_mul]
    congr 1
  simpa only [heq, Function.comp_def] using Real.continuous_sqrt.comp
    (continuous_integral_norm_pow_time hF.continuous hc 2 (by norm_num))

/-- Every nonpositive inhomogeneous Fourier Sobolev time norm of a compact
smooth spacetime force lies in every `L^q`, including both paper exponents. -/
theorem memLp_fourierSobolev_nonpositive_time {s : ℝ} (hs : s ≤ 0)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))) q volume := by
  have hzero : MemLp (fun t => NSFormalization.Source.fourierSobolevNorm 0 (fun x => F (t, x))) q volume :=
    (continuous_fourierSobolev_zero_time hF hc).memLp_of_hasCompactSupport (compact_fourierSobolev_time 0 hc)
  apply hzero.mono' (stronglyMeasurable_fourierSobolev_time s hF.continuous).aestronglyMeasurable
  filter_upwards [] with t
  unfold NSFormalization.Source.fourierSobolevNorm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact integral_besselIntegrand_mono hs (compact_spacetime_fourier_slice_continuous hF hc t)
    (compact_spacetime_bessel_slices 0 hF hc t)

end NSFormalization.Paper3
