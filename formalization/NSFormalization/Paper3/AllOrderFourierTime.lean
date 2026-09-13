import NSFormalization.Paper3.PositiveFourierTime

/-! All real-order actual Fourier time norms of compact smooth spacetime inputs. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NavierStokesR3.HarmonicTestFunctionals
open scoped ContDiff ENNReal

/-- The actual Bessel energy at the next order is controlled by the current
energy and the energies of the physical coordinate derivatives. -/
theorem bessel_succ_energy_le (s : ℝ) (φ : SchwartzMap Space ℂ) :
    (∫ ξ : Space, besselIntegrand (s + 1) (𝓕 φ : SchwartzMap Space ℂ) ξ) ≤
      (∫ ξ : Space, besselIntegrand s (𝓕 φ : SchwartzMap Space ℂ) ξ) +
        ∑ i : Fin 3, ∫ ξ : Space, besselIntegrand s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ) ξ := by
  have hp (ξ : Space) : besselIntegrand (s + 1) (𝓕 φ : SchwartzMap Space ℂ) ξ ≤
      besselIntegrand s (𝓕 φ : SchwartzMap Space ℂ) ξ + ∑ i : Fin 3, besselIntegrand s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ) ξ := by
    have hn : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
    have hbase : (1 + ‖ξ‖ ^ 2) * ‖𝓕 φ ξ‖ ^ 2 ≤
        ‖𝓕 φ ξ‖ ^ 2 + ∑ i : Fin 3, ‖𝓕 (partialCLM i φ) ξ‖ ^ 2 := by
      simp [hn, Fin.sum_univ_succ]
      nlinarith [fourier_coordinate_sq_le φ ξ 0, fourier_coordinate_sq_le φ ξ 1,
        fourier_coordinate_sq_le φ ξ 2]
    have hm := mul_le_mul_of_nonneg_left hbase
      (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2) s)
    rw [mul_add, Finset.mul_sum] at hm
    simpa only [besselIntegrand, Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2),
      Real.rpow_one, mul_assoc] using hm
  have h := integral_mono (schwartz_bessel_integrable (s + 1) (𝓕 φ : SchwartzMap Space ℂ))
    ((schwartz_bessel_integrable s (𝓕 φ : SchwartzMap Space ℂ)).add (integrable_finsetSum _
      (fun i _ => schwartz_bessel_integrable s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ)))) hp
  change (∫ ξ : Space, besselIntegrand (s + 1) (𝓕 φ : SchwartzMap Space ℂ) ξ) ≤
    ∫ ξ : Space, besselIntegrand s (𝓕 φ : SchwartzMap Space ℂ) ξ + ∑ i : Fin 3, besselIntegrand s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ) ξ at h
  rw [integral_add (schwartz_bessel_integrable s (𝓕 φ : SchwartzMap Space ℂ))
    (integrable_finsetSum _ (fun i _ => schwartz_bessel_integrable s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ))),
    integral_finsetSum _ (fun i _ => schwartz_bessel_integrable s (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ))] at h
  exact h

/-- A compact smooth spacetime input has uniformly bounded actual Fourier
energy at every nonnegative integer order. -/
theorem uniform_bessel_nat_time (n : ℕ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ C : ℝ, ∀ t, (∫ ξ : Space, besselIntegrand (n : ℝ) (𝓕 (fun x => F (t, x))) ξ) ≤ C := by
  induction n generalizing F with
  | zero =>
    obtain ⟨C, _, hC⟩ := uniform_integral_norm_pow_time hF.continuous hc 2 (by norm_num)
    refine ⟨C, fun t => ?_⟩
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
      (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
    have hp : (∫ ξ : Space, ‖𝓕 (fun x => F (t, x)) ξ‖ ^ 2) = ∫ x : Space, ‖F (t, x)‖ ^ 2 :=
      SchwartzMap.integral_norm_sq_fourier φ
    simpa only [Nat.cast_zero, besselIntegrand, Real.rpow_zero, one_mul, hp] using hC t
  | succ n ih =>
    obtain ⟨C₀, h₀⟩ := ih hF hc
    have hd (i : Fin 3) := ih (spacetimePartial_smooth hF i) (spacetimePartial_compact hc i)
    choose C hC using hd
    refine ⟨C₀ + ∑ i, C i, fun t => ?_⟩
    let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x))
      (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t)
    have heq (i : Fin 3) : (partialCLM i φ : Space → ℂ) = (fun x => spacetimePartial i F (t, x)) := by
      funext x
      exact (spacetimePartial_eq_slice hF i t x).symm
    have hsum : (∫ ξ : Space, besselIntegrand (n : ℝ) (𝓕 φ : SchwartzMap Space ℂ) ξ) +
        ∑ i : Fin 3, ∫ ξ : Space, besselIntegrand (n : ℝ) (𝓕 (partialCLM i φ) : SchwartzMap Space ℂ) ξ ≤
        C₀ + ∑ i, C i := by
      apply add_le_add (h₀ t)
      apply Finset.sum_le_sum
      intro i _
      change (∫ ξ : Space, besselIntegrand (n : ℝ) (𝓕 (partialCLM i φ : Space → ℂ)) ξ) ≤ C i
      rw [heq]
      exact hC i t
    simpa only [Nat.cast_add, Nat.cast_one, SchwartzMap.fourier_coe, φ,
      NavierStokesR3.CompactSchwartz.coe_ofCompactSupport] using (bessel_succ_energy_le (n : ℝ) φ).trans hsum

/-- Actual inhomogeneous Fourier norms at every real order are uniformly
bounded in time for compact smooth spacetime inputs. -/
theorem uniform_fourierSobolev_time (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ C : ℝ, ∀ t, ‖NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))‖ ≤ C := by
  obtain ⟨n, hn⟩ := exists_nat_ge s
  obtain ⟨C, hC⟩ := uniform_bessel_nat_time n hF hc
  refine ⟨Real.sqrt C, fun t => ?_⟩
  unfold NSFormalization.Source.fourierSobolevNorm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  exact (integral_besselIntegrand_mono hn
    (compact_spacetime_fourier_slice_continuous hF hc t)
    (compact_spacetime_bessel_slices (n : ℝ) hF hc t)).trans (hC t)

/-- Every real-order actual inhomogeneous Fourier norm of a compact smooth
spacetime input belongs to every time `L^q`, including both manuscript exponents. -/
theorem memLp_fourierSobolev_time (s : ℝ) {F : ℝ × Space → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))) q volume := by
  obtain ⟨C, hC⟩ := uniform_fourierSobolev_time s hF hc
  exact (compact_fourierSobolev_time s hc).memLp_of_bound
    (stronglyMeasurable_fourierSobolev_time s hF.continuous).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end NSFormalization.Paper3
