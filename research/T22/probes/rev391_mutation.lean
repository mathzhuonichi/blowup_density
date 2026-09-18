import NSFormalization.Section3.T22.CutoffKernel
noncomputable section
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff SchwartzMap
namespace Review391
theorem integrable_weighted_schwartz (s : ℝ) (ψ : SchwartzMap Space ℂ) :
    Integrable (fun ζ : Space => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * (‖ψ ζ‖ + 1)) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (|s| + 3)
  set C : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ with hC
  -- The polynomial tail is integrable because `finrank ℝ ℝ³ = 3 < k - |s|`.
  have hfr : (Module.finrank ℝ Space : ℝ) < (k : ℝ) - |s| := by
    have h3 : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [h3]; push_cast; linarith
  have hg : Integrable (fun ζ : Space => C * (1 + ‖ζ‖) ^ (-((k : ℝ) - |s|))) :=
    (integrable_one_add_norm hfr).const_mul C
  refine Integrable.mono' hg ?_ ?_
  · exact Continuous.aestronglyMeasurable
      ((Continuous.rpow_const (by fun_prop) (fun _ => Or.inl (by positivity))).mul (by fun_prop))
  · filter_upwards [] with ζ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    set b : ℝ := 1 + ‖ζ‖ with hb
    have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
    -- Weight comparison `(1+‖ζ‖²)^{|s|/2} ≤ (1+‖ζ‖)^{|s|}`.
    have hw : (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) ≤ b ^ |s| := by
      have hbase : (1 + ‖ζ‖ ^ 2) ≤ b ^ 2 := by rw [hb]; nlinarith [norm_nonneg ζ]
      calc (1 + ‖ζ‖ ^ 2) ^ (|s| / 2)
            ≤ (b ^ 2) ^ (|s| / 2) := Real.rpow_le_rpow (by positivity) hbase (by positivity)
        _ = b ^ |s| := by rw [← Real.rpow_natCast b 2, ← Real.rpow_mul hb0.le]; congr 1; ring
    -- Uniform Schwartz decay `(1+‖ζ‖)^k · ‖ψ ζ‖ ≤ C`.
    have hdecay : b ^ (k : ℕ) * ‖ψ ζ‖ ≤ C := by
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl ψ ζ
      rw [norm_iteratedFDeriv_zero] at h
      simpa [hb, hC] using h
    have hbk : (0 : ℝ) < b ^ (k : ℕ) := by positivity
    have hψbound : ‖ψ ζ‖ ≤ C * b ^ (-(k : ℝ)) := by
      rw [Real.rpow_neg hb0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hbk, mul_comm]
      exact hdecay
    have hcomb : b ^ |s| * (C * b ^ (-(k : ℝ))) = C * b ^ (-((k : ℝ) - |s|)) := by
      rw [show (-((k : ℝ) - |s|)) = |s| + -(k : ℝ) by ring, Real.rpow_add hb0]; ring
    calc (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖
          ≤ b ^ |s| * (C * b ^ (-(k : ℝ))) :=
            mul_le_mul hw hψbound (norm_nonneg _) (Real.rpow_nonneg hb0.le _)
      _ = C * b ^ (-((k : ℝ) - |s|)) := hcomb

end Review391
