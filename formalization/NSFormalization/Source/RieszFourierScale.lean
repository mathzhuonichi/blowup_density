import NSFormalization.Source.RieszGaussianMixture

noncomputable section
namespace NSFormalization.Source.RieszFourierScale
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Source.RieszGaussianMixture

private theorem inverse_substitution (s c t : ℝ) (ht : 0 < t) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
      ((t ^ (-1 : ℝ)) ^ (s - 1) * Real.exp (-(c * t ^ (-1 : ℝ)))) =
      t ^ (-s - 1) * Real.exp (-c / t) := by
  rw [← Real.rpow_mul ht.le]
  simp only [abs_neg, abs_one, one_mul, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_add ht]
  congr 1
  · congr 1
    ring
  · rw [Real.rpow_neg_one]
    congr 1
    ring

/-- Genuine inverse-scale Gamma-moment integrability. -/
theorem inverse_scale_integrable {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-s - 1) * Real.exp (-c / t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := s - 1) (p := 1) (by linarith) (by norm_num) hc
  simp only [Real.rpow_one, neg_mul] at h
  have hi := (integrableOn_Ioi_comp_rpow_iff
    (fun u : ℝ => u ^ (s - 1) * Real.exp (-(c * u)))
    (p := -1) (by norm_num)).mpr (by simpa only [neg_mul] using h)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  exact inverse_substitution s c t ht

/-- Exact inverse-scale Gamma moment, before any Fourier interchange. -/
theorem integral_inverse_scale {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, t ^ (-s - 1) * Real.exp (-c / t)) =
      Real.Gamma s / c ^ s := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
        ((t ^ (-1 : ℝ)) ^ (s - 1) * Real.exp (-(c * t ^ (-1 : ℝ)))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (inverse_substitution s c t ht).symm
    _ = (1 / c) ^ s * Real.Gamma s :=
      (integral_comp_rpow_Ioi _ (p := -1) (by norm_num)).trans
        (Real.integral_rpow_mul_exp_neg_mul_Ioi hs hc)
    _ = _ := by rw [one_div, Real.inv_rpow hc.le]; ring
/-- Real Fourier-scale profile in the exact cycles-frequency convention. -/
def fourierProfile (a : ℝ) (ξ : Space) (t : ℝ) : ℝ :=
  scaleWeight a t * ((Real.pi / t) ^ (3 / 2 : ℝ) *
    Real.exp (-(Real.pi ^ 2) * ‖ξ‖ ^ 2 / t))

private theorem fourierProfile_eq (a : ℝ) (ξ : Space) {t : ℝ} (ht : 0 < t) :
    fourierProfile a ξ t =
      ((Real.Gamma ((3 - a) / 2))⁻¹ * Real.pi ^ (3 / 2 : ℝ)) *
        (t ^ (-(a / 2) - 1) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2) / t)) := by
  unfold fourierProfile scaleWeight
  rw [Real.div_rpow Real.pi_pos.le ht.le,
    div_eq_mul_inv (Real.pi ^ (3 / 2 : ℝ)), ← Real.rpow_neg ht.le]
  have he : t ^ ((3 - a) / 2 - 1) * t ^ (-(3 / 2 : ℝ)) =
      t ^ (-(a / 2) - 1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [neg_mul]
  calc
    _ = ((Real.Gamma ((3 - a) / 2))⁻¹ * Real.pi ^ (3 / 2 : ℝ)) *
        ((t ^ ((3 - a) / 2 - 1) * t ^ (-(3 / 2 : ℝ))) *
          Real.exp (-(Real.pi ^ 2) * ‖ξ‖ ^ 2 / t)) := by ring
    _ = _ := by rw [he, neg_mul]

/-- The scale integral of the Fourier profile is genuinely integrable off zero. -/
theorem fourierProfile_integrable {a : ℝ} (ha : 0 < a) {ξ : Space} (hξ : ξ ≠ 0) :
    IntegrableOn (fourierProfile a ξ) (Ioi 0) := by
  have hc : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos (norm_pos_iff.mpr hξ))
  have h := (inverse_scale_integrable (by linarith : 0 < a / 2) hc).const_mul
    ((Real.Gamma ((3 - a) / 2))⁻¹ * Real.pi ^ (3 / 2 : ℝ))
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  exact (fourierProfile_eq a ξ ht).symm

/-- Exact integral of the individual Fourier profiles, without exchanging the
infinite scale integral with a physical Fourier integral. -/
theorem integral_fourierProfile {a : ℝ} (ha : 0 < a) {ξ : Space} (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, fourierProfile a ξ t) =
      ((Real.Gamma ((3 - a) / 2))⁻¹ * Real.pi ^ (3 / 2 : ℝ)) *
        (Real.Gamma (a / 2) / (Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (a / 2)) := by
  have hc : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos (norm_pos_iff.mpr hξ))
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => fourierProfile_eq a ξ ht),
    integral_const_mul, integral_inverse_scale (by linarith : 0 < a / 2) hc]

/-- The actual individual-scale Fourier transforms are integrable in scale. -/
theorem fourier_scaleDensity_integrable {a : ℝ} (ha : 0 < a)
    {ξ : Space} (hξ : ξ ≠ 0) :
    IntegrableOn (fun t : ℝ => 𝓕 (scaleDensity a t) ξ) (Ioi 0) := by
  have h : IntegrableOn (fun t => (fourierProfile a ξ t : ℂ)) (Ioi 0) :=
    (fourierProfile_integrable ha hξ).ofReal
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [fourier_scaleDensity a ht]
  simp only [fourierProfile, Complex.ofReal_mul]

/-- Integral of actual individual-scale Fourier transforms, with exact Gamma
and pi factors. This is not a transform of the infinite physical mixture. -/
theorem integral_fourier_scaleDensity {a : ℝ} (ha : 0 < a)
    {ξ : Space} (hξ : ξ ≠ 0) :
    (∫ t : ℝ in Ioi 0, 𝓕 (scaleDensity a t) ξ) =
      ((((Real.Gamma ((3 - a) / 2))⁻¹ * Real.pi ^ (3 / 2 : ℝ)) *
        (Real.Gamma (a / 2) / (Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (a / 2)) : ℝ) : ℂ) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (fourierProfile a ξ t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [fourier_scaleDensity a ht]
      simp only [fourierProfile, Complex.ofReal_mul]
    _ = ((∫ t : ℝ in Ioi 0, fourierProfile a ξ t : ℝ) : ℂ) := by
      exact Complex.ofRealCLM.integral_comp_comm (fourierProfile_integrable ha hξ)
    _ = _ := congrArg Complex.ofReal (integral_fourierProfile ha hξ)

end NSFormalization.Source.RieszFourierScale

