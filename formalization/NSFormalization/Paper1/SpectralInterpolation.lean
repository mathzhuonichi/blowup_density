import Mathlib.Analysis.MeanInequalities

/-! An adapter of Mathlib's proved infinite-sum Hölder inequality to spectral
weights. It applies to actual summable nonnegative Fourier energies. -/
noncomputable section
namespace NSFormalization.Paper1

 theorem summable_spectral_interpolation {ι : Type*} {a w : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i)
    (hA : Summable a) (hB : Summable (fun i => w i * a i))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (fun i => w i ^ s * a i) ∧
      (∑' i, w i ^ s * a i) ≤ (∑' i, a i) ^ (1 - s) * (∑' i, w i * a i) ^ s := by
  have hp : (1 - s)⁻¹.HolderConjugate s⁻¹ := Real.HolderConjugate.one_sub_inv_inv hs0 hs1
  have hleft (i : ι) : (a i ^ (1 - s)) ^ (1 - s)⁻¹ = a i := by
    rw [← Real.rpow_mul (ha i), mul_inv_cancel₀ (by linarith : 1 - s ≠ 0), Real.rpow_one]
  have hright (i : ι) : ((w i * a i) ^ s) ^ s⁻¹ = w i * a i := by
    rw [← Real.rpow_mul (mul_nonneg (hw i) (ha i)), mul_inv_cancel₀ hs0.ne', Real.rpow_one]
  have hprod (i : ι) : a i ^ (1 - s) * (w i * a i) ^ s = w i ^ s * a i := by
    rw [Real.mul_rpow (hw i) (ha i)]
    calc
      a i ^ (1 - s) * (w i ^ s * a i ^ s) = w i ^ s * (a i ^ (1 - s) * a i ^ s) := by ring
      _ = w i ^ s * a i := by
        rw [← Real.rpow_add' (ha i) (by ring_nf; norm_num : 1 - s + s ≠ 0)]
        simp
  have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hp
    (fun i => Real.rpow_nonneg (ha i) (1 - s))
    (fun i => Real.rpow_nonneg (mul_nonneg (hw i) (ha i)) s)
    (by simpa only [hleft] using hA) (by simpa only [hright] using hB)
  simpa only [hprod, hleft, hright, one_div, inv_inv] using hh

end NSFormalization.Paper1
