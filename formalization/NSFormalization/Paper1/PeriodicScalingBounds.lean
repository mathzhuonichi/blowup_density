import NSFormalization.Paper1.PeriodicSobolevHilbert

/-!
# Endpoint interpolation interface for periodic insertion estimates

The concrete packet and correction modules supply the endpoint L² and H¹
identities. This file records the exact spectral interpolation consequence
used when those identities are instantiated; the general fractional
localization lemma remains a separate manuscript obligation.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicScalingBounds
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators

/-- H⁰--H¹ interpolation for a periodic field, with endpoint energies supplied
by explicit hypotheses. Keeping these equalities as premises prevents an
unproved localization argument from being hidden in the interpolation step. -/
theorem periodic_interpolation_of_endpoint_energies
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    {A B : ℝ} (hA : cubeIntegral (fun x => ‖f x‖ ^ 2) = A)
    (hB : periodicH1Energy f = B) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    periodicSobolevNorm s f ≤ (Real.sqrt A) ^ (1 - s) * (Real.sqrt B) ^ s := by
  have hA0 : 0 ≤ A := by
    rw [← hA]
    exact cubeIntegral_nonneg (fun x => sq_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [← hB]
    unfold periodicH1Energy
    exact add_nonneg (cubeIntegral_nonneg (fun x => sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => cubeIntegral_nonneg (fun x => sq_nonneg _)))
  have h := periodicSobolevNorm_interpolation hf hp hs0 hs1
  rw [hA, hB] at h
  exact h

/- A monotone version suited to estimates: upper bounds for the physical
endpoint energies imply the corresponding bound for every real order between
zero and one. -/
theorem periodic_interpolation_of_endpoint_bounds
    {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (hp : UnitPeriods f)
    {A B : ℝ} (hA : cubeIntegral (fun x => ‖f x‖ ^ 2) ≤ A ^ 2)
    (hB : periodicH1Energy f ≤ B ^ 2) {s : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    periodicSobolevNorm s f ≤ A ^ (1 - s) * B ^ s := by
  have h := periodicSobolevSq_interpolation hf hp hs0 hs1
  have hnonA : 0 ≤ cubeIntegral (fun x => ‖f x‖ ^ 2) :=
    cubeIntegral_nonneg (fun x => sq_nonneg _)
  have hnonB : 0 ≤ periodicH1Energy f := by
    unfold periodicH1Energy
    exact add_nonneg (cubeIntegral_nonneg (fun x => sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => cubeIntegral_nonneg (fun x => sq_nonneg _)))
  have hAroot : Real.sqrt (cubeIntegral (fun x => ‖f x‖ ^ 2)) ≤ A := by
    rw [Real.sqrt_le_iff]
    exact ⟨hA0, hA⟩
  have hBroot : Real.sqrt (periodicH1Energy f) ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨hB0, hB⟩
  have hpowA : (Real.sqrt (cubeIntegral (fun x => ‖f x‖ ^ 2))) ^ (1 - s) ≤
      A ^ (1 - s) := Real.rpow_le_rpow (Real.sqrt_nonneg _) hAroot
        (by linarith)
  have hpowB : (Real.sqrt (periodicH1Energy f)) ^ s ≤ B ^ s :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hBroot hs0
  have hbase := periodicSobolevNorm_interpolation hf hp hs0 hs1
  exact hbase.trans (mul_le_mul hpowA hpowB
    (Real.rpow_nonneg (Real.sqrt_nonneg _) s)
    (Real.rpow_nonneg hA0 (1 - s)))

end NSFormalization.Paper1.PeriodicScalingBounds
