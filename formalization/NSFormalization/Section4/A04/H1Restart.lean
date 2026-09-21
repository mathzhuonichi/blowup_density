import NSFormalization.Section4.A04.H1BridgesSmooth
import NSFormalization.Section4.A04.EnstrophyInequality
import NSFormalization.Section4.A04.EnstrophyBarrier
import NSFormalization.Section4.A04.ShiftedExtension

/-!
# Uniform H¹ restart on R³

The revised article `02-preliminaries.tex:149–156` states: “For each initial
velocity in the stated class ... a unique maximal smooth velocity” and that
finite squared H² integral implies extension. This module addresses the separate
registered H¹-uniform restart target recorded in `research/P21/Targets.lean`.
The angular convention requires κ=1 in B1's parameterized estimate.
-/
noncomputable section
namespace NSFormalization.Section4.A04
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 NSFormalization.Section4.C01
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ENNReal

/-- The constant in the angular-convention enstrophy estimate. -/
def h1RestartConstant (ν : ℝ) : ℝ :=
  (2 * A05.gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (ν / 2) ^ 3 +
    (1 + ν) + (1 + 2 / ν)

/-- B1's differential inequality with all norm bridges discharged. -/
theorem enstrophy_differential_on_Icc'
    {ν T r s : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hν : 0 < ν) (hr : 0 < r) (hs : s < T) :
    ∀ t ∈ Icc r s,
      deriv (fun q => (sobolevENorm 1 (slice w.velocity q)).toReal ^ 2) t +
        ν * (sobolevENorm 2 (slice w.velocity t)).toReal ^ 2 ≤
      h1RestartConstant ν * (1 + (sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 +
        h1RestartConstant ν * l2Sq (slice f t) := by
  intro t ht
  have ht' : t ∈ Ioo (0 : ℝ) T := ⟨hr.trans_le ht.1, ht.2.trans_lt hs⟩
  have hOne : ∀ q ∈ Ioo (0 : ℝ) T,
      (sobolevENorm 1 (C01.slice w.velocity q)).toReal ^ 2 =
        l2Sq (C01.slice w.velocity q) + (1 : ℝ) * gradientSq (C01.slice w.velocity q) := by
    intro q hq
    convert sobolevEnergy_one_smooth (velocitySliceField w (Ioo_subset_Ico_self hq)) using 1 <;> first | rfl | (simp only [one_mul]; rfl)
  have hTwo : (sobolevENorm 2 (C01.slice w.velocity t)).toReal ^ 2 ≤
      l2Sq (C01.slice w.velocity t) + 2 * (1 : ℝ) * gradientSq (C01.slice w.velocity t) +
        (1 : ℝ) ^ 2 * laplacianSq (C01.slice w.velocity t) := by
    convert (sobolevEnergy_two_smooth (velocitySliceField w (Ioo_subset_Ico_self ht'))).le using 1 <;> first | rfl | (simp only [one_mul, mul_one, one_pow]; rfl)
  have h := enstrophy_differential_of_norm_bridges (κ := 1) w hf hν
    zero_lt_one le_rfl hOne ht' hTwo
    (eLpNorm_gradTensor_eq_sqrt (velocitySliceField w (Ioo_subset_Ico_self ht'))).le
  simp only [mul_one, one_mul, one_pow, div_one] at h
  have hA : 0 ≤ (2 * A05.gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 / (ν / 2) ^ 3 +
      (1 + ν) := by positivity
  have hB : 0 ≤ 1 + 2 / ν := by positivity
  have hF := l2Sq_nonneg (slice f t)
  have hY : 0 ≤ (1 + (sobolevENorm 1 (slice w.velocity t)).toReal ^ 2) ^ 3 := by positivity
  dsimp [h1RestartConstant]
  nlinarith [mul_nonneg hA hF, mul_nonneg hB hY]

/-- The fixed force cap controls squared physical force energy on every unit restart window. -/
theorem timeShift_force_l2Sq_le {f : SpaceTimeField} (hf : MemForceR f)
    {S t₀ t : ℝ} (hS : 0 ≤ S) (ht₀ : t₀ ∈ Icc (0 : ℝ) S)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    l2Sq (C01.slice (timeShift t₀ f) t) ≤ (forceL2CapR f S).toReal ^ 2 := by
  have h := ENNReal.toReal_mono (forceL2CapR_ne_top hf hS)
    (timeShift_force_slice_le_forceL2CapR (f := f) ht₀ ht)
  have he := eLpNorm_toReal_sq_eq_l2Sq
    (forceSliceField (restart_force f hf t₀ ht₀.1) ht.1)
  change (eLpNorm (C01.slice (timeShift t₀ f) t) 2 volume).toReal ^ 2 =
    l2Sq (C01.slice (timeShift t₀ f) t) at he
  rw [← he]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h 2

/-- Every classical solution has the full manuscript regularity bundle. -/
theorem classical_manuscriptLocalRegularity {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) : A01.ManuscriptLocalRegularity ν a f T w where
  sobolev_smooth := classical_hasSmoothSobolevPath hν hf w
  pressure_recovery := A01.pressure_recovery_of_classicalSolution w hf
  projected := A01.projected_of_classicalSolution w
  pressure_potential := A01.PressureGauge.pressure_potential_of_classicalSolution w

end NSFormalization.Section4.A04
