import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer NEGATIVE check M1 for lane 149: weaken `T₀ < T` to `T₀ ≤ T` in
`kbnd_of_sup_bound_Icc`, keeping the lane's proof verbatim.  EXPECTED TO FAIL. -/

noncomputable section
namespace Rev149Mut1
open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerCylinderSobolev
open scoped ENNReal ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

set_option autoImplicit false in
theorem kbnd_of_sup_bound_Icc_MUT {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T))
    {T₀ : ℝ} (hT₀T : T₀ ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T₀,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T₀ := by
  have hRnn : 0 ≤ R := le_trans (norm_nonneg u) hR
  have hpt := sobolevNormAt_two_sq_le_of_sup u U hu hU hq v hslice hR
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t < T := lt_of_le_of_lt ht.2 hT₀T
  have hsub : uIcc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := by
    rw [uIcc_of_le ht0]
    exact fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩
  have hII : IntervalIntegrable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2) volume 0 t :=
    ((hcont.pow 2).mono hsub).intervalIntegrable
  have hle_pt : ∀ s ∈ Icc (0 : ℝ) t, sobolevNormAt (2 : ℝ) v s ^ 2 ≤ 256 * R ^ 2 := by
    intro s hs
    have hsT : s ≤ T := le_trans hs.2 htT.le
    have := hpt ⟨s, hs.1, hsT⟩
    simpa using this
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2)
      ≤ ∫ _s in (0 : ℝ)..t, (256 * R ^ 2) :=
        intervalIntegral.integral_mono_on ht0 hII intervalIntegrable_const hle_pt
    _ = t * (256 * R ^ 2) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ T₀ * (256 * R ^ 2) := by
        apply mul_le_mul_of_nonneg_right ht.2; positivity
    _ = 256 * R ^ 2 * T₀ := by ring

end Rev149Mut1
