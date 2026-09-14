import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer probe for lane 149, residual row (iii) at the endpoint `T₀ = T`: is the *cap* row
(as opposed to the Grönwall output) really out of reach at the closed endpoint?  The lane's
`kbnd_of_sup_bound_Icc` needs `T₀ < T` only to get interval-integrability out of `hcont`
(continuity on the half-open `Ico 0 T`).  The pointwise bound `sobolevNormAt_two_sq_le_of_sup` is
already unconditional on the **closed** `Icc 0 T`, so integrability at the endpoint follows from
a.e.-continuity + boundedness. -/

noncomputable section
namespace Rev149Endpoint
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
/-- The `T₀ = T` case of the cap, same constant `256·R²·T`, same hypotheses as the lane's
`kbnd_of_sup_bound_Icc` (with `T₀ := T`, so `hT₀T : T₀ < T` is dropped). -/
theorem kbnd_of_sup_bound_Icc_endpoint {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T := by
  have hRnn : 0 ≤ R := le_trans (norm_nonneg u) hR
  have hpt := sobolevNormAt_two_sq_le_of_sup u U hu hU hq v hslice hR
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hle_pt : ∀ s ∈ Icc (0 : ℝ) t, sobolevNormAt (2 : ℝ) v s ^ 2 ≤ 256 * R ^ 2 := by
    intro s hs
    have := hpt ⟨s, hs.1, le_trans hs.2 htT⟩
    simpa using this
  -- integrability at the closed endpoint: continuity on `Ioo 0 t` (⊆ `Ico 0 T`) plus the
  -- unconditional pointwise bound on the closed window
  have hmeas : AEStronglyMeasurable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2)
      (volume.restrict (Ioc (0 : ℝ) t)) := by
    have hsub : Ioo (0 : ℝ) t ⊆ Ico (0 : ℝ) T := fun s hs => ⟨hs.1.le, lt_of_lt_of_le hs.2 htT⟩
    have h1 : AEStronglyMeasurable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2)
        (volume.restrict (Ioo (0 : ℝ) t)) :=
      ((hcont.pow 2).mono hsub).aestronglyMeasurable measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have hII : IntervalIntegrable (fun s => sobolevNormAt (2 : ℝ) v s ^ 2) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    refine Integrable.mono' (g := fun _ : ℝ => 256 * R ^ 2)
      (integrableOn_const (by simp)) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have h0 : 0 ≤ sobolevNormAt (2 : ℝ) v s ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact hle_pt s ⟨hs.1.le, hs.2⟩
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2)
      ≤ ∫ _s in (0 : ℝ)..t, (256 * R ^ 2) :=
        intervalIntegral.integral_mono_on ht0 hII intervalIntegrable_const hle_pt
    _ = t * (256 * R ^ 2) := by rw [intervalIntegral.integral_const]; ring
    _ ≤ T * (256 * R ^ 2) := by apply mul_le_mul_of_nonneg_right htT; positivity
    _ = 256 * R ^ 2 * T := by ring

end Rev149Endpoint
