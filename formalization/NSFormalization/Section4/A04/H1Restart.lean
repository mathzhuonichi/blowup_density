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

/-- Squared registered norms are continuous up to the initial endpoint. -/
theorem continuousOn_sobolevEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (m : ℕ) :
    ContinuousOn (fun t => (sobolevENorm (m : ℝ) (C01.slice w.velocity t)).toReal ^ 2)
      (Ico (0 : ℝ) T) :=
  (continuousOn_sobolevNormAt_velocity w m).pow 2

/-- The H¹ energy is differentiable at every strictly interior time. -/
theorem differentiableAt_hOneEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    DifferentiableAt ℝ
      (fun q => (sobolevENorm 1 (C01.slice w.velocity q)).toReal ^ 2) t := by
  apply (inhomogeneousEnergyIdentity w hf ht).differentiableAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with q hq
  exact sobolevEnergy_one_smooth (velocitySliceField w (Ioo_subset_Ico_self hq))

/-- Every integer-order norm is finite on a classical slice. -/
theorem sobolevENorm_slice_ne_top {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    sobolevENorm (m : ℝ) (C01.slice w.velocity t) ≠ ⊤ := by
  obtain ⟨G, _, hG⟩ := w.sobolev m
  have he := A03.sobolevENorm_eq (hG t ht)
  change sobolevENorm (m : ℝ) (C01.slice w.velocity t) = ‖G t‖ₑ at he
  rw [he]
  exact enorm_ne_top

/-- Classical compact-interval dissipation is the nonnegative integral of its real energy. -/
theorem hTwo_lintegral_eq {ν T s : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hs0 : 0 ≤ s) (hsT : s < T) :
    (∫⁻ t in Ico (0 : ℝ) s, sobolevENorm 2 (C01.slice w.velocity t) ^ 2) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..s,
        (sobolevENorm 2 (C01.slice w.velocity t)).toReal ^ 2) := by
  have hi : IntegrableOn (fun t => (sobolevENorm 2 (C01.slice w.velocity t)).toReal ^ 2)
      (Icc (0 : ℝ) s) := ((continuousOn_sobolevEnergy w 2).mono
    (show Icc (0 : ℝ) s ⊆ Ico 0 T from fun t ht => ⟨ht.1, ht.2.trans_lt hsT⟩)).integrableOn_Icc
  rw [intervalIntegral.integral_of_le hs0, ← integral_Ico_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hi.mono_set Ico_subset_Icc_self)
      (ae_of_all _ (fun t => sq_nonneg _))]
  apply setLIntegral_congr_fun measurableSet_Ico
  intro t ht
  dsimp only
  have hne : sobolevENorm 2 (C01.slice w.velocity t) ≠ ⊤ :=
    sobolevENorm_slice_ne_top w 2 ⟨ht.1, ht.2.trans hsT⟩
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]

/-- A single window and dissipation bound precede both restart time and datum. -/
theorem uniform_hTwo_running_bound (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : MemForceR f) (S : ℝ) (hS : 0 ≤ S)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ d > 0, d ≤ 1 ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a : SpatialField, sobolevENorm 1 a ≤ K →
      ∀ T : ℝ, ∀ w : ClassicalSolutionR ν a (timeShift t₀ f) T,
      ∀ s : ℝ, 0 ≤ s → s < T → s ≤ d →
        (∫⁻ t in Ico (0 : ℝ) s, sobolevENorm 2 (C01.slice w.velocity t) ^ 2) ≤
          ENNReal.ofReal B := by
  have hC : 0 < h1RestartConstant ν := by unfold h1RestartConstant; positivity
  obtain ⟨d, hd, M, hM, hb⟩ := enstrophy_uniform_barrier_and_dissipation hν hC
    (sq_nonneg K.toReal) (sq_nonneg (forceL2CapR f S).toReal)
  let D := min d 1
  let B := (K.toReal ^ 2 + h1RestartConstant ν * (1 + M) ^ 3 * D +
    h1RestartConstant ν * (forceL2CapR f S).toReal ^ 2 * D) / ν
  have hD : 0 < D := lt_min hd zero_lt_one
  have hM0 : 0 ≤ M := by rw [hM]; nlinarith [sq_nonneg K.toReal]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D, hD, min_le_right _ _, B, hB, ?_⟩
  intro t₀ ht₀ a ha T w s hs0 hsT hsD
  let Y := fun t => (sobolevENorm 1 (C01.slice w.velocity t)).toReal ^ 2
  let Z := fun t => (sobolevENorm 2 (C01.slice w.velocity t)).toReal ^ 2
  have hf' := restart_force f hf t₀ ht₀.1
  have hsub : Icc (0 : ℝ) s ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hsT⟩
  have hcY : ContinuousOn Y (Icc (0 : ℝ) s) := by
    convert (continuousOn_sobolevEnergy w 1).mono hsub using 1; norm_num [Y]
  have hcZ : ContinuousOn Z (Icc (0 : ℝ) s) := by
    convert (continuousOn_sobolevEnergy w 2).mono hsub using 1; norm_num [Z]
  have hinit : Y 0 ≤ K.toReal ^ 2 := by
    have he : C01.slice w.velocity 0 = a := funext w.initial
    dsimp [Y]
    rw [he]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hK ha) 2
  have hdY : ∀ t ∈ Ioo (0 : ℝ) s, DifferentiableAt ℝ Y t :=
    fun t ht => differentiableAt_hOneEnergy w hf' ⟨ht.1, ht.2.trans hsT⟩
  have hineq : ∀ t ∈ Ioo (0 : ℝ) s,
      deriv Y t + ν * Z t ≤ h1RestartConstant ν * (1 + Y t) ^ 3 +
        h1RestartConstant ν * (forceL2CapR f S).toReal ^ 2 := by
    intro t ht
    have he := enstrophy_differential_on_Icc' w hf' hν ht.1 hsT t ⟨le_rfl, ht.2.le⟩
    exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (timeShift_force_l2Sq_le hf hS ht₀
        ⟨ht.1.le, ht.2.le.trans (hsD.trans (min_le_right _ _))⟩) hC.le))
  have hh := hb 0 s Y Z hs0 (hsD.trans (min_le_left _ _))
    (by simpa only [zero_add] using hcY)
    (by simpa only [zero_add] using hdY)
    (fun t _ => sq_nonneg _) hinit (fun t _ => sq_nonneg _)
    (by simpa only [zero_add] using hcZ.integrableOn_Icc (μ := volume))
    (by simpa only [zero_add] using hineq)
  have hreal : (∫ t in (0 : ℝ)..s, Z t) ≤ B := by
    have hh' : (∫ t in (0 : ℝ)..s, Z t) ≤
        (K.toReal ^ 2 + h1RestartConstant ν * (1 + M) ^ 3 * s +
          h1RestartConstant ν * (forceL2CapR f S).toReal ^ 2 * s) / ν := by
      simpa only [zero_add] using hh.2
    apply hh'.trans
    dsimp [B]
    gcongr
  rw [hTwo_lintegral_eq w hs0 hsT]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Pass the uniform bound through every shorter classical horizon to the endpoint. -/
theorem uniform_hTwo_endpoint_bound (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : MemForceR f) (S : ℝ) (hS : 0 ≤ S)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ d > 0, ∃ B : ℝ, 0 ≤ B ∧
      ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a : SpatialField, sobolevENorm 1 a ≤ K →
      ∀ R : ℝ, 0 < R → R ≤ d → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a (timeShift t₀ f) R u p → squaredHTwoIntegral R u ≤ ENNReal.ofReal B := by
  obtain ⟨d, hd, _, B, hB, hb⟩ := uniform_hTwo_running_bound ν hν f hf S hS K hK
  refine ⟨d, hd, B, hB, ?_⟩
  intro t₀ ht₀ a ha R hR hRd u p hu
  have heq (s : ℝ) (hs : s ≤ R) :
      (∫⁻ t in Ico (0 : ℝ) s, sobolevENorm 2 (C01.slice u t) ^ 2) =
        ∫⁻ t in Ico (0 : ℝ) s, ENNReal.ofReal ((sobolevENorm 2 (C01.slice u t)).toReal ^ 2) := by
    apply setLIntegral_congr_fun measurableSet_Ico
    intro t ht
    dsimp only
    obtain ⟨w, hw, _⟩ := hu ((t + R) / 2) (by linarith [ht.1])
      (by linarith [ht.2])
    have hne : sobolevENorm 2 (C01.slice u t) ≠ ⊤ := by
      rw [← hw]
      exact sobolevENorm_slice_ne_top w 2 ⟨ht.1, by linarith [ht.2]⟩
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne]
  have he : (∫⁻ t in Ico (0 : ℝ) R, sobolevENorm 2 (C01.slice u t) ^ 2) ≤
      ENNReal.ofReal B := by
    rw [heq R le_rfl]
    apply enstrophy_endpoint_lintegral
    intro s hs
    rw [← heq s hs.le]
    by_cases hs0 : 0 ≤ s
    · obtain ⟨w, hw, _⟩ := hu ((s + R) / 2) (by linarith) (by linarith)
      have h := hb t₀ ht₀ a ha _ w s hs0 (by linarith) (hs.le.trans hRd)
      simpa only [hw] using h
    · simp [Ico_eq_empty_of_le (le_of_not_ge hs0)]
  exact (lintegral_mono_set Ioo_subset_Ico_self).trans he

end NSFormalization.Section4.A04
