import NSFormalization.Section3.T11.MildMomentum
import NSFormalization.Section3.T11.DuhamelHalfStep
import NSFormalization.Section3.T11.Restart

/-!
# T11 / U9d2c — the classical solution of a forced mild solution

This module closes the U9d target: from a forced mild solution
`TorusForcedMildOn C A P T u` on the torus it produces a genuine
`ClassicalSolutionT ν a g T` together with `PeriodicLocalRegularity` and the
identification of its order-three Fourier data with `u`.

The two residuals recorded by lanes 320/326/327 — the joint slab smoothness of
`torusPhysicalVelocity u` and of `mildPressure g u` — are proved here, by the
Banach-valued route: the order-`m` realizations of the mild solution form
`C^∞` paths into `PeriodicSobolev m` (each time derivative costs two Sobolev
orders, and persistence supplies every order), and the Fourier inversion is a
`C^j`-smooth map with values in the dual of `PeriodicSobolev m` once `m` is
large compared with `j`.
-/

noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section3.T10
open scoped BigOperators ContDiff ComplexConjugate ENNReal NNReal

local instance mildClassicalNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance mildClassicalNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace
-- Short-circuits an expensive instance search on the `lp`-based carrier.
local instance mildClassicalSecondCountableEither (s : ℝ) :
    SecondCountableTopologyEither ℝ (PeriodicSobolev s) :=
  ⟨Or.inl inferInstance⟩

/-! ## 0. The time derivative of a smooth space-time field -/

/-- The partial time derivative of a space-time field. -/
def timeDerivField (h : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ fderiv ℝ h z (1, 0)

/-- Smoothness is inherited by the partial time derivative. -/
theorem timeDerivField_contDiff {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (timeDerivField h) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (m := ∞) le_rfl
  exact hd.clm_apply contDiff_const

/-- At a fixed physical point the time slice differentiates to the field. -/
theorem timeDerivField_hasDerivAt {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h)
    (t : ℝ) (x : Space) :
    HasDerivAt (fun r : ℝ ↦ h (r, x)) (timeDerivField h (t, x)) t := by
  have hf : HasFDerivAt h (fderiv ℝ h (t, x)) (t, x) :=
    (hh.differentiable (by simp) (t, x)).hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ ↦ (r, x)) (1, 0) t := by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact hf.comp_hasDerivAt t hc

/-- Unit spatial periods pass to the partial time derivative. -/
theorem timeDerivField_periodic {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h)
    (hp : IsPeriodicOn univ h) : IsPeriodicOn univ (timeDerivField h) := by
  intro t _ x i
  have hshift : HasFDerivAt (fun z : SpaceTime ↦ (z.1, z.2 + coordinateVector i))
      (ContinuousLinearMap.id ℝ SpaceTime) (t, x) := by
    have h1 : HasFDerivAt (fun z : SpaceTime ↦ z.1)
        (ContinuousLinearMap.fst ℝ ℝ Space) (t, x) := hasFDerivAt_fst
    have h2 : HasFDerivAt (fun z : SpaceTime ↦ z.2 + coordinateVector i)
        (ContinuousLinearMap.snd ℝ ℝ Space) (t, x) :=
      hasFDerivAt_snd.add_const _
    simpa using h1.prodMk h2
  have hcomp : HasFDerivAt (fun z : SpaceTime ↦ h (z.1, z.2 + coordinateVector i))
      ((fderiv ℝ h (t, x + coordinateVector i)).comp (ContinuousLinearMap.id ℝ SpaceTime))
      (t, x) :=
    ((hh.differentiable (by simp) (t, x + coordinateVector i)).hasFDerivAt).comp (t, x) hshift
  have heq : (fun z : SpaceTime ↦ h (z.1, z.2 + coordinateVector i)) = h := by
    funext z
    exact hp z.1 (mem_univ _) z.2 i
  rw [heq] at hcomp
  have := hcomp.unique ((hh.differentiable (by simp) (t, x)).hasFDerivAt)
  change fderiv ℝ h (t, x + coordinateVector i) (1, 0) = fderiv ℝ h (t, x) (1, 0)
  rw [← this]
  rfl

/-! ## 1. The order-`m` datum path of a smooth periodic space-time field -/

/-- Differentiation under the cube integral: the Fourier coefficient of a time
slice of a smooth field differentiates to the coefficient of the time
derivative. -/
theorem periodicFourierCoeff_time_hasDerivAt {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h)
    (i : Fin 3) (k : PeriodicFrequency) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ periodicFourierCoeff (fun x ↦ ((h (r, x) i : ℝ) : ℂ)) k)
      (periodicFourierCoeff (fun x ↦ ((timeDerivField h (t, x) i : ℝ) : ℂ)) k) t := by
  classical
  set χ : Space → ℂ := NSFormalization.Paper1.periodicCharacter (-k) with hχ
  set F : ℝ → NavierStokes.PeriodicIntegration.Coords → ℂ := fun r y ↦
    χ (NavierStokes.PeriodicIntegration.toSpace y) *
      ((h (r, NavierStokes.PeriodicIntegration.toSpace y) i : ℝ) : ℂ) with hF
  set F' : ℝ → NavierStokes.PeriodicIntegration.Coords → ℂ := fun r y ↦
    χ (NavierStokes.PeriodicIntegration.toSpace y) *
      ((timeDerivField h (r, NavierStokes.PeriodicIntegration.toSpace y) i : ℝ) : ℂ) with hF'
  have hcoeff (r : ℝ) : periodicFourierCoeff (fun x ↦ ((h (r, x) i : ℝ) : ℂ)) k =
      ∫ y, F r y ∂NavierStokes.PeriodicIntegration.cubeMeasure := by
    exact NSFormalization.Paper1.periodicFourierCoeff_eq_cube _ _
  have hcoeff' (r : ℝ) :
      periodicFourierCoeff (fun x ↦ ((timeDerivField h (r, x) i : ℝ) : ℂ)) k =
      ∫ y, F' r y ∂NavierStokes.PeriodicIntegration.cubeMeasure := by
    exact NSFormalization.Paper1.periodicFourierCoeff_eq_cube _ _
  have hχc : Continuous χ := (NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous
  have hdt : ContDiff ℝ ∞ (timeDerivField h) := timeDerivField_contDiff hh
  have hFc (r : ℝ) : Continuous (fun x : Space ↦ χ x * ((h (r, x) i : ℝ) : ℂ)) :=
    hχc.mul (Complex.continuous_ofReal.comp
      (((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i)).comp
        (hh.continuous.comp (continuous_const.prodMk continuous_id))))
  have hF'c (r : ℝ) : Continuous (fun x : Space ↦ χ x * ((timeDerivField h (r, x) i : ℝ) : ℂ)) :=
    hχc.mul (Complex.continuous_ofReal.comp
      (((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i)).comp
        (hdt.continuous.comp (continuous_const.prodMk continuous_id))))
  -- a uniform bound for the derivative on a compact time window
  have hKc : IsCompact (Icc (t - 1) (t + 1) ×ˢ
      (NavierStokes.PeriodicIntegration.toSpace ''
        (Icc (0 : NavierStokes.PeriodicIntegration.Coords) 1))) :=
    isCompact_Icc.prod (isCompact_Icc.image
      NavierStokes.PeriodicIntegration.toSpace.continuous)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (hdt.continuous.continuousOn (s := Icc (t - 1) (t + 1) ×ˢ
      (NavierStokes.PeriodicIntegration.toSpace ''
        (Icc (0 : NavierStokes.PeriodicIntegration.Coords) 1))))
  have hballmem : Metric.ball t 1 ∈ nhds t := Metric.ball_mem_nhds t one_pos
  have hbound : ∀ᵐ y ∂NavierStokes.PeriodicIntegration.cubeMeasure,
      ∀ r ∈ Metric.ball t 1, ‖F' r y‖ ≤ M := by
    have hmem := MeasureTheory.ae_restrict_mem
      (μ := (volume : Measure NavierStokes.PeriodicIntegration.Coords))
      (s := NavierStokes.PeriodicIntegration.cube) measurableSet_Icc
    filter_upwards [hmem] with y hy r hr
    have hrmem : r ∈ Icc (t - 1) (t + 1) := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
      constructor <;> linarith [hr.1, hr.2]
    have hzmem : (r, NavierStokes.PeriodicIntegration.toSpace y) ∈
        Icc (t - 1) (t + 1) ×ˢ (NavierStokes.PeriodicIntegration.toSpace ''
          (Icc (0 : NavierStokes.PeriodicIntegration.Coords) 1)) :=
      ⟨hrmem, ⟨y, hy, rfl⟩⟩
    have hle := hM _ hzmem
    have hcomp : ‖(timeDerivField h (r, NavierStokes.PeriodicIntegration.toSpace y) i : ℝ)‖ ≤
        ‖timeDerivField h (r, NavierStokes.PeriodicIntegration.toSpace y)‖ :=
      PiLp.norm_apply_le _ i
    calc ‖F' r y‖ = ‖χ (NavierStokes.PeriodicIntegration.toSpace y)‖ *
          ‖((timeDerivField h (r, NavierStokes.PeriodicIntegration.toSpace y) i : ℝ) : ℂ)‖ :=
        norm_mul _ _
      _ ≤ 1 * M := by
        refine mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one
        · exact le_of_eq (torusCharacter_norm (-k) _)
        · exact le_trans (by simpa using hcomp) hle
      _ = M := one_mul M
  have hdiff : ∀ᵐ y ∂NavierStokes.PeriodicIntegration.cubeMeasure,
      ∀ r ∈ Metric.ball t 1, HasDerivAt (fun r : ℝ ↦ F r y) (F' r y) r := by
    filter_upwards with y r _
    exact ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
      (((EuclideanSpace.proj (𝕜 := ℝ) i)).hasFDerivAt.comp_hasDerivAt r
        (timeDerivField_hasDerivAt hh r
          (NavierStokes.PeriodicIntegration.toSpace y)))).const_mul
      (χ (NavierStokes.PeriodicIntegration.toSpace y)))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := NavierStokes.PeriodicIntegration.cubeMeasure) (bound := fun _ ↦ M)
    (F := F) (F' := F') (x₀ := t) (s := Metric.ball t 1) hballmem
    (Filter.Eventually.of_forall (fun r ↦
      ((hFc r).comp NavierStokes.PeriodicIntegration.toSpace.continuous).aestronglyMeasurable))
    (NavierStokes.PeriodicIntegration.integrable_cube (hFc t))
    ((hF'c t).comp
      NavierStokes.PeriodicIntegration.toSpace.continuous |>.aestronglyMeasurable)
    hbound (integrable_const M) hdiff
  simpa only [hcoeff, hcoeff'] using hmain.2

/-- The order-`m` datum path of a smooth periodic field differentiates to the
datum path of its time derivative. -/
theorem datumPath_hasDerivAt (m : ℕ) {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h)
    {G G' : ℝ → PeriodicSobolev (m : ℝ)}
    (hG : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ h (t, x)) (G t))
    (hG' : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ timeDerivField h (t, x)) (G' t))
    (t : ℝ) : HasDerivAt G (G' t) t := by
  have hcG' : Continuous G' :=
    continuous_datum_path m (timeDerivField_contDiff hh) G' hG'
  have hcoeff (i : Fin 3) (k : PeriodicFrequency) (r : ℝ) :
      HasDerivAt (fun q : ℝ ↦ (G q).1 i k) ((G' r).1 i k) r := by
    have hbase := periodicFourierCoeff_time_hasDerivAt hh i k r
    have := hbase.const_smul ((periodicFrequencyWeight k) ^ ((m : ℝ) / 2) : ℝ)
    have heq : (fun q : ℝ ↦ (G q).1 i k) =
        fun q : ℝ ↦ ((periodicFrequencyWeight k) ^ ((m : ℝ) / 2) : ℝ) •
          periodicFourierCoeff (fun x ↦ ((h (q, x) i : ℝ) : ℂ)) k := by
      funext q
      exact (hG q).2.2 i k
    rw [heq, (hG' r).2.2 i k]
    exact this
  have hint : ∀ b : ℝ, G b = G 0 + ∫ s in (0 : ℝ)..b, G' s := by
    intro b
    have hII : IntervalIntegrable G' volume 0 b := hcG'.intervalIntegrable 0 b
    apply torusDatum_ext
    intro i k
    have hr : (∫ s in (0 : ℝ)..b, G' s).1 i k = ∫ s in (0 : ℝ)..b, (G' s).1 i k :=
      torusCoeff_intervalIntegral hII i k
    have hscalar : (∫ s in (0 : ℝ)..b, (G' s).1 i k) = (G b).1 i k - (G 0).1 i k := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        exact hcoeff i k x
      · exact (((torusEvalCLM (m : ℝ) i k).continuous.comp hcG')).intervalIntegrable 0 b
    change (G b).1 i k = (G 0).1 i k + (∫ s in (0 : ℝ)..b, G' s).1 i k
    rw [hr, hscalar]
    ring
  have hFTC : HasDerivAt (fun b : ℝ ↦ G 0 + ∫ s in (0 : ℝ)..b, G' s) (G' t) t := by
    have hd := intervalIntegral.integral_hasDerivAt_right (f := G') (a := (0 : ℝ)) (b := t)
      (hcG'.intervalIntegrable 0 t)
      (hcG'.stronglyMeasurable.stronglyMeasurableAtFilter) hcG'.continuousAt
    exact hd.const_add _
  exact hFTC.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun b ↦ hint b))

/-- Every order-`m` datum path of a smooth unit-periodic space-time field is
`C^j` in time, for every finite order `j`. -/
theorem datumPath_contDiff_nat :
    ∀ (j m : ℕ) (h : SpaceTimeField), ContDiff ℝ ∞ h → IsPeriodicOn univ h →
      ∀ G : ℝ → PeriodicSobolev (m : ℝ),
        (∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ h (t, x)) (G t)) →
        ContDiff ℝ (j : ℕ) G := by
  intro j
  induction j with
  | zero =>
      intro m h hh _ G hG
      simpa only [Nat.cast_zero, contDiff_zero] using continuous_datum_path m hh G hG
  | succ j ih =>
      intro m h hh hp G hG
      have hdt : ContDiff ℝ ∞ (timeDerivField h) := timeDerivField_contDiff hh
      have hdp : IsPeriodicOn univ (timeDerivField h) := timeDerivField_periodic hh hp
      have hex : ∀ t : ℝ, ∃ A : PeriodicSobolev (m : ℝ),
          IsPeriodicDatum (m : ℝ) (fun x ↦ timeDerivField h (t, x)) A := by
        intro t
        exact smooth_periodic_datum (m : ℝ)
          (hdt.comp (contDiff_const.prodMk contDiff_id)) (hdp t (mem_univ t))
      choose G' hG' using hex
      have hderiv : ∀ t : ℝ, HasDerivAt G (G' t) t := datumPath_hasDerivAt m hh hG hG'
      have hdifferentiable : Differentiable ℝ G := fun t ↦ (hderiv t).differentiableAt
      have hderivEq : deriv G = G' := funext (fun t ↦ (hderiv t).deriv)
      have hG'c : ContDiff ℝ (j : ℕ) G' := ih m (timeDerivField h) hdt hdp G' hG'
      rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 by push_cast; ring]
      rw [contDiff_succ_iff_deriv]
      refine ⟨hdifferentiable, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · rw [hderivEq]
        exact hG'c

/-- Every order-`m` datum path of a smooth unit-periodic space-time field is
`C^∞` in time. -/
theorem datumPath_contDiff (m : ℕ) {h : SpaceTimeField} (hh : ContDiff ℝ ∞ h)
    (hp : IsPeriodicOn univ h) (G : ℝ → PeriodicSobolev (m : ℝ))
    (hG : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ h (t, x)) (G t)) :
    ContDiff ℝ ∞ G :=
  contDiff_infty.2 (fun j ↦ datumPath_contDiff_nat j m h hh hp G hG)

/-! ## 2. The tower of order-`m` realizations and its time derivative -/

theorem mildClassical_nat_ne_omega (j : ℕ) : ¬ ((j : ℕ∞ω) = ω) := by simp

theorem mildClassical_weight_pos (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight; positivity

theorem mildClassical_inv_eq_rpow (k : PeriodicFrequency) :
    (periodicFrequencyWeight k)⁻¹ = periodicFrequencyWeight k ^ (-1 : ℝ) := by
  rw [Real.rpow_neg (mildClassical_weight_pos k).le, Real.rpow_one]

theorem mildClassical_angular_div_le (ν : ℝ) (k : PeriodicFrequency) :
    |-(ν * periodicAngularFrequencySq k) / periodicFrequencyWeight k| ≤ |ν| := by
  have hw := mildClassical_weight_pos k
  have hang := periodicAngularFrequencySq_nonneg k
  have hle := periodicAngularFrequencySq_le k
  rw [abs_div, abs_neg, abs_mul, abs_of_pos hw, abs_of_nonneg hang,
    div_le_iff₀ hw]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg ν)

/-- The rescaled Laplace multiplier `−ν·4π²|k|²·W(k)⁻¹`, bounded by `|ν|`. -/
def mildLaplaceCLM (ν s r : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev r :=
  torusMultiplierCLM s r
    (fun k ↦ -(ν * periodicAngularFrequencySq k) / periodicFrequencyWeight k) |ν|
    (abs_nonneg ν) (mildClassical_angular_div_le ν)
    (fun k ↦ by
      have hang : periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
        simp [periodicAngularFrequencySq]
      rw [hang, torus_weight_neg])

theorem mildLaplaceCLM_coeff (ν s r : ℝ) (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    (mildLaplaceCLM ν s r A).1 i k =
      ((-(ν * periodicAngularFrequencySq k) / periodicFrequencyWeight k : ℝ) : ℂ) * A.1 i k :=
  rfl

theorem mildTower_le_add_two (m : ℕ) : (m : ℝ) ≤ (m : ℝ) + 2 := by linarith

theorem mildTower_three_le (m : ℕ) : (3 : ℝ) ≤ (m : ℝ) + 3 := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The candidate time derivative of the order-`m` realization:
`ν Δ` of the order-`(m+2)` realization plus the projected force minus the
projected convection of the order-`(m+3)` realization. -/
def mildTowerDeriv (ν : ℝ) (m : ℕ) (Pm : ℝ → PeriodicSobolev (m : ℝ))
    (w2 : ℝ → PeriodicSobolev ((m : ℝ) + 2))
    (w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)) (t : ℝ) : PeriodicSobolev (m : ℝ) :=
  mildLaplaceCLM ν ((m : ℝ) + 2) (m : ℝ) (w2 t) +
    (Pm t -
      persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
        (torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m) (w3 t) (w3 t)))

/-- The coefficients of the candidate derivative are the weighted coefficients of
lane 327's `mildDerivCoeff`. -/
theorem mildTowerDeriv_coeff {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3}
    (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (m : ℕ) {Pm : ℝ → PeriodicSobolev (m : ℝ)}
    {Fm : ℝ → PeriodicSobolev (m : ℝ)}
    (hFm : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) (Fm t))
    (hPm : ∀ t : ℝ, Pm t = torusLerayCLM (m : ℝ) (Fm t))
    {w2 : ℝ → PeriodicSobolev ((m : ℝ) + 2)}
    (hw2 : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 2) (u t) (w2 t))
    {w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)}
    (hw3 : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    (mildTowerDeriv ν m Pm w2 w3 t).1 i k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) * mildDerivCoeff C P u t i k := by
  have hw := mildClassical_weight_pos k
  have hlap : (mildLaplaceCLM ν ((m : ℝ) + 2) (m : ℝ) (w2 t)).1 i k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
          torusPhysicalCoeff 3 (u t) i k) := by
    rw [mildLaplaceCLM_coeff, hw2 t ht i k, torusPhysicalCoeff]
    simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [div_eq_mul_inv, mildClassical_inv_eq_rpow k]
    calc -(ν * periodicAngularFrequencySq k) *
          periodicFrequencyWeight k ^ (-1 : ℝ) *
          periodicFrequencyWeight k ^ (((m : ℝ) + 2 - 3) / 2)
        = -(ν * periodicAngularFrequencySq k) *
            (periodicFrequencyWeight k ^ (((m : ℝ) + 2 - 3) / 2) *
              periodicFrequencyWeight k ^ (-1 : ℝ)) := by ring
      _ = -(ν * periodicAngularFrequencySq k) *
            (periodicFrequencyWeight k ^ ((m : ℝ) / 2) *
              periodicFrequencyWeight k ^ (-3 / 2 : ℝ)) := by
            rw [← Real.rpow_add hw, ← Real.rpow_add hw]
            congr 2
            ring
      _ = periodicFrequencyWeight k ^ ((m : ℝ) / 2) * -(ν * periodicAngularFrequencySq k) *
            periodicFrequencyWeight k ^ (-3 / 2 : ℝ) := by ring
  have hforce : (Pm t).1 i k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        torusPhysicalCoeff 3 (P t) i k := by
    have hre : IsPeriodicReweight 3 (m : ℝ) (F t) (Fm t) :=
      persistence_reweight_of_data (hF t ht.1) (hFm t)
    rw [hPm t, torusLerayCLM_coeff, periodicLeray_reweight hre i k,
      ← (hPL t ht.1) i k, torusPhysicalCoeff]
    simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [← Real.rpow_add hw]
    congr 1
    ring
  have hconv : (persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
        (torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m) (w3 t) (w3 t))).1 i k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k := by
    have hdown : persistenceDown ((m : ℝ) + 3) 3 (mildTower_three_le m) (w3 t) = u t :=
      torusHalfStep_down_eq (mildTower_three_le m) hw3 ht
    have hstep := torusConvolutionCLM_real_coeff_transport ((m : ℝ) + 3)
      (mildTower_three_le m) (w3 t) (w3 t) i k
    rw [hdown] at hstep
    change ((periodicFrequencyWeight k ^ (((m : ℝ) - ((m : ℝ) + 2)) / 2) : ℝ) : ℂ) *
      (torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m) (w3 t) (w3 t)).1 i k = _
    rw [hstep, torusPhysicalCoeff, mildNonlinearDatum, C.bilinear_symbol]
    simp only [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [← Real.rpow_add hw, ← Real.rpow_add hw]
    congr 1
    ring
  change (mildLaplaceCLM ν ((m : ℝ) + 2) (m : ℝ) (w2 t)).1 i k +
    ((Pm t).1 i k - (persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
      (torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m) (w3 t) (w3 t))).1 i k) = _
  rw [hlap, hforce, hconv, mildDerivCoeff]
  ring

/-- Coefficients of an order-`m` realization in terms of the physical ones. -/
theorem mildTower_coeff {T : ℝ} {u : ℝ → PeriodicSobolev 3} (m : ℕ)
    {v : ℝ → PeriodicSobolev (m : ℝ)}
    (hv : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 (m : ℝ) (u t) (v t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    (v t).1 i k = ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      torusPhysicalCoeff 3 (u t) i k := by
  have hw := mildClassical_weight_pos k
  rw [hv t ht i k, torusPhysicalCoeff]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [← Real.rpow_add hw]
  congr 1
  ring

/-- Two order-`m` realizations of the same mild solution agree on the horizon. -/
theorem mildTower_unique {T : ℝ} {u : ℝ → PeriodicSobolev 3} (m : ℕ)
    {v w : ℝ → PeriodicSobolev (m : ℝ)}
    (hv : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 (m : ℝ) (u t) (v t))
    (hw : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 (m : ℝ) (u t) (w t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : v t = w t :=
  torusDatum_ext (fun i k ↦ by rw [hv t ht i k, hw t ht i k])

-- The induction carries eighteen data hypotheses and the `derivWithin` step
-- unfolds the order-`m` carrier; the default budget is not quite enough.
set_option maxHeartbeats 400000 in
/-- All-order time smoothness of every realization of a forced mild solution. -/
theorem mildTower_contDiffOn_nat {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T)) :
    ∀ (j m : ℕ) (v : ℝ → PeriodicSobolev (m : ℝ)),
      (∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 (m : ℝ) (u t) (v t)) →
      ContDiffOn ℝ (j : ℕ) v (Ico 0 T) := by
  classical
  have hper := persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu
  have hudiff : UniqueDiffOn ℝ (Ico (0 : ℝ) T) := uniqueDiffOn_Ico 0 T
  -- smooth order-`m` datum paths of the force
  have hFmex : ∀ m : ℕ, ∃ Fm : ℝ → PeriodicSobolev (m : ℝ),
      ContDiff ℝ ∞ Fm ∧
        ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) (Fm t) := by
    intro m
    have hex : ∀ t : ℝ, ∃ B : PeriodicSobolev (m : ℝ),
        IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) B := fun t ↦
      smooth_periodic_datum (m : ℝ) (hg.comp (contDiff_const.prodMk contDiff_id))
        (hgp t (mem_univ t))
    choose Fm hFm using hex
    exact ⟨Fm, datumPath_contDiff m hg hgp Fm hFm, hFm⟩
  intro j
  induction j with
  | zero =>
      intro m v hv
      obtain ⟨w, hwre, hwc, _⟩ := hper m
      have hcongr : ∀ t ∈ Ico (0 : ℝ) T, v t = w t := fun t ht ↦
        mildTower_unique m hv hwre ht
      simpa only [Nat.cast_zero, contDiffOn_zero] using hwc.congr hcongr
  | succ j ih =>
      intro m v hv
      obtain ⟨Fm, hFmsmooth, hFm⟩ := hFmex m
      obtain ⟨w2, hw2re, _, _⟩ := hper (m + 2)
      obtain ⟨w3, hw3re, _, _⟩ := hper (m + 3)
      have hw2re' : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 2) (u t) (w2 t) := by
        intro t ht i k
        have h := hw2re t ht i k
        push_cast at h
        exact h
      have hw3re' : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t) := by
        intro t ht i k
        have h := hw3re t ht i k
        push_cast at h
        exact h
      set Pm : ℝ → PeriodicSobolev (m : ℝ) := fun t ↦ torusLerayCLM (m : ℝ) (Fm t) with hPmdef
      set D : ℝ → PeriodicSobolev (m : ℝ) := mildTowerDeriv ν m Pm w2 w3 with hDdef
      clear_value D Pm
      -- the candidate derivative is `C^j`
      have hw2s : ContDiffOn ℝ (j : ℕ) w2 (Ico 0 T) := ih (m + 2) w2 hw2re
      have hw3s : ContDiffOn ℝ (j : ℕ) w3 (Ico 0 T) := ih (m + 3) w3 hw3re
      have hPms : ContDiffOn ℝ (j : ℕ) Pm (Ico 0 T) := by
        have : ContDiff ℝ ∞ Pm := by
          rw [hPmdef]; exact (torusLerayCLM (m : ℝ)).contDiff.comp hFmsmooth
        exact (this.of_le (by exact_mod_cast le_top)).contDiffOn
      have hbil : ContDiffOn ℝ (j : ℕ)
          (fun t ↦ torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m)
            (w3 t) (w3 t)) (Ico 0 T) := by
        have hleft : ContDiffOn ℝ (j : ℕ)
            (fun t ↦ torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m) (w3 t))
            (Ico 0 T) :=
          (torusConvolutionCLM_real ((m : ℝ) + 3) (mildTower_three_le m)).contDiff.comp_contDiffOn
            hw3s
        exact (isBoundedBilinearMap_apply.contDiff (n := (j : ℕ∞ω))).comp_contDiffOn
          (hleft.prodMk hw3s)
      have hD : ContDiffOn ℝ (j : ℕ) D (Ico 0 T) := by
        rw [hDdef]
        exact ((mildLaplaceCLM ν ((m : ℝ) + 2) (m : ℝ)).contDiff.comp_contDiffOn hw2s).add
          (hPms.sub ((persistenceDown ((m : ℝ) + 2) (m : ℝ)
            (mildTower_le_add_two m)).contDiff.comp_contDiffOn hbil))
      have hDcoeff : ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
          (D t).1 i k = ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
            mildDerivCoeff C P u t i k := by
        intro t ht i k
        rw [hDdef]
        exact mildTowerDeriv_coeff C hF hPL m hFm (fun t ↦ congrFun hPmdef t) hw2re' hw3re' ht i k
      -- the integral identity on the horizon
      have hDcontOn : ContinuousOn D (Ico 0 T) := hD.continuousOn
      have hint : ∀ b ∈ Ico (0 : ℝ) T, v b = v 0 + ∫ s in (0 : ℝ)..b, D s := by
        intro b hb
        have hsub : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun x hx ↦
          ⟨hx.1, lt_of_le_of_lt hx.2 hb.2⟩
        have hII : IntervalIntegrable D volume 0 b := by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hb.1]
          exact hDcontOn.mono hsub
        apply torusDatum_ext
        intro i k
        set c : ℝ := periodicFrequencyWeight k ^ ((m : ℝ) / 2) with hc
        set φ : ℝ → ℂ := fun s ↦ (c : ℂ) * torusPhysicalCoeff 3 (u s) i k with hφ
        set φ' : ℝ → ℂ := fun s ↦ (c : ℂ) * mildDerivCoeff C P u s i k with hφ'
        have hφc : ContinuousOn φ (Icc 0 b) := by
          have hcu : ContinuousOn (fun s ↦ torusPhysicalCoeff 3 (u s) i k) (Icc 0 b) := by
            have h1 : ContinuousOn (fun s ↦ (u s).1 i k) (Icc 0 b) :=
              ((torusEvalCLM 3 i k).continuous.comp_continuousOn
                (hu.continuous_path.mono (fun x hx ↦ ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hb.2)⟩)))
            exact (continuousOn_const.mul h1)
          exact continuousOn_const.mul hcu
        have hφ'eq : ∀ s ∈ Icc (0 : ℝ) b, φ' s = (D s).1 i k := by
          intro s hs
          rw [hDcoeff s (hsub hs) i k]
        have hφ'c : ContinuousOn φ' (Icc 0 b) := by
          apply ContinuousOn.congr _ hφ'eq
          exact (torusEvalCLM (m : ℝ) i k).continuous.comp_continuousOn (hDcontOn.mono hsub)
        have hderiv : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivWithinAt φ (φ' x) (Ioi x) x := by
          intro x hx
          have hxT : x ∈ Ioo (0 : ℝ) T := ⟨hx.1, lt_trans hx.2 hb.2⟩
          have hbase := mild_physicalCoeff_hasDerivAt hu hPc hxT i k
          exact (hbase.const_mul (c : ℂ)).hasDerivWithinAt
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb.1 hφc hderiv
          (hφ'c.intervalIntegrable_of_Icc hb.1)
        have hcoeffint : (∫ s in (0 : ℝ)..b, D s).1 i k = ∫ s in (0 : ℝ)..b, (D s).1 i k :=
          torusCoeff_intervalIntegral hII i k
        have hcongrint : (∫ s in (0 : ℝ)..b, (D s).1 i k) = ∫ s in (0 : ℝ)..b, φ' s := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hb.1] at hs
          exact (hφ'eq s hs).symm
        change (v b).1 i k = (v 0).1 i k + (∫ s in (0 : ℝ)..b, D s).1 i k
        rw [hcoeffint, hcongrint, hFTC, mildTower_coeff m hv hb i k,
          mildTower_coeff m hv ⟨le_rfl, hT⟩ i k]
        ring
      -- the derivative within the horizon
      have hderivWithin : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt v (D t) (Ico 0 T) t := by
        intro t ht
        set b' : ℝ := (t + T) / 2 with hb'
        have htb' : t < b' := by rw [hb']; linarith [ht.2]
        have hb'T : b' < T := by rw [hb']; linarith [ht.2]
        have hb'0 : (0 : ℝ) ≤ b' := le_trans ht.1 htb'.le
        have hclamp : Continuous (fun s : ℝ ↦ max 0 (min s b')) :=
          continuous_const.max (continuous_id.min continuous_const)
        have hclampmem : ∀ s : ℝ, max 0 (min s b') ∈ Icc (0 : ℝ) b' :=
          fun s ↦ ⟨le_max_left _ _, max_le hb'0 (min_le_right _ _)⟩
        have hIccsub : Icc (0 : ℝ) b' ⊆ Ico (0 : ℝ) T := fun x hx ↦
          ⟨hx.1, lt_of_le_of_lt hx.2 hb'T⟩
        set Dt : ℝ → PeriodicSobolev (m : ℝ) := fun s ↦ D (max 0 (min s b')) with hDt
        have hDtc : Continuous Dt :=
          (hDcontOn.mono hIccsub).comp_continuous hclamp hclampmem
        have hDteq : ∀ s ∈ Icc (0 : ℝ) b', Dt s = D s := by
          intro s hs
          have : max 0 (min s b') = s := by
            rw [min_eq_left hs.2, max_eq_right hs.1]
          rw [hDt]
          simp only [this]
        have hshift : ∀ b ∈ Icc (0 : ℝ) b',
            (∫ s in (0 : ℝ)..b, D s) = ∫ s in (0 : ℝ)..b, Dt s := by
          intro b hb
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hb.1] at hs
          exact (hDteq s ⟨hs.1, le_trans hs.2 hb.2⟩).symm
        have hFTC : HasDerivAt (fun b : ℝ ↦ v 0 + ∫ s in (0 : ℝ)..b, Dt s) (Dt t) t := by
          have hd := intervalIntegral.integral_hasDerivAt_right (f := Dt) (a := (0 : ℝ)) (b := t)
            (hDtc.intervalIntegrable 0 t)
            (hDtc.stronglyMeasurable.stronglyMeasurableAtFilter) hDtc.continuousAt
          exact hd.const_add _
        have hnhd : Ico (0 : ℝ) b' ∈ nhdsWithin t (Ico (0 : ℝ) T) := by
          apply mem_nhdsWithin.2
          refine ⟨Iio b', isOpen_Iio, htb', ?_⟩
          intro x hx
          exact ⟨hx.2.1, hx.1⟩
        have heq : ∀ x ∈ Ico (0 : ℝ) b', v x = v 0 + ∫ s in (0 : ℝ)..x, Dt s := by
          intro x hx
          rw [← hshift x ⟨hx.1, hx.2.le⟩]
          exact hint x (hIccsub ⟨hx.1, hx.2.le⟩)
        have hDtt : Dt t = D t := hDteq t ⟨ht.1, htb'.le⟩
        rw [← hDtt]
        exact (hFTC.hasDerivWithinAt).congr_of_eventuallyEq
          (Filter.eventually_of_mem hnhd heq) (heq t ⟨ht.1, htb'⟩)
      have hdiffOn : DifferentiableOn ℝ v (Ico 0 T) := fun t ht ↦
        (hderivWithin t ht).differentiableWithinAt
      rw [show (((j + 1 : ℕ)) : ℕ∞ω) = (j : ℕ∞ω) + 1 by push_cast; ring]
      rw [contDiffOn_succ_iff_derivWithin hudiff]
      refine ⟨hdiffOn, ?_, ?_⟩
      · exact fun hω ↦ absurd hω (mildClassical_nat_ne_omega j)
      · apply hD.congr
        intro t ht
        exact (hderivWithin t ht).derivWithin (hudiff t ht)

/-- All-order time smoothness of every realization of a forced mild solution. -/
theorem mildTower_contDiffOn {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (m : ℕ) (v : ℝ → PeriodicSobolev (m : ℝ))
    (hv : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 (m : ℝ) (u t) (v t)) :
    ContDiffOn ℝ ∞ v (Ico 0 T) :=
  contDiffOn_infty.2 (fun j ↦
    mildTower_contDiffOn_nat hν C ha hg hgp hT hA hF hPL hu hPc j m v hv)

/-! ## 3. Fourier inversion as a smooth family of functionals -/

theorem mildClassical_one_le_weight (k : PeriodicFrequency) :
    1 ≤ periodicFrequencyWeight k := one_le_periodicFrequencyWeight' k

/-- Inverse weights of any exponent at least three are summable. -/
theorem mildClassical_summable_inv_rpow {α : ℝ} (hα : 3 ≤ α) :
    Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ (-α)) := by
  have hbase : Summable (fun k : PeriodicFrequency ↦ (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹) := by
    simpa only [torus_weight_eq] using
      NSFormalization.Paper1.PeriodicInverseWeightSummable.summable_inverse_weight_cube
  have hbase' : Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ (-3 : ℝ)) := by
    refine hbase.congr (fun k ↦ ?_)
    rw [Real.rpow_neg (mildClassical_weight_pos k).le, ← Real.rpow_natCast _ 3]
    norm_num
  refine Summable.of_nonneg_of_le (fun k ↦ Real.rpow_nonneg (mildClassical_weight_pos k).le _)
    (fun k ↦ ?_) hbase'
  exact Real.rpow_le_rpow_of_exponent_le (mildClassical_one_le_weight k) (by linarith)

/-- The unweighted Fourier coefficient as a bounded real functional. -/
def torusPhysicalCoeffCLM (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    PeriodicSobolev s →L[ℝ] ℂ :=
  (periodicFrequencyWeight k ^ (-s / 2) : ℝ) • torusEvalCLM s i k

theorem torusPhysicalCoeffCLM_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency)
    (A : PeriodicSobolev s) :
    torusPhysicalCoeffCLM s i k A = torusPhysicalCoeff s A i k := by
  change (periodicFrequencyWeight k ^ (-s / 2) : ℝ) • (torusEvalCLM s i k A) = _
  rw [torusEvalCLM_apply, torusPhysicalCoeff, Complex.real_smul]

theorem torusPhysicalCoeffCLM_norm_le (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    ‖torusPhysicalCoeffCLM s i k‖ ≤ periodicFrequencyWeight k ^ (-s / 2) := by
  have hev : ‖torusEvalCLM s i k‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa only [one_mul, torusEvalCLM_apply] using torusCoeff_norm_le A i k
  have hpos : (0 : ℝ) ≤ periodicFrequencyWeight k ^ (-s / 2) :=
    Real.rpow_nonneg (mildClassical_weight_pos k).le _
  have hsm : ‖torusPhysicalCoeffCLM s i k‖ ≤
      ‖(periodicFrequencyWeight k ^ (-s / 2) : ℝ)‖ * ‖torusEvalCLM s i k‖ := by
    change ‖(periodicFrequencyWeight k ^ (-s / 2) : ℝ) • torusEvalCLM s i k‖ ≤ _
    exact norm_smul_le (periodicFrequencyWeight k ^ (-s / 2) : ℝ) (torusEvalCLM s i k)
  calc ‖torusPhysicalCoeffCLM s i k‖
      ≤ ‖(periodicFrequencyWeight k ^ (-s / 2) : ℝ)‖ * ‖torusEvalCLM s i k‖ := hsm
    _ ≤ periodicFrequencyWeight k ^ (-s / 2) * 1 := by
        refine mul_le_mul ?_ hev (norm_nonneg _) hpos
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    _ = _ := mul_one _

/-- One term of the Fourier inversion, as a functional-valued function of the point. -/
def torusEvalTerm (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) (x : Space) :
    PeriodicSobolev s →L[ℝ] ℂ :=
  NSFormalization.Paper1.periodicCharacter k x • torusPhysicalCoeffCLM s i k

theorem torusEvalTerm_norm (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) (x : Space) :
    ‖torusEvalTerm s i k x‖ = ‖torusPhysicalCoeffCLM s i k‖ := by
  rw [torusEvalTerm, norm_smul, torusCharacter_norm, one_mul]

theorem torusEvalTerm_summable {s : ℝ} (hs : 6 ≤ s) (i : Fin 3) (x : Space) :
    Summable (fun k ↦ torusEvalTerm s i k x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
    (mildClassical_summable_inv_rpow (α := s / 2) (by linarith))
  rw [torusEvalTerm_norm]
  have := torusPhysicalCoeffCLM_norm_le s i k
  rwa [show (-s / 2 : ℝ) = -(s / 2) by ring] at this

/-- The Fourier inversion of the `i`-th component as a bounded functional at `x`. -/
def torusEvalSeriesCLM (s : ℝ) (i : Fin 3) (x : Space) : PeriodicSobolev s →L[ℝ] ℂ :=
  ∑' k, torusEvalTerm s i k x

theorem torusEvalSeriesCLM_apply {s : ℝ} (hs : 6 ≤ s) (i : Fin 3) (x : Space)
    (A : PeriodicSobolev s) :
    torusEvalSeriesCLM s i x A =
      ∑' k, torusPhysicalCoeff s A i k * NSFormalization.Paper1.periodicCharacter k x := by
  have hmap := (ContinuousLinearMap.apply ℝ ℂ A).map_tsum (torusEvalTerm_summable hs i x)
  have h1 : torusEvalSeriesCLM s i x A = ∑' k, (torusEvalTerm s i k x) A := hmap
  rw [h1]
  refine tsum_congr (fun k ↦ ?_)
  change NSFormalization.Paper1.periodicCharacter k x • torusPhysicalCoeffCLM s i k A = _
  rw [torusPhysicalCoeffCLM_apply, smul_eq_mul, mul_comm]

/-- The evaluation family is `C^n` in the physical point once the Sobolev order is
large compared with `n`. -/
theorem torusEvalSeriesCLM_contDiff {s : ℝ} {n : ℕ} (hs : 2 * (n : ℝ) + 6 ≤ s) (i : Fin 3) :
    ContDiff ℝ (n : ℕ) (torusEvalSeriesCLM s i) := by
  apply contDiff_tsum (v := fun q k ↦ 3 ^ q * periodicFrequencyWeight k ^ ((q : ℝ) - s / 2))
  · intro k
    exact (NSFormalization.Paper1.periodicCharacter_smooth k).of_le
      (by exact_mod_cast le_top) |>.smul contDiff_const
  · intro q hq
    have hqn : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq
    have hα : (3 : ℝ) ≤ s / 2 - (q : ℝ) := by linarith
    have hsum := mildClassical_summable_inv_rpow hα
    refine (hsum.mul_left (3 ^ q)).congr (fun k ↦ ?_)
    congr 2
    ring
  · intro q k x _
    have hb := assembly_character_derivative_bound k q x
    have hph := assembly_phase_norm_le k
    have hCk := torusPhysicalCoeffCLM_norm_le s i k
    have hL : ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (torusPhysicalCoeffCLM s i k)‖ ≤
        ‖torusPhysicalCoeffCLM s i k‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro z
      change ‖z • torusPhysicalCoeffCLM s i k‖ ≤ _
      rw [norm_smul, mul_comm]
    have hstep : ‖iteratedFDeriv ℝ q (torusEvalTerm s i k) x‖ ≤
        ‖torusPhysicalCoeffCLM s i k‖ * ‖NSFormalization.Paper1.periodicPhase k‖ ^ q := by
      have he : torusEvalTerm s i k = fun y ↦
          NSFormalization.Paper1.periodicCharacter k y • torusPhysicalCoeffCLM s i k := rfl
      rw [he, iteratedFDeriv_smul_const_apply
        ((NSFormalization.Paper1.periodicCharacter_smooth k).of_le (by simp)).contDiffAt]
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      exact mul_le_mul hL hb (norm_nonneg _) (norm_nonneg _)
    refine hstep.trans ?_
    have hw := mildClassical_weight_pos k
    calc ‖torusPhysicalCoeffCLM s i k‖ * ‖NSFormalization.Paper1.periodicPhase k‖ ^ q
        ≤ periodicFrequencyWeight k ^ (-s / 2) * (3 * periodicFrequencyWeight k) ^ q := by
          refine mul_le_mul hCk (pow_le_pow_left₀ (norm_nonneg _) hph q) (by positivity)
            (Real.rpow_nonneg hw.le _)
      _ = 3 ^ q * (periodicFrequencyWeight k ^ (-s / 2) * periodicFrequencyWeight k ^ (q : ℕ)) := by
          rw [mul_pow]; ring
      _ = 3 ^ q * periodicFrequencyWeight k ^ ((q : ℝ) - s / 2) := by
          rw [← Real.rpow_natCast (periodicFrequencyWeight k) q, ← Real.rpow_add hw]
          congr 2
          ring

/-- Joint slab smoothness of the Fourier inversion of a smooth Sobolev path. -/
theorem fourierSlice_contDiffOn {s : ℝ} {n : ℕ} (hs : 2 * (n : ℝ) + 6 ≤ s) {S : Set ℝ}
    {V : ℝ → PeriodicSobolev s} (hV : ContDiffOn ℝ (n : ℕ) V S) (i : Fin 3) :
    ContDiffOn ℝ (n : ℕ) (fun z : SpaceTime ↦ (torusEvalSeriesCLM s i z.2 (V z.1)).re)
      (S ×ˢ (univ : Set Space)) := by
  have h1 : ContDiffOn ℝ (n : ℕ) (fun z : SpaceTime ↦ torusEvalSeriesCLM s i z.2)
      (S ×ˢ (univ : Set Space)) :=
    (torusEvalSeriesCLM_contDiff hs i).comp_contDiffOn contDiff_snd.contDiffOn
  have h2 : ContDiffOn ℝ (n : ℕ) (fun z : SpaceTime ↦ V z.1) (S ×ˢ (univ : Set Space)) :=
    hV.comp (f := fun z : SpaceTime ↦ z.1) contDiff_fst.contDiffOn (fun z hz ↦ hz.1)
  have hbil : ContDiff ℝ (n : ℕ∞ω)
      (fun q : (PeriodicSobolev s →L[ℝ] ℂ) × PeriodicSobolev s ↦ q.1 q.2) :=
    isBoundedBilinearMap_apply.contDiff
  have h3 : ContDiffOn ℝ (n : ℕ) (fun z : SpaceTime ↦ torusEvalSeriesCLM s i z.2 (V z.1))
      (S ×ˢ (univ : Set Space)) := by
    simpa only [Function.comp_def] using hbil.comp_contDiffOn (h1.prodMk h2)
  exact Complex.reCLM.contDiff.comp_contDiffOn h3

/-- The evaluation family computes the physical Fourier inversion of any
realization of the same physical data. -/
theorem torusEvalSeriesCLM_eq_component {s : ℝ} (hs : 6 ≤ s) {B : PeriodicSobolev s}
    {A : PeriodicSobolev 3} (hBA : IsPeriodicReweight 3 s A B) (i : Fin 3) (x : Space) :
    torusEvalSeriesCLM s i x B = torusPhysicalComponent A i x := by
  rw [torusEvalSeriesCLM_apply hs]
  refine tsum_congr (fun k ↦ ?_)
  rw [(physicalCoeff_eq_iff_reweight A B).mpr hBA i k]

/-- Joint slab smoothness of the physical velocity of a forced mild solution. -/
theorem torusPhysicalVelocity_contDiffOn {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  rw [contDiffOn_infty]
  intro n
  obtain ⟨v, hvre, _, _⟩ :=
    persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu (2 * n + 6)
  have hs6 : (6 : ℝ) ≤ ((2 * n + 6 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsn : 2 * (n : ℝ) + 6 ≤ ((2 * n + 6 : ℕ) : ℝ) := by push_cast; ring_nf; linarith
  have hvs : ContDiffOn ℝ (n : ℕ) v (Ico 0 T) :=
    mildTower_contDiffOn_nat hν C ha hg hgp hT hA hF hPL hu hPc n (2 * n + 6) v hvre
  have hpi : ContDiffOn ℝ (n : ℕ)
      (fun z : SpaceTime ↦ WithLp.toLp 2 (fun i ↦
        (torusEvalSeriesCLM ((2 * n + 6 : ℕ) : ℝ) i z.2 (v z.1)).re))
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
    apply (PiLp.contDiff_toLp (𝕜 := ℝ) (E := fun _ : Fin 3 ↦ ℝ) (p := 2)).comp_contDiffOn
    rw [contDiffOn_pi]
    intro i
    exact fourierSlice_contDiffOn hsn hvs i
  refine hpi.congr ?_
  intro z hz
  have hzt : z.1 ∈ Ico (0 : ℝ) T := hz.1
  have : torusPhysicalVelocity u z =
      WithLp.toLp 2 (fun i ↦ (torusPhysicalComponent (u z.1) i z.2).re) := rfl
  rw [this]
  congr 1
  funext i
  rw [torusEvalSeriesCLM_eq_component hs6 (hvre z.1 hzt) i z.2]

/-! ## 4. The unprojected real-order convolution as a bounded bilinear map -/

theorem mildClassical_scalar_energy (c : PeriodicScalarData) :
    Summable (fun k ↦ ‖c k‖ ^ 2) := by
  simpa using (lp.memℓp c).summable (by norm_num)

theorem mildClassical_weight_rpow_le_one {r : ℝ} (hr : 0 ≤ r) (l : PeriodicFrequency) :
    ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (mildClassical_weight_pos l).le _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (mildClassical_one_le_weight l) (by linarith)

theorem mildClassical_convolution_summable {r : ℝ} (hr : 0 ≤ r) (c d : PeriodicScalarData)
    (k : PeriodicFrequency) :
    Summable (fun l : PeriodicFrequency ↦
      ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * c l *
        ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * d (k - l)‖) := by
  have hA : Summable (fun l ↦ ‖c l‖ ^ 2) := mildClassical_scalar_energy c
  have hB : Summable (fun l ↦ ‖d (k - l)‖ ^ 2) :=
    (mildClassical_scalar_energy d).comp_injective sub_right_injective
  apply (hA.add hB).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro l
  have hprod : ‖((periodicFrequencyWeight l ^ (-r / 2) : ℝ) : ℂ) * c l *
      ((periodicFrequencyWeight (k - l) ^ (-r / 2) : ℝ) : ℂ) * d (k - l)‖ ≤
        ‖c l‖ * ‖d (k - l)‖ := by
    simp only [norm_mul]
    calc
      _ ≤ (1 * ‖c l‖) * 1 * ‖d (k - l)‖ := by
          gcongr <;> exact mildClassical_weight_rpow_le_one hr _
      _ = _ := by ring
  exact hprod.trans (by nlinarith [sq_nonneg (‖c l‖ - ‖d (k - l)‖)])

theorem mildClassical_conv_add_left {r : ℝ} (hr : 0 ≤ r) (A D B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r (A + D) B i k =
      torusConvectionSymbolReal r A B i k + torusConvectionSymbolReal r D B i k := by
  unfold torusConvectionSymbolReal
  have h (j : Fin 3) := ((mildClassical_convolution_summable hr (A.1 j) (B.1 i) k).of_norm).tsum_add
    ((mildClassical_convolution_summable hr (D.1 j) (B.1 i) k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, add_mul, h, Finset.sum_add_distrib]

theorem mildClassical_conv_add_right {r : ℝ} (hr : 0 ≤ r) (A B D : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A (B + D) i k =
      torusConvectionSymbolReal r A B i k + torusConvectionSymbolReal r A D i k := by
  unfold torusConvectionSymbolReal
  have h (j : Fin 3) := ((mildClassical_convolution_summable hr (A.1 j) (B.1 i) k).of_norm).tsum_add
    ((mildClassical_convolution_summable hr (A.1 j) (D.1 i) k).of_norm)
  simp only [Submodule.coe_add, PiLp.add_apply, lp.coeFn_add, Pi.add_apply,
    mul_add, h, Finset.sum_add_distrib]

theorem mildClassical_conv_smul_left (r c : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r (c • A) B i k = (c : ℂ) * torusConvectionSymbolReal r A B i k := by
  unfold torusConvectionSymbolReal
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

theorem mildClassical_conv_smul_right (r c : ℝ) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbolReal r A (c • B) i k = (c : ℂ) * torusConvectionSymbolReal r A B i k := by
  unfold torusConvectionSymbolReal
  simp only [Submodule.coe_smul, PiLp.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul, mul_left_comm, mul_assoc, tsum_mul_left, Finset.mul_sum]

theorem mildClassical_convolutionConstant_nonneg (r : ℝ) :
    0 ≤ torusConvolutionConstant_real r := by
  unfold torusConvolutionConstant_real
  positivity

/-- The unprojected real-order convection datum, as a real bilinear map.  The
output Sobolev index is carried as the separate parameter `q` (see the note on
`torusConvolutionLinearMapReal`). -/
def torusConvUnprojLinear (r q : ℝ) (hr : 3 ≤ r) :
    PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev q :=
  LinearMap.mk₂ ℝ (torusConvectionDatumReal hr)
    (fun A D B ↦ torusDatum_ext (fun i k ↦ by
      simp only [torusConvectionDatumReal_coeff, Submodule.coe_add, PiLp.add_apply,
        lp.coeFn_add, Pi.add_apply]
      exact mildClassical_conv_add_left (by linarith) A D B i k))
    (fun c A B ↦ torusDatum_ext (fun i k ↦ by
      simp only [torusConvectionDatumReal_coeff, Submodule.coe_smul, PiLp.smul_apply,
        lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
      exact mildClassical_conv_smul_left r c A B i k))
    (fun A B D ↦ torusDatum_ext (fun i k ↦ by
      simp only [torusConvectionDatumReal_coeff, Submodule.coe_add, PiLp.add_apply,
        lp.coeFn_add, Pi.add_apply]
      exact mildClassical_conv_add_right (by linarith) A B D i k))
    (fun c A B ↦ torusDatum_ext (fun i k ↦ by
      simp only [torusConvectionDatumReal_coeff, Submodule.coe_smul, PiLp.smul_apply,
        lp.coeFn_smul, Pi.smul_apply, Complex.real_smul]
      exact mildClassical_conv_smul_right r c A B i k))

/-- The bounded unprojected real-order convolution. -/
def torusConvUnprojCLM (r q : ℝ) (hr : 3 ≤ r) :
    PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev q :=
  (torusConvUnprojLinear r q hr).mkContinuous₂ (torusConvolutionConstant_real r)
    (torusConvectionDatumReal_norm_le hr)

theorem torusConvUnprojCLM_coeff (r q : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvUnprojCLM r q hr A B).1 i k = torusConvectionSymbolReal r A B i k :=
  torusConvectionDatumReal_coeff hr A B i k

/-- Smoothness of the quadratic unprojected convolution along a smooth path.
Stated at plain real indices so that instance search never meets a compound
Sobolev index. -/
theorem convUnproj_contDiffOn {r q : ℝ} (hr : 3 ≤ r) {n : ℕ} {S : Set ℝ}
    {w : ℝ → PeriodicSobolev r} (hw : ContDiffOn ℝ (n : ℕ) w S) :
    ContDiffOn ℝ (n : ℕ) (fun t ↦ torusConvUnprojCLM r q hr (w t) (w t)) S := by
  have hleft : ContDiffOn ℝ (n : ℕ) (fun t ↦ torusConvUnprojCLM r q hr (w t)) S :=
    (torusConvUnprojCLM r q hr).contDiff.comp_contDiffOn hw
  exact (isBoundedBilinearMap_apply.contDiff (n := (n : ℕ∞ω))).comp_contDiffOn
    (hleft.prodMk hw)

/-- Smoothness of a bounded-operator image of a smooth path, at plain indices. -/
theorem clm_contDiffOn {r q : ℝ} (L : PeriodicSobolev r →L[ℝ] PeriodicSobolev q) {n : ℕ}
    {S : Set ℝ} {w : ℝ → PeriodicSobolev r} (hw : ContDiffOn ℝ (n : ℕ) w S) :
    ContDiffOn ℝ (n : ℕ) (fun t ↦ L (w t)) S :=
  L.contDiff.comp_contDiffOn hw

/-! ## 5. The pressure potential as a bounded operator -/

/-- The symbol `−2πik_j/(4π²|k|²)` recovering the Leray potential from the source. -/
def pressureSymbol (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then 0
  else -(periodicDerivativeSymbol j k) / ((periodicAngularFrequencySq k : ℝ) : ℂ)

theorem pressureSymbol_norm_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖pressureSymbol j k‖ ≤ 1 := by
  unfold pressureSymbol
  split_ifs with hk
  · simp
  · have hsq : (1 : ℝ) ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := mildPressure_one_le_sq_sum hk
    have hang : periodicAngularFrequencySq k = 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := rfl
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have habs : |(k j : ℝ)| ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := mildPressure_abs_le_sq_sum k j
    have hangpos : 0 < periodicAngularFrequencySq k := by
      rw [hang]; nlinarith [Real.pi_gt_three]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hangpos,
      div_le_one hangpos]
    have hnum : ‖periodicDerivativeSymbol j k‖ = 2 * Real.pi * |(k j : ℝ)| := by
      unfold periodicDerivativeSymbol
      rw [norm_mul, norm_mul, norm_mul]
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [hnum, hang]
    nlinarith [Real.pi_gt_three, habs, hsq]

/-- The symbol away from the zero mode. -/
theorem pressureSymbol_of_ne (j : Fin 3) {k : PeriodicFrequency} (hk : k ≠ 0) :
    pressureSymbol j k =
      -(periodicDerivativeSymbol j k) / ((periodicAngularFrequencySq k : ℝ) : ℂ) := by
  simp [pressureSymbol, hk]

theorem pressureSymbol_neg (j : Fin 3) (k : PeriodicFrequency) :
    pressureSymbol j (-k) = star (pressureSymbol j k) := by
  have hang : periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
    simp [periodicAngularFrequencySq]
  by_cases hk : k = 0
  · simp [pressureSymbol, hk]
  · have hnk : (-k) ≠ 0 := fun h ↦ hk (by simpa using congrArg Neg.neg h)
    rw [pressureSymbol_of_ne j hnk, pressureSymbol_of_ne j hk, hang]
    have hd : periodicDerivativeSymbol j (-k) = -periodicDerivativeSymbol j k := by
      unfold periodicDerivativeSymbol
      simp only [Pi.neg_apply, Int.cast_neg]
      ring
    have hs : star (periodicDerivativeSymbol j k) = -periodicDerivativeSymbol j k := by
      unfold periodicDerivativeSymbol
      simp
    rw [hd, neg_neg, star_div₀, star_neg, hs, neg_neg]
    congr 1
    simp

/-- Multiplication by a symbol of norm at most one on the scalar carrier. -/
def torusSymbolLp (σ : PeriodicFrequency → ℂ) (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (c : PeriodicScalarData) : PeriodicScalarData :=
  ⟨fun k ↦ σ k * c k, Memℓp.mono' (lp.memℓp c) (fun k ↦ by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hσ k))⟩

theorem torusSymbolLp_apply (σ : PeriodicFrequency → ℂ) (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (c : PeriodicScalarData) (k : PeriodicFrequency) :
    torusSymbolLp σ hσ c k = σ k * c k := rfl

theorem torusSymbolLp_norm_le (σ : PeriodicFrequency → ℂ) (hσ : ∀ k, ‖σ k‖ ≤ 1)
    (c : PeriodicScalarData) : ‖torusSymbolLp σ hσ c‖ ≤ ‖c‖ := by
  apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
  intro k
  rw [torusSymbolLp_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hσ k)

/-- The Leray potential of a vector datum, placed in every component slot. -/
def pressurePotentialDatum (s q : ℝ) (B : PeriodicSobolev s) : PeriodicSobolev q := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin 3 ↦
    ∑ j : Fin 3, torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j)), ?_⟩
  intro i k
  change (∑ j : Fin 3,
      torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j)) (-k) =
    star ((∑ j : Fin 3,
      torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j)) k)
  simp only [lp.coeFn_sum, Finset.sum_apply, torusSymbolLp_apply, star_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [pressureSymbol_neg, B.2 j k, star_mul']

theorem pressurePotentialDatum_coeff (s q : ℝ) (B : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    (pressurePotentialDatum s q B).1 i k = ∑ j : Fin 3, pressureSymbol j k * B.1 j k := by
  change (∑ j : Fin 3,
      torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j)) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply, torusSymbolLp_apply]

theorem pressurePotentialDatum_norm_le (s q : ℝ) (B : PeriodicSobolev s) :
    ‖pressurePotentialDatum s q B‖ ≤ 6 * ‖B‖ := by
  set c : PeriodicScalarData :=
    ∑ j : Fin 3, torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j) with hc
  have hcnorm : ‖c‖ ≤ 3 * ‖B‖ := by
    calc ‖c‖ ≤ ∑ j : Fin 3,
          ‖torusSymbolLp (pressureSymbol j) (pressureSymbol_norm_le j) (B.1 j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖B‖ := by
        refine Finset.sum_le_sum (fun j _ ↦ ?_)
        exact (torusSymbolLp_norm_le _ _ _).trans (PiLp.norm_apply_le B.1 j)
      _ = 3 * ‖B‖ := by simp [Finset.sum_const]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖(pressurePotentialDatum s q B).1‖ ^ 2 ≤ (6 * ‖B‖) ^ 2
  have hval : (pressurePotentialDatum s q B).1 = WithLp.toLp 2 (fun _ : Fin 3 ↦ c) := rfl
  rw [hval, PiLp.norm_sq_eq_of_L2]
  have : ∑ _i : Fin 3, ‖(WithLp.toLp 2 (fun _ : Fin 3 ↦ c) : PeriodicVectorData) _i‖ ^ 2 =
      3 * ‖c‖ ^ 2 := by
    simp [Finset.sum_const]
  rw [this]
  nlinarith [norm_nonneg B, norm_nonneg c, hcnorm]

/-- The bounded Leray-potential operator. -/
def pressurePotentialCLM (s q : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev q :=
  LinearMap.mkContinuous
    { toFun := pressurePotentialDatum s q
      map_add' := fun B D ↦ torusDatum_ext (fun i k ↦ by
        simp only [pressurePotentialDatum_coeff, Submodule.coe_add, PiLp.add_apply,
          lp.coeFn_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      map_smul' := fun r B ↦ torusDatum_ext (fun i k ↦ by
        simp only [pressurePotentialDatum_coeff, Submodule.coe_smul, PiLp.smul_apply,
          lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, RingHom.id_apply,
          Finset.mul_sum, mul_left_comm]) }
    6 (pressurePotentialDatum_norm_le s q)

theorem pressurePotentialCLM_coeff (s q : ℝ) (B : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    (pressurePotentialCLM s q B).1 i k = ∑ j : Fin 3, pressureSymbol j k * B.1 j k :=
  pressurePotentialDatum_coeff s q B i k

/-! ## 6. The pressure datum path and the joint smoothness of the pressure -/

/-- The order-`m` datum of the pressure source `g − ∇·(u⊗u)`. -/
def mildSourceDatum (m : ℕ) (Fm : ℝ → PeriodicSobolev (m : ℝ))
    (w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)) (t : ℝ) : PeriodicSobolev (m : ℝ) :=
  Fm t - persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
    (torusConvUnprojCLM ((m : ℝ) + 3) ((m : ℝ) + 2) (mildTower_three_le m) (w3 t) (w3 t))

theorem mildSourceDatum_coeff {T : ℝ} {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u)
    {F : ℝ → PeriodicSobolev 3} (hF : IsPeriodicSobolevPath 3 g F)
    (m : ℕ) {Fm : ℝ → PeriodicSobolev (m : ℝ)}
    (hFm : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) (Fm t))
    {w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)}
    (hw3 : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (j : Fin 3) (k : PeriodicFrequency) :
    (mildSourceDatum m Fm w3 t).1 j k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k := by
  have hw := mildClassical_weight_pos k
  have hforce : (Fm t).1 j k = ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
      torusPhysicalCoeff 3 (F t) j k := by
    rw [(hFm t).2.2 j k, torusPhysicalCoeff_eq (hF t ht.1), Complex.real_smul]
  have hdown : persistenceDown ((m : ℝ) + 3) 3 (mildTower_three_le m) (w3 t) = u t :=
    torusHalfStep_down_eq (mildTower_three_le m) hw3 ht
  have hre3 : IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t) := hw3 t ht
  have hconvsym : torusConvectionSymbolReal ((m : ℝ) + 3) (w3 t) (w3 t) j k =
      ((periodicFrequencyWeight k ^ (((m : ℝ) + 3 - 3) / 2) : ℝ) : ℂ) *
        torusConvectionSymbol (u t) (u t) j k := by
    rw [torusConvectionSymbolReal_reweight 3 ((m : ℝ) + 3) hre3 hre3 j k,
      torusConvectionSymbolReal_three]
  have hconv : (persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
        (torusConvUnprojCLM ((m : ℝ) + 3) ((m : ℝ) + 2) (mildTower_three_le m)
          (w3 t) (w3 t))).1 j k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k := by
    change ((periodicFrequencyWeight k ^ (((m : ℝ) - ((m : ℝ) + 2)) / 2) : ℝ) : ℂ) *
      (torusConvUnprojCLM ((m : ℝ) + 3) ((m : ℝ) + 2) (mildTower_three_le m)
        (w3 t) (w3 t)).1 j k = _
    rw [torusConvUnprojCLM_coeff, hconvsym, torusPhysicalCoeff,
      torusConvectionDatum_coeff]
    simp only [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [← Real.rpow_add hw, ← Real.rpow_add hw]
    congr 1
    ring
  change (Fm t).1 j k - (persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)
      (torusConvUnprojCLM ((m : ℝ) + 3) ((m : ℝ) + 2) (mildTower_three_le m)
        (w3 t) (w3 t))).1 j k = _
  rw [hforce, hconv, mildPressureSourceCoeff_eq_canonical hu hF ht j k, mul_sub]

/-- The order-`m` datum of the pressure. -/
def mildPressureDatum (m : ℕ) (Fm : ℝ → PeriodicSobolev (m : ℝ))
    (w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)) (t : ℝ) : PeriodicSobolev (m : ℝ) :=
  pressurePotentialCLM (m : ℝ) (m : ℝ) (mildSourceDatum m Fm w3 t)

/-- The pressure symbol reproduces the Leray potential coefficient. -/
theorem sum_pressureSymbol_eq (S : SpatialField) (k : PeriodicFrequency) :
    (∑ j : Fin 3, pressureSymbol j k * sourceComponentCoeff S j k) =
      lerayPotentialCoeff S k := by
  by_cases hk : k = 0
  · subst hk
    simp [pressureSymbol, lerayPotentialCoeff_zero]
  · have hsq : (1 : ℝ) ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := mildPressure_one_le_sq_sum hk
    have hangpos : 0 < periodicAngularFrequencySq k := by
      have : periodicAngularFrequencySq k = 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := rfl
      rw [this]
      nlinarith [Real.pi_gt_three]
    have hne : ((periodicAngularFrequencySq k : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hangpos)
    have hlap := lerayPotentialCoeff_laplace_symbol S k
    have hcast : (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) =
        -((periodicAngularFrequencySq k : ℝ) : ℂ) := by
      push_cast [periodicAngularFrequencySq]
      ring
    rw [hcast] at hlap
    have hstep : ∀ j : Fin 3, pressureSymbol j k * sourceComponentCoeff S j k =
        -(periodicDerivativeSymbol j k * sourceComponentCoeff S j k) /
          ((periodicAngularFrequencySq k : ℝ) : ℂ) := by
      intro j
      rw [pressureSymbol_of_ne j hk]
      ring
    have hneg : (∑ j : Fin 3, -(periodicDerivativeSymbol j k * sourceComponentCoeff S j k)) =
        -(∑ j : Fin 3, periodicDerivativeSymbol j k * sourceComponentCoeff S j k) := by
      simp
    simp only [hstep]
    rw [← Finset.sum_div, hneg, ← hlap]
    field_simp

theorem mildPressureDatum_coeff {T : ℝ} {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u)
    {F : ℝ → PeriodicSobolev 3} (hF : IsPeriodicSobolevPath 3 g F)
    (m : ℕ) {Fm : ℝ → PeriodicSobolev (m : ℝ)}
    (hFm : ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) (Fm t))
    {w3 : ℝ → PeriodicSobolev ((m : ℝ) + 3)}
    (hw3 : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    (mildPressureDatum m Fm w3 t).1 i k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) * mildPressureCoeff g u t k := by
  rw [mildPressureDatum, pressurePotentialCLM_coeff]
  have hstep : ∀ j : Fin 3, pressureSymbol j k * (mildSourceDatum m Fm w3 t).1 j k =
      ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (pressureSymbol j k *
          sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) := by
    intro j
    rw [mildSourceDatum_coeff hu hF m hFm hw3 ht j k]
    ring
  simp only [hstep, ← Finset.mul_sum]
  rw [sum_pressureSymbol_eq]
  rfl

/-- Smooth order-`m` datum paths of a smooth unit-periodic force. -/
theorem exists_smooth_forceDatumPath {g : SpaceTimeField} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodicOn univ g) (m : ℕ) :
    ∃ Fm : ℝ → PeriodicSobolev (m : ℝ), ContDiff ℝ ∞ Fm ∧
      ∀ t : ℝ, IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) (Fm t) := by
  classical
  have hex : ∀ t : ℝ, ∃ B : PeriodicSobolev (m : ℝ),
      IsPeriodicDatum (m : ℝ) (fun x ↦ g (t, x)) B := fun t ↦
    smooth_periodic_datum (m : ℝ) (hg.comp (contDiff_const.prodMk contDiff_id))
      (hgp t (mem_univ t))
  choose Fm hFm using hex
  exact ⟨Fm, datumPath_contDiff m hg hgp Fm hFm, hFm⟩

/-- The projected force path of a smooth periodic force is continuous. -/
theorem forcedLeray_continuousOn {g : SpaceTimeField} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodicOn univ g) {F P : ℝ → PeriodicSobolev 3}
    (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) (T : ℝ) :
    ContinuousOn P (Icc (0 : ℝ) T) := by
  obtain ⟨F3, hF3c, hF3⟩ := exists_smooth_forceDatumPath hg hgp 3
  have hFeq : ∀ t : ℝ, 0 ≤ t → F t = F3 t := by
    intro t ht
    apply torusDatum_ext
    intro i k
    rw [(hF t ht).2.2 i k, (hF3 t).2.2 i k]
    norm_num
  have hPeq : ∀ t ∈ Icc (0 : ℝ) T, P t = torusLerayCLM 3 (F3 t) := by
    intro t ht
    rw [torusLerayCLM_eq_of_isDatum (hPL t ht.1), hFeq t ht.1]
  exact ContinuousOn.congr
    (((torusLerayCLM (3 : ℝ)).continuous.comp hF3c.continuous).continuousOn) hPeq

/-- The force path of a smooth periodic force satisfies lane 320's persistence input. -/
theorem forcePersistenceInput {g : SpaceTimeField} (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodicOn univ g) {F : ℝ → PeriodicSobolev 3}
    (hF : IsPeriodicSobolevPath 3 g F) (T : ℝ) : PersistenceInput T F := by
  intro m
  obtain ⟨Fm, hFmc, hFm⟩ := exists_smooth_forceDatumPath hg hgp m
  refine ⟨Fm, hFmc.continuous.continuousOn, fun t ht j k ↦ ?_⟩
  rw [torusPhysicalCoeff_eq (hFm t), torusPhysicalCoeff_eq (hF t ht.1)]

/-- Lane 330's persistence, in the shape of lane 320's `PersistenceInput`. -/
theorem persistenceInput_of_mild {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) : PersistenceInput T u := by
  intro m
  obtain ⟨v, hvre, hvc, _⟩ :=
    persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu m
  exact ⟨v, hvc, fun t ht i k ↦ (physicalCoeff_eq_iff_reweight (u t) (v t)).mpr (hvre t ht) i k⟩

/-- Joint slab smoothness of the constructed pressure. -/
theorem mildPressure_contDiffOn {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  have hPI : PersistenceInput T u := persistenceInput_of_mild hν C ha hg hgp hT hA hF hPL hu
  rw [contDiffOn_infty]
  intro n
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * n + 6 := ⟨_, rfl⟩
  obtain ⟨Fm, hFmsmooth, hFm⟩ := exists_smooth_forceDatumPath hg hgp m
  obtain ⟨w3, hw3re, _, _⟩ :=
    persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu (m + 3)
  have hw3re' : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 ((m : ℝ) + 3) (u t) (w3 t) := by
    intro t ht i k
    have h := hw3re t ht i k
    push_cast at h
    exact h
  have hw3s : ContDiffOn ℝ (n : ℕ) w3 (Ico 0 T) :=
    mildTower_contDiffOn_nat hν C ha hg hgp hT hA hF hPL hu hPc n (m + 3) w3 hw3re
  have hs6 : (6 : ℝ) ≤ ((m : ℕ) : ℝ) := by
    rw [hm]; push_cast
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsn : 2 * (n : ℝ) + 6 ≤ ((m : ℕ) : ℝ) := by rw [hm]; push_cast; ring_nf; linarith
  have hbil : ContDiffOn ℝ (n : ℕ)
      (fun t ↦ torusConvUnprojCLM ((m : ℝ) + 3) ((m : ℝ) + 2) (mildTower_three_le m)
        (w3 t) (w3 t)) (Ico 0 T) :=
    convUnproj_contDiffOn (q := (m : ℝ) + 2) (mildTower_three_le m) hw3s
  have hSm : ContDiffOn ℝ (n : ℕ) (mildSourceDatum m Fm w3) (Ico 0 T) :=
    (hFmsmooth.of_le (by exact_mod_cast le_top)).contDiffOn.sub
      (clm_contDiffOn (persistenceDown ((m : ℝ) + 2) (m : ℝ) (mildTower_le_add_two m)) hbil)
  have hPm : ContDiffOn ℝ (n : ℕ) (mildPressureDatum m Fm w3) (Ico 0 T) :=
    clm_contDiffOn (pressurePotentialCLM (m : ℝ) (m : ℝ)) hSm
  have hslice := fourierSlice_contDiffOn hsn hPm 0
  refine hslice.congr ?_
  intro z hz
  have hzt : z.1 ∈ Ico (0 : ℝ) T := hz.1
  rw [torusEvalSeriesCLM_apply hs6]
  have hcoeff : ∀ k : PeriodicFrequency,
      torusPhysicalCoeff ((m : ℕ) : ℝ) (mildPressureDatum m Fm w3 z.1) 0 k =
        mildPressureCoeff g u z.1 k := by
    intro k
    have hw := mildClassical_weight_pos k
    rw [torusPhysicalCoeff, mildPressureDatum_coeff hPI hF m hFm hw3re' hzt 0 k,
      ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hw,
      show (-(m : ℝ) / 2 + (m : ℝ) / 2) = 0 by ring, Real.rpow_zero]
    simp
  simp only [hcoeff]
  rfl

/-! ## 7. The U9d target and its Picard corollary -/

/-- **U9d.**  Every forced mild solution on the torus is the Fourier datum path
of a genuine classical solution on the same horizon, with all three local
regularity clauses. -/
theorem mild_to_classical (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
    (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u := by
  have hPc : ContinuousOn P (Icc (0 : ℝ) T) := forcedLeray_continuousOn hg hgp hF hPL T
  have hPI : PersistenceInput T u := persistenceInput_of_mild hν C ha hg hgp hT hA hF hPL hu
  have hFI : PersistenceInput T F := forcePersistenceInput hg hgp hF T
  have hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence (torusPhysicalVelocity u) t x = 0 :=
    persistence_mild_physical_divergence ha hA hPL hu hPI
  refine ⟨{ velocity := torusPhysicalVelocity u
            pressure := mildPressure g u
            horizon_pos := hT
            velocity_smooth :=
              torusPhysicalVelocity_contDiffOn hν C ha hg hgp hT hA hF hPL hu hPc
            pressure_smooth := mildPressure_contDiffOn hν C ha hg hgp hT hA hF hPL hu hPc
            initial := fun x ↦ torusPhysicalVelocity_initial ha hA hu x
            divergence := hdiv
            momentum := fun t ht x ↦
              momentum_of_mildPressure hu hPc hPI hFI hPL hg hgp hF hdiv ht x
            sobolev := persistence_physical_sobolev hPI
            pressure_gradient := mildPressure_gradient_memLp hg hgp hPI
            velocity_periodic := fun t _ ↦ torusPhysicalVelocity_periodic u t (mem_univ t)
            pressure_periodic := fun t _ ↦ mildPressure_periodic g u t (mem_univ t)
            pressure_gauge := mildPressure_gauge hg hgp hPI }, ⟨?_, ?_, ?_⟩,
    torusPhysicalVelocity_datum u _⟩
  · intro m
    obtain ⟨v, hvre, _, _⟩ :=
      persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu m
    exact ⟨v, torusPhysicalVelocity_reweight hvre,
      mildTower_contDiffOn hν C ha hg hgp hT hA hF hPL hu hPc m v hvre⟩
  · exact mildPressure_poisson hg hgp hPI
  · intro t ht x
    exact projected_of_mildPressure hu hPc hPI hFI hPL hg hgp hF hdiv ht x

/-- The Picard horizon of a smooth periodic datum and force carries a genuine
classical solution.  No named input is used anywhere in the chain. -/
theorem exists_classical_of_picard (ν : ℝ) (hν : 0 < ν) (a : SpatialField)
    (ha : a ∈ initialClassT) (g : SpaceTimeField) (hg : ContDiff ℝ ∞ g)
    (hgp : IsPeriodicOn univ g) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g δ,
      PeriodicLocalRegularity ν a g δ w := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' ν hν
  obtain ⟨A, hA⟩ := smooth_periodic_datum (3 : ℝ) ha.1 ha.2.1
  obtain ⟨F3, hF3c, hF3⟩ := exists_smooth_forceDatumPath hg hgp 3
  have hFpath : IsPeriodicSobolevPath 3 g F3 := by
    intro t _
    refine ⟨(hF3 t).1, (hF3 t).2.1, fun i k ↦ ?_⟩
    simpa using (hF3 t).2.2 i k
  refine ?_
  let Pp : ℝ → PeriodicSobolev 3 := fun t ↦ torusLerayCLM (3 : ℝ) (F3 t)
  have hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F3 t) (Pp t) :=
    fun t _ i k ↦ torusLerayCLM_coeff (3 : ℝ) (F3 t) i k
  have hPcont : Continuous Pp := (torusLerayCLM (3 : ℝ)).continuous.comp hF3c.continuous
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := Pp) (s := Icc (0 : ℝ) 1) hPcont.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (Pp 0)) (hB 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨hT0, _, u, hmild, _⟩ := torusForcedPicard_quantitative hν C A Pp B hB0
    hPcont.continuousOn hB
  obtain ⟨w, hreg, _⟩ := mild_to_classical ν hν C a g _ ha hg hgp hT0 A F3 Pp u hA hFpath hPL hmild
  exact ⟨_, hT0, w, hreg⟩

/-! ## 8. Non-vacuity -/

/-- The constant-force affine family satisfies every hypothesis of
`mild_to_classical` on an arbitrary positive horizon, and the classical solution
it produces starts at the prescribed datum. -/
theorem mild_to_classical_affine_constant {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (T : ℝ) (hT : 0 < T) (c : Space) :
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) T,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity
        (fun t ↦ (1 + t) • torusConstantDatum 3 c) ∧
      ∀ x : Space, w.velocity (0, x) = c := by
  have hmild := torusForcedMildOn_affine_constant C c hT.le
  have hFpath : IsPeriodicSobolevPath 3 (fun _ : SpaceTime ↦ c)
      (fun _ : ℝ ↦ torusConstantDatum 3 c) := fun t _ ↦ torusConstantDatum_isDatum 3 c
  obtain ⟨w, hreg, hpath⟩ := mild_to_classical ν hν C (fun _ ↦ c) (fun _ : SpaceTime ↦ c) T
    (constantDatum_mem_initialClassT c) contDiff_const (fun _ _ _ _ ↦ rfl) hT
    (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c)
    (fun t ↦ (1 + t) • torusConstantDatum 3 c) (torusConstantDatum_isDatum 3 c) hFpath
    (fun t _ ↦ torusConstantDatum_lerayDatum 3 c) hmild
  exact ⟨w, hreg, hpath, w.initial⟩

example {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν) (c : Space) :
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) 1,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun _ : SpaceTime ↦ c) 1 w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity
        (fun t ↦ (1 + t) • torusConstantDatum 3 c) ∧
      ∀ x : Space, w.velocity (0, x) = c :=
  mild_to_classical_affine_constant hν C 1 one_pos c

example (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
    (g : SpaceTimeField) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g δ,
      PeriodicLocalRegularity ν a g δ w :=
  exists_classical_of_picard ν hν a ha g hg hgp

end NSFormalization.Section3.T11
