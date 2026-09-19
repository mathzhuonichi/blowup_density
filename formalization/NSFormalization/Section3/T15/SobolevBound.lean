import NSFormalization.Section3.T15.ForceMem
import NSFormalization.Section3.T17.Sobolev
import NSFormalization.Paper1.PeriodicPacketEndpointRates
import NSFormalization.Paper3.PositiveFourierTime

/-! # T15 U12–U13: the packet force Sobolev estimate. -/
noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source (coordinateForce fourierSobolevNorm)
open NavierStokes.PeriodicLocalization (SupportedInCube periodize)
open NSFormalization.Paper1.PeriodicBridge (supported_comp periodize_comp)
open NSFormalization.Paper1.PeriodicForceConvergence (periodicVectorSobolevNorm)
open scoped ContDiff ENNReal Topology BigOperators

/-- The unscaled component endpoint time norm. -/
def packetEndpoint (f : VelocityField) (s : ℝ) (i : Fin 3) : ℝ≥0∞ :=
  eLpNorm (fun t => fourierSobolevNorm s (fun x => coordinateForce f i (t, x))) 1 volume

/-- One scale-independent interpolation constant for each component. -/
def packetComponentConst (f : VelocityField) (s : ℝ) (i : Fin 3) : ℝ :=
  (packetEndpoint f 0 i).toReal ^ (1 - s) *
    (2 * Real.pi * (packetEndpoint f 1 i).toReal) ^ s

/-- Explicit positive family, chosen before the scale. -/
def sobolevConst (f : VelocityField) (s : ℝ) : ℝ :=
  1 + ∑ i : Fin 3, packetComponentConst f s i

theorem packetComponentConst_nonneg (f : VelocityField) (s : ℝ) (i : Fin 3) :
    0 ≤ packetComponentConst f s i := by
  unfold packetComponentConst
  positivity

theorem sobolevConst_pos (f : VelocityField) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst f s := by
  intro s _ _
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => packetComponentConst_nonneg f s i)
  unfold sobolevConst
  linarith

/-- The exact U12 path field, obtained from smooth periodic test-force data. -/
theorem forceSobolev_memLp
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s (periodizedScaledForce f place.x₀ place.T ε) := by
  intro s _ hs ε hε
  obtain ⟨G, _, _, _, _, hpath, hLp⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real (force_mem hf hc place ε hε) hs
  exact ⟨G, hpath, hLp⟩

/-- Recenter the Euclidean copy at the chart center, not the packet center. -/
def chartForce (f : VelocityField) (x₀ c : Space) (T ε : ℝ) : VelocityField :=
  fun z => scaledForce f x₀ T ε (z.1, z.2 + c)

theorem chartForce_smooth {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (x₀ c : Space) (T ε : ℝ) : ContDiff ℝ ∞ (chartForce f x₀ c T ε) := by
  have h : ContDiff ℝ ∞ (scaledForce f x₀ T ε) := by
    rw [scaledForce_eq_parabolicForce]
    exact NSFormalization.Source.parabolicForce_smooth _ _ _ hf
  exact h.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))

theorem chartForce_compact {f : VelocityField} (hc : HasCompactSupport f)
    (x₀ c : Space) (T ε : ℝ) : HasCompactSupport (chartForce f x₀ c T ε) := by
  have h : HasCompactSupport (scaledForce f x₀ T ε) := by
    rw [scaledForce_eq_parabolicForce]
    exact NSFormalization.Source.parabolicForce_compact _ _ _ hc
  exact h.comp_homeomorph (Homeomorph.refl ℝ |>.prodCongr (Homeomorph.addRight c))

theorem chartForce_supportedInCube
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    SupportedInCube place.chartRadius (chartForce f place.x₀ place.chartCenter place.T ε) := by
  intro z hz i
  have hs := scaledForce_tsupp_subset hε.1 place.Kstar_compact hc
    place.force_projection_subset z.1 (subset_tsupport _ hz)
  have hb := affineImage_subset_ball hε place.eps_space hs
  rw [Metric.mem_ball, dist_eq_norm] at hb
  simp only [add_sub_cancel_right] at hb
  exact (abs_spaceCoord_le_norm z.2 i).trans hb.le

theorem chartRadius_lt_half {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : PlacementData u p f K) : place.chartRadius < 1 / 2 := by
  obtain ⟨h0, h1⟩ := ball_coord_bounds place.chartRadius_pos place.chartBall_in_cube 0
  linarith

theorem periodize_chartForce (f : VelocityField) (x₀ c : Space) (T ε t : ℝ) (x : Space) :
    periodize (chartForce f x₀ c T ε) (t, x) =
      periodizedScaledForce f x₀ T ε (t, x + c) := by
  apply tsum_congr
  intro n
  change scaledForce f x₀ T ε (t, x - latticeVector n + c) =
    scaledForce f x₀ T ε (t, x + c - latticeVector n)
  rw [sub_add_eq_add_sub]

theorem chartForce_fourierNorm (f : VelocityField) (x₀ c : Space) (T ε s t : ℝ) (i : Fin 3) :
    fourierSobolevNorm s (fun x => coordinateForce (chartForce f x₀ c T ε) i (t, x)) =
      fourierSobolevNorm s (fun x => coordinateForce
        (NSFormalization.Source.parabolicForce ε⁻¹ (T - ε ^ 2) 0 f) i (t, x)) := by
  change fourierSobolevNorm s (fun x => coordinateForce (scaledForce f x₀ T ε) i (t, x + c)) = _
  have ht := NSFormalization.Source.fourierSobolevNorm_translate s
    (fun x => coordinateForce (scaledForce f x₀ T ε) i (t, x)) (-c)
  simp only [sub_neg_eq_add] at ht
  rw [ht, scaledForce_eq_parabolicForce,
    NSFormalization.Source.coordinate_norm_parabolicForce,
    NSFormalization.Source.coordinate_norm_parabolicForce]

theorem packetEndpoint_lt_top {f : VelocityField} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : ℝ} (hs : s ≤ 1) (i : Fin 3) :
    packetEndpoint f s i < ⊤ :=
  (NSFormalization.Paper3.memLp_fourierSobolev_le_one_time hs
    (NSFormalization.Source.coordinateForce_smooth hf i)
    (NSFormalization.Source.coordinateForce_compact hc i) 1).2

/-- Interpolated component estimate at every admissible scale. -/
theorem packet_component_bound
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (i : Fin 3) :
    eLpNorm (fun t => NSFormalization.Paper1.periodicSobolevNorm s
      (fun x => coordinateForce
        (periodize (chartForce f place.x₀ place.chartCenter place.T ε)) i (t, x))) 1 volume ≤
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2 - s) * packetComponentConst f s i) := by
  have hε0 := hε.1
  have hε1 := hε.2.trans place.eps_le_one
  have hS := chartForce_supportedInCube hc place hε
  have hr := chartRadius_lt_half place
  have hsm := chartForce_smooth hf place.x₀ place.chartCenter place.T ε
  have hcp := chartForce_compact hc.1 place.x₀ place.chartCenter place.T ε
  have hcoord := periodize_comp hS hr (fun w : Space => (w i : ℂ)) (by simp)
  have heq : (fun t => NSFormalization.Paper1.periodicSobolevNorm s
      (fun x => coordinateForce
        (periodize (chartForce f place.x₀ place.chartCenter place.T ε)) i (t, x))) =
      fun t => NSFormalization.Paper1.periodicSobolevNorm s
        (fun x => periodize (coordinateForce
          (chartForce f place.x₀ place.chartCenter place.T ε) i) (t, x)) := by
    funext t
    exact congrArg (NSFormalization.Paper1.periodicSobolevNorm s)
      (funext fun x => congrFun hcoord (t, x))
  rw [heq]
  refine (NSFormalization.Paper1.PeriodicForceEndpointScaling.periodized_scalar_L1Hs_le_endpoint_product
    (supported_comp hS (fun w : Space => (w i : ℂ)) (by simp)) hr
    (NSFormalization.Source.coordinateForce_smooth hsm i)
    (NSFormalization.Source.coordinateForce_compact hcp i) hs0 hs1).trans ?_
  change (eLpNorm (fun t => fourierSobolevNorm 0 (fun x => coordinateForce
    (chartForce f place.x₀ place.chartCenter place.T ε) i (t, x))) 1 volume) ^ (1 - s) *
    (ENNReal.ofReal (2 * Real.pi) * eLpNorm (fun t => fourierSobolevNorm 1
      (fun x => coordinateForce (chartForce f place.x₀ place.chartCenter place.T ε) i (t, x)))
        1 volume) ^ s ≤ _
  simp only [chartForce_fourierNorm]
  have hrate0 := NSFormalization.Paper1.PeriodicPacketEndpointRates.packet_scalar_H0_L1_endpoint_bound
    hf hc.1 i hε0 hε1 (place.T - ε ^ 2)
  have hrate1 := NSFormalization.Paper1.PeriodicPacketEndpointRates.packet_scalar_H1_L1_endpoint_bound
    hf hc.1 i hε0 hε1 (place.T - ε ^ 2)
  refine le_trans (mul_le_mul'
    (ENNReal.rpow_le_rpow hrate0 (by linarith))
    (ENNReal.rpow_le_rpow (mul_le_mul' (le_refl (ENNReal.ofReal (2 * Real.pi))) hrate1)
      hs0)) (le_of_eq ?_)
  change (ENNReal.ofReal (ε ^ ((1 : ℝ) / 2)) * packetEndpoint f 0 i) ^ (1 - s) *
    (ENNReal.ofReal (2 * Real.pi) *
      (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * packetEndpoint f 1 i)) ^ s = _
  have hC0top := packetEndpoint_lt_top hf hc.1 (s := 0) (by norm_num) i
  have hC1top := packetEndpoint_lt_top hf hc.1 (s := 1) le_rfl i
  set c0 : ℝ := (packetEndpoint f 0 i).toReal with hc0def
  set c1 : ℝ := (packetEndpoint f 1 i).toReal with hc1def
  have hc0 : 0 ≤ c0 := ENNReal.toReal_nonneg
  have hc1 : 0 ≤ c1 := ENNReal.toReal_nonneg
  unfold packetComponentConst
  rw [← ENNReal.ofReal_toReal hC0top.ne, ← ENNReal.ofReal_toReal hC1top.ne,
    ← hc0def, ← hc1def, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith : (0:ℝ) ≤ 1 - s),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hs0,
    ← ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.toReal_ofReal hc0, ENNReal.toReal_ofReal hc1]
  congr 1
  have hstep1 : (ε ^ ((1 : ℝ) / 2) * c0) ^ (1 - s)
      = ε ^ ((1 : ℝ) / 2 * (1 - s)) * c0 ^ (1 - s) := by
    rw [Real.mul_rpow (by positivity) hc0, ← Real.rpow_mul hε0.le]
  have hstep2 : (2 * Real.pi * (ε ^ (-(1 : ℝ) / 2) * c1)) ^ s
      = ε ^ (-(1 : ℝ) / 2 * s) * (2 * Real.pi * c1) ^ s := by
    rw [show 2 * Real.pi * (ε ^ (-(1 : ℝ) / 2) * c1)
        = ε ^ (-(1 : ℝ) / 2) * (2 * Real.pi * c1) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hε0.le]
  rw [hstep1, hstep2, show (1 : ℝ) / 2 - s = (1 : ℝ) / 2 * (1 - s) + (-(1 : ℝ) / 2) * s by ring,
    Real.rpow_add hε0]
  ring

/-- `eq:packetHs`, with one explicit constant family for the whole scale interval. -/
theorem packetSobolevBound
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst f s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) := by
  intro s hs0 hs1 ε hε
  have hS := chartForce_supportedInCube hc place hε
  have hWsm := NavierStokes.PeriodicLocalization.contDiff_periodize hS
    (chartForce_smooth hf place.x₀ place.chartCenter place.T ε)
  have hWper := NavierStokes.PeriodicLocalization.unitSpatialPeriodsOn_periodize
    (chartForce f place.x₀ place.chartCenter place.T ε) univ
  have hb := (NSFormalization.Section3.T17.forceSobolevENormT_le_of_translate hs1
    (force_mem hf hc place ε hε) hWsm hWper place.chartCenter
    (periodize_chartForce f place.x₀ place.chartCenter place.T ε)).1
  refine hb.trans ?_
  have hmeas : ∀ i : Fin 3, AEStronglyMeasurable
      (fun t => NSFormalization.Paper1.periodicSobolevNorm s
        (fun x => coordinateForce
          (periodize (chartForce f place.x₀ place.chartCenter place.T ε)) i (t, x))) volume :=
    fun i => (NSFormalization.Paper1.stronglyMeasurable_periodicSobolevNorm_time s
      (NSFormalization.Source.coordinateForce_smooth hWsm i).continuous).aestronglyMeasurable
  calc
    _ ≤ ∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Paper1.periodicSobolevNorm s
        (fun x => coordinateForce
          (periodize (chartForce f place.x₀ place.chartCenter place.T ε)) i (t, x))) 1 volume :=
      NSFormalization.Paper1.PeriodicForceConvergence.eLpNorm_periodicVectorSobolevNorm_le_sum hmeas
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (ε ^ ((1 : ℝ) / 2 - s) * packetComponentConst f s i) :=
      Finset.sum_le_sum fun i _ => packet_component_bound hf hc place hε hs0 hs1 i
    _ = ENNReal.ofReal (∑ i : Fin 3, ε ^ ((1 : ℝ) / 2 - s) * packetComponentConst f s i) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        mul_nonneg (Real.rpow_nonneg hε.1.le _) (packetComponentConst_nonneg f s i))).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => packetComponentConst_nonneg f s i)
      have hA := Real.rpow_pos_of_pos hε.1 ((1 : ℝ) / 2)
      have hB := Real.rpow_pos_of_pos hε.1 ((1 : ℝ) / 2 - s)
      unfold sobolevConst
      nlinarith

end NSFormalization.Section3.T15
