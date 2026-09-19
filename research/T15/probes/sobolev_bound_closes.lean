import NSFormalization.Section3.T15.SobolevBound
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The concrete packet and placement below are copied verbatim from
`energy_mixed_closes.lean`, Part 2, so this probe can run independently. -/
noncomputable section
namespace NSFormalization.Section3.T15.SobolevBoundProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15 NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source NSFormalization.Source.PacketScaling
open scoped ContDiff ENNReal Topology

/-- Centre of the fundamental cube. -/
def emCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- Spatial bump, support `closedBall 0 (1/4)`. -/
def emSpaceBump : ContDiffBump (0 : Space) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- Time bump, support `closedBall (1/2) (1/4) = [1/4,3/4] ⊆ (0,∞)`. -/
def emTimeBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A genuinely nonzero smooth spatial profile. -/
def emField : Space → Space := fun x => emSpaceBump x • coordinateVector 0

/-- The velocity packet: nonzero, smooth, vanishing at every nonpositive time. -/
def emVel : VelocityField := fun z => emTimeBump z.1 • emField z.2

/-- The force: the same time-localized bump field. -/
def emForce : VelocityField := fun z => emTimeBump z.1 • emField z.2

/-- The pressure packet. -/
def emPres : PressureField := fun z => emTimeBump z.1 * emSpaceBump z.2

def emCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem emTimeBump_eq_zero {t : ℝ} (ht : t ≤ 0) : emTimeBump t = 0 := by
  refine emTimeBump.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 1 / 2 ≤ 0)]
  change (1 / 4 : ℝ) ≤ _
  linarith

theorem emField_tsupport : tsupport emField ⊆ emCarrier := by
  have hsub : Function.support emField ⊆ Function.support (⇑emSpaceBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hzero
    exact hx (by simp [emField, hzero])
  have h : tsupport emField ⊆ tsupport (⇑emSpaceBump) := closure_mono hsub
  change tsupport emField ⊆ Metric.closedBall (0 : Space) (1 / 4)
  rwa [emSpaceBump.tsupport_eq] at h

theorem emField_contDiff : ContDiff ℝ ∞ emField :=
  emSpaceBump.contDiff.smul contDiff_const

theorem emVel_contDiff : ContDiff ℝ ∞ emVel :=
  (emTimeBump.contDiff.comp contDiff_fst).smul (emField_contDiff.comp contDiff_snd)

theorem emVel_zeroPast : zeroPastField emVel = emVel := by
  funext z
  by_cases h : 0 < z.1
  · exact zeroPastField_of_pos emVel h z.2
  · rw [zeroPastField_of_nonpos emVel (not_lt.1 h)]
    show (0 : Space) = emTimeBump z.1 • emField z.2
    rw [emTimeBump_eq_zero (not_lt.1 h), zero_smul]

theorem emVel_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField emVel) (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := by
  rw [emVel_zeroPast]
  exact emVel_contDiff.contDiffOn

theorem emVel_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => emVel (t, x)) ⊆ emCarrier := by
  intro t _
  refine Subset.trans (closure_mono ?_) emField_tsupport
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  exact hx (by simp [emVel, hzero])

/-- The time-localized bump field has compact spacetime support inside strictly
positive times, and its spatial projection stays in the carrier. -/
theorem emForce_tsupport :
    tsupport emForce ⊆ tsupport (⇑emTimeBump) ×ˢ tsupport emField := by
  have hsub : Function.support emForce ⊆
      Function.support (⇑emTimeBump) ×ˢ Function.support emField := by
    intro z hz
    simp only [Function.mem_support] at hz
    constructor
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [emForce, hzero])
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [emForce, hzero])
  refine Subset.trans (closure_mono hsub) ?_
  rw [closure_prod_eq]
  exact Subset.rfl

theorem emForce_contDiff : ContDiff ℝ ∞ emForce := emVel_contDiff

theorem emForce_compactSupport :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport emForce := by
  have hts := emForce_tsupport
  have htime : tsupport (⇑emTimeBump) = Metric.closedBall (1 / 2 : ℝ) (1 / 4) :=
    emTimeBump.tsupport_eq
  constructor
  · refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hts
    exact (htime ▸ (isCompact_closedBall (1 / 2 : ℝ) (1 / 4))).prod
      ((isCompact_closedBall (0 : Space) (1 / 4)).of_isClosed_subset
        (isClosed_tsupport _) emField_tsupport)
  · intro z hz
    obtain ⟨hz1, _⟩ := hts hz
    rw [htime, Metric.mem_closedBall, Real.dist_eq] at hz1
    refine ⟨?_, mem_univ _⟩
    have := abs_le.1 hz1
    simp only [mem_Ioi]
    linarith [this.1]

theorem em_chartBall_in_cube :
    closure (Metric.ball emCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - emCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - emCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - emCenter) i
    have h2 : (x - emCenter) i = x i - emCenter i := rfl
    rw [h2] at h
    linarith
  have hc : emCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem em_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ emCarrier,
    emCenter + ε • y ∈ Metric.ball emCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : emCenter + ε • y - emCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [emCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have h1 : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

/-- The canonical placement datum on this geometry. -/
def emPlacement : PlacementData emVel emPres emForce emCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := emCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := em_chartBall_in_cube
  x₀ := emCenter
  x₀_mem := by simp
  Kstar := emCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    exact emField_tsupport (emForce_tsupport h).2
  ε₀ := 1 / 2
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have hsquare : ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hε.1, hε.2]
    nlinarith
  eps_space := em_eps_space


-- The target fields, closed directly over the raw field placement data.
example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s (periodizedScaledForce f place.x₀ place.T ε) := by
  exact forceSobolev_memLp hf hc place

example (f : VelocityField) : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst f s := by
  exact sobolevConst_pos f

example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst f s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) := by
  exact packetSobolevBound hf hc place

-- Reverse conformance against the literal record projections.
example {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    {M D : ℝ} {place : PlacementData u p f K} (A : ScalingAPI (ν := ν) u p f K M D place) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s (periodizedScaledForce f place.x₀ place.T ε) := by
  exact A.forceSobolev_memLp

example {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    {M D : ℝ} {place : PlacementData u p f K} (A : ScalingAPI (ν := ν) u p f K M D place) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
        ENNReal.ofReal (A.sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) := by
  exact A.packetSobolevBound

example {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    {M D : ℝ} {place : PlacementData u p f K} (A : ScalingAPI (ν := ν) u p f K M D place) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < A.sobolevConst s := by
  exact A.sobolevConst_pos

/-- The same nonzero bump packet, at an admissible scale and all orders in [0,1]. -/
theorem nonzero_packet_sobolev :
    emForce (1/2, 0) ≠ 0 ∧
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      MemForceSobolevT 1 s (periodizedScaledForce emForce emPlacement.x₀ emPlacement.T (1/2)) ∧
      forceSobolevENormT 1 s (periodizedScaledForce emForce emPlacement.x₀ emPlacement.T (1/2)) ≤
        ENNReal.ofReal (sobolevConst emForce s *
          ((1/2 : ℝ) ^ ((1 : ℝ)/2) + (1/2 : ℝ) ^ ((1 : ℝ)/2 - s))) := by
  constructor
  · have hb : emSpaceBump (0 : Space) = 1 :=
      emSpaceBump.one_of_mem_closedBall (by norm_num [emSpaceBump])
    have ht : emTimeBump (1/2 : ℝ) = 1 :=
      emTimeBump.one_of_mem_closedBall (by norm_num [emTimeBump])
    change emTimeBump (1/2 : ℝ) • emField (0 : Space) ≠ 0
    rw [ht, one_smul]
    simp [emField, hb, coordinateVector]
  · intro s hs0 hs1
    have hε : (1/2 : ℝ) ∈ Ioc (0 : ℝ) emPlacement.ε₀ := by
      change (1/2 : ℝ) ∈ Ioc (0 : ℝ) (1/2)
      norm_num
    exact ⟨forceSobolev_memLp emForce_contDiff emForce_compactSupport emPlacement s hs0 hs1 _ hε,
      packetSobolevBound emForce_contDiff emForce_compactSupport emPlacement s hs0 hs1 _ hε⟩

end NSFormalization.Section3.T15.SobolevBoundProbe
