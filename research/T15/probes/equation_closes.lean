import NSFormalization.Section3.T15.Equation
import Bindings.Packet

/-! Instantiate all three transport conclusions on the registered nonzero
packet at viscosity one. The placement uses the cube-centre geometry of
`placement_closes.lean`, with a threshold adapted to the actual packet carrier.
The earlier geometric bump instances have no momentum/divergence clauses. -/
noncomputable section
namespace NSFormalization.Section3.T15.EquationProbe
open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped Topology

def packet := BlowupDensity.Bindings.packet 1 (by norm_num)
def center : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))
def carrier : Set Space := packet.carrier ∪ Prod.snd '' tsupport packet.force

theorem carrier_compact : IsCompact carrier :=
  packet.carrier_compact.union (packet.force_support.1.image continuous_snd)

theorem carrier_bound : ∃ R : ℝ, 0 < R ∧ ∀ y ∈ carrier, ‖y‖ ≤ R :=
  carrier_compact.isBounded.exists_pos_norm_le

def radius : ℝ := Classical.choose carrier_bound

theorem radius_pos : 0 < radius := (Classical.choose_spec carrier_bound).1

theorem norm_le_radius {y : Space} (hy : y ∈ carrier) : ‖y‖ ≤ radius :=
  (Classical.choose_spec carrier_bound).2 y hy

def threshold : ℝ := min (1 / 2) (1 / (8 * (radius + 1)))

theorem threshold_pos : 0 < threshold := by
  unfold threshold
  exact lt_min (by norm_num) (by have := radius_pos; positivity)

theorem chart_in_cube :
    closure (Metric.ball center (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine Metric.closure_ball_subset_closedBall.trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - center‖ ≤ 3 / 8 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hc := abs_spaceCoord_le_norm (x - center) i
  have hcoord : (x - center) i = x i - 1 / 2 := rfl
  rw [hcoord] at hc
  have h := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

def place : PlacementData packet.velocity packet.pressure packet.force packet.carrier where
  T := 1
  time_pos := by norm_num
  chartCenter := center
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := chart_in_cube
  x₀ := center
  x₀_mem := by simp
  Kstar := carrier
  Kstar_compact := carrier_compact
  carrier_subset := subset_union_left
  force_projection_subset := fun t x hx => Or.inr ⟨(t, x), hx, rfl⟩
  ε₀ := threshold
  eps_pos := threshold_pos
  eps_le_one := (min_le_left _ _).trans (by norm_num)
  eps_time := by
    intro ε hε
    have he : ε ≤ 1 / 2 := hε.2.trans (min_le_left _ _)
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1 / 2 + ε by linarith [hε.1])]
  eps_space := by
    intro ε hε y hy
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : center + ε • y - center = ε • y := by abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
    have hden : 0 < 8 * (radius + 1) := by have := radius_pos; positivity
    have he : ε * (8 * (radius + 1)) ≤ 1 :=
      (le_div_iff₀ hden).mp (hε.2.trans (min_le_right _ _))
    have hn := mul_le_mul_of_nonneg_left (norm_le_radius hy) hε.1.le
    nlinarith [hε.1]

/-- Concrete momentum field, at unchanged viscosity one. -/
theorem momentum : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual 1
      (periodizedScaledVelocity packet.velocity place.x₀ place.T ε)
      (normalizedScaledPressure packet.pressure place.x₀ place.T ε) t x =
      periodizedScaledForce packet.force place.x₀ place.T ε (t, x) :=
  periodized_momentum packet.carrier_compact packet.velocity_support packet.pressure_support
    packet.force_support packet.force_zero_nonpos packet.extension_navier_stokes place

/-- Concrete incompressibility field, including zero. -/
theorem divergence : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
    spatialDivergence (periodizedScaledVelocity packet.velocity place.x₀ place.T ε) t x = 0 :=
  periodized_divergence packet.carrier_compact packet.velocity_support
    packet.extension_divergence_free place

/-- Concrete initial field. -/
theorem initial : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ x : Space,
    periodizedScaledVelocity packet.velocity place.x₀ place.T ε (0, x) = 0 :=
  periodized_initial place

/-- The source packet used by the three applications is nonzero. -/
theorem packet_nonzero : ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, packet.velocity (t, x) ≠ 0 := by
  obtain ⟨t, x, ht, _, hx⟩ := packet.speed_unbounded 1 (by norm_num) 1 (by norm_num)
  refine ⟨t, ht, x, ?_⟩
  intro hzero
  rw [hzero, norm_zero] at hx
  linarith

/-- A nonzero periodized velocity occurs inside the evolution interval at an
admissible scale, so the three field checks do not only test zero slices. -/
theorem periodized_nonzero : ∃ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∃ t ∈ Ioo (0 : ℝ) place.T, ∃ x : Space,
      periodizedScaledVelocity packet.velocity place.x₀ place.T ε (t, x) ≠ 0 := by
  obtain ⟨s, hs, y, hy⟩ := packet_nonzero
  let ε := place.ε₀
  have hε : ε ∈ Ioc (0 : ℝ) place.ε₀ := ⟨place.eps_pos, le_rfl⟩
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε.1
  let t := place.T - ε ^ 2 + ε ^ 2 * s
  let x := place.x₀ + ε • y
  have ht : t ∈ Ioo (0 : ℝ) place.T := by
    dsimp [t]
    constructor <;> nlinarith [place.eps_time ε hε, mul_pos he2 hs.1,
      mul_pos he2 (sub_pos.mpr hs.2)]
  have hyK : y ∈ packet.carrier :=
    packet.velocity_support s ⟨hs.1.le, hs.2⟩ (subset_tsupport _ hy)
  have hx : x ∈ fundamentalCube := interior_subset
    (place.chartBall_in_cube (subset_closure (place.eps_space ε hε y (place.carrier_subset hyK))))
  refine ⟨ε, hε, t, ht, x, ?_⟩
  rw [velocity_singleCopy packet.carrier_compact packet.velocity_support place ε hε t ht.2 x hx]
  have hsource : scaledSourcePoint place.x₀ place.T ε (t, x) = (s, y) := by
    ext
    · dsimp [scaledSourcePoint, scaledStartTime, t]
      field_simp [hε.1.ne']
      ring
    · simp [scaledSourcePoint, x, smul_smul, hε.1.ne']
  change ε⁻¹ • zeroPastField packet.velocity (scaledSourcePoint place.x₀ place.T ε (t, x)) ≠ 0
  rw [hsource, zeroPastField_of_pos _ hs.1]
  exact smul_ne_zero (inv_ne_zero hε.1.ne') hy

end NSFormalization.Section3.T15.EquationProbe
