import NSFormalization.Section3.T24.Multiple

/-! Ub1–Ub3 of `prop:multiple`, `03-torus.tex:697-712`. -/
noncomputable section
namespace NSFormalization.Section3.T24
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

/-- Raw packet clauses consumed by T15, and the prescribed regions
(`03-torus.tex:697-706`). No placement or solution is assumed. -/
structure RegionsData (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) (M E : ℝ) where
  packet : NSFormalization.Section4.I03.PacketData u K M E
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K
  pressure_smooth : ContDiffOn ℝ ∞ (zeroPastField p) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  force_smooth : ContDiff ℝ ∞ f
  force_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f
  force_zero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0
  momentum : ∀ t : ℝ, t < 1 → ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x)
  divergence : ∀ t : ℝ, t < 1 → ∀ x : Space, spatialDivergence (zeroPastField u) t x = 0
  blowup : SpeedUnboundedAtOne u
  T : ℝ
  hT : 0 < T
  N : ℕ
  N_pos : 0 < N
  regionCenter : Fin N → Space
  regionRadius : Fin N → ℝ
  regionRadius_pos : ∀ j, 0 < regionRadius j
  region_interior : ∀ j,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ interior fundamentalCube
  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))

namespace RegionsData
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

/-- `03-torus.tex:701-705`: lane 459's compact carrier, with a threshold
adapted to the prescribed radius. -/
def placement (j : Fin d.N) : PlacementData u p f K where
  T := d.T
  time_pos := d.hT
  chartCenter := d.regionCenter j
  chartRadius := d.regionRadius j
  chartRadius_pos := d.regionRadius_pos j
  chartBall_in_cube := d.region_interior j
  x₀ := d.regionCenter j
  x₀_mem := Metric.mem_ball_self (d.regionRadius_pos j)
  Kstar := placementCarrier K f
  Kstar_compact := placementCarrier_compact d.packet.carrier_compact d.force_support.1
  carrier_subset := subset_union_left
  force_projection_subset := fun t x hx => Or.inr ⟨(t, x), hx, rfl⟩
  ε₀ := min (min (1 / 2) (d.T / 4))
    (d.regionRadius j / (2 * (placementRadius d.packet.carrier_compact d.force_support.1 + 1)))
  eps_pos := by
    have := placementRadius_pos d.packet.carrier_compact d.force_support.1
    have := d.regionRadius_pos j
    have := d.hT
    positivity
  eps_le_one := (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  eps_time := by
    intro ε hε
    have he : ε ≤ 1 / 2 := hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have ht : ε ≤ d.T / 4 := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    nlinarith [hε.1, mul_nonneg hε.1.le (sub_nonneg.mpr he)]
  eps_space := by
    intro ε hε y hy
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hε.1]
    have hR := placementRadius_pos d.packet.carrier_compact d.force_support.1
    have hden : 0 < 2 * (placementRadius d.packet.carrier_compact d.force_support.1 + 1) := by positivity
    have he := (le_div_iff₀ hden).mp (hε.2.trans (min_le_right _ _))
    have hn := mul_le_mul_of_nonneg_left
      (placement_norm_le_radius d.packet.carrier_compact d.force_support.1 hy) hε.1.le
    have hr := d.regionRadius_pos j
    nlinarith

/-- `03-torus.tex:721`: the shared horizon. -/
theorem placement_time : ∀ j, (d.placement j).T = d.T := fun _ => rfl

/-- `03-torus.tex:701-705`: the prescribed chart. -/
theorem placement_chart : ∀ j,
    (d.placement j).chartCenter = d.regionCenter j ∧
    (d.placement j).chartRadius = d.regionRadius j := fun _ => ⟨rfl, rfl⟩

/-- `03-torus.tex:701-706`: full T15 scaling at each placement. -/
def scaling (j : Fin d.N) : ScalingAPI (ν := ν) u p f K M E (d.placement j) :=
  scalingAPI d.packet d.pressure_support d.pressure_smooth d.force_smooth
    d.force_support d.force_zero d.momentum d.divergence d.blowup (d.placement j)

/-- `03-torus.tex:703-704`: choose the admissible endpoint. -/
def ε (j : Fin d.N) : ℝ := (d.placement j).ε₀

/-- `03-torus.tex:703-704`: positivity and admissibility. -/
theorem eps_admissible : ∀ j, d.ε j ∈ Ioc (0 : ℝ) (d.placement j).ε₀ :=
  fun j => ⟨(d.placement j).eps_pos, le_rfl⟩

/-- `03-torus.tex:702`: the strict time smallness. -/
theorem eps_time : ∀ j, d.ε j ^ 2 < d.T := by
  intro j
  have h := (d.placement j).eps_time (d.ε j) (d.eps_admissible j)
  change 2 * d.ε j ^ 2 < d.T at h
  nlinarith [sq_nonneg (d.ε j)]

/-- `03-torus.tex:706-712`: select the actual T15 solution. -/
def component (j : Fin d.N) : ClassicalSolutionT ν (0 : SpatialField)
    (periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j)) d.T :=
  Classical.choose ((d.scaling j).solution (d.ε j) (d.eps_admissible j))

/-- `03-torus.tex:706-712`: both selected fields are pinned. -/
theorem component_pin : ∀ j,
    (d.component j).velocity = periodizedScaledVelocity u (d.placement j).x₀ d.T (d.ε j) ∧
    (d.component j).pressure = normalizedScaledPressure p (d.placement j).x₀ d.T (d.ε j) :=
  fun j => Classical.choose_spec ((d.scaling j).solution (d.ε j) (d.eps_admissible j))

/-- `03-torus.tex:701-712`: velocity vanishes on the cube outside its ball. -/
theorem component_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) → (d.component j).velocity (t, x) = 0 := by
  intro j t ht x hx hout
  rw [(d.component_pin j).1]
  have hcopy := (d.scaling j).velocity_singleCopy (d.ε j) (d.eps_admissible j) t ht.2 x hx
  rw [d.placement_time j] at hcopy
  rw [hcopy]
  by_contra hne
  apply hout
  exact affineImage_subset_ball (d.eps_admissible j) (d.placement j).eps_space
    (scaledVelocity_tsupp_subset (d.eps_admissible j).1 d.packet.carrier_compact
      d.packet.support (d.placement j).carrier_subset ht.2 (subset_tsupport (fun y => scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, y)) hne))

/-- `03-torus.tex:701-712`: force support, at every real time. -/
theorem component_force_support : ∀ j, ∀ t : ℝ, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) →
      periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0 := by
  intro j t x hx hout
  have hcopy := (d.scaling j).force_singleCopy (d.ε j) (d.eps_admissible j) t x hx
  rw [d.placement_time j] at hcopy
  rw [hcopy]
  by_contra hne
  apply hout
  exact affineImage_subset_ball (d.eps_admissible j) (d.placement j).eps_space
    (scaledForce_tsupp_subset (d.eps_admissible j).1 (d.placement j).Kstar_compact
      d.force_support (d.placement j).force_projection_subset t (subset_tsupport (fun y => scaledForce f (d.placement j).x₀ d.T (d.ε j) (t, y)) hne))

end RegionsData
end NSFormalization.Section3.T24
