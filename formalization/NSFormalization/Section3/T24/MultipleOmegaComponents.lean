import NSFormalization.Section3.T24.MultipleOmega
import NSFormalization.Section3.T23.Triple

/-! P5.1, `paper/revised/sections/03-torus.tex:512,517,520`:
"Fix finitely many disjoint interior balls"; "In a bounded domain its boundary
condition is homogeneous no-slip." "Apply ... to each building block with
start time T − ε_j²." Raw packet construction, without a background. -/
noncomputable section
namespace NSFormalization.Section3.T24
open NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff Topology

/-- Raw packet clauses consumed by T15, and the prescribed regions
(`paper/revised/sections/03-torus.tex:511-520`). No placement or solution is assumed. -/
structure RegionsOmegaData (ν : ℝ) (u : VelocityField) (p : PressureField)
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
  Ω : Set Space
  hΩ : IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty
  T : ℝ
  hT : 0 < T
  N : ℕ
  N_pos : 0 < N
  regionCenter : Fin N → Space
  regionRadius : Fin N → ℝ
  regionRadius_pos : ∀ j, 0 < regionRadius j
  region_interior : ∀ j,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ Ω
  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))

namespace RegionsOmegaData
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsOmegaData ν u p f K M E)

/-- Prescribed cube-free placement at the center of each ball. -/
def placement (j : Fin d.N) : DomainPlacementData u p f K :=
  domainPlacementData d.packet.carrier_compact d.force_support.1
    (d.regionCenter j) (d.regionRadius j) (d.regionRadius_pos j)
    (d.region_interior j) (d.regionCenter j)
    (Metric.mem_ball_self (d.regionRadius_pos j)) d.T d.hT

theorem placement_time : ∀ j, (d.placement j).T = d.T := fun _ => rfl
theorem placement_chart : ∀ j,
    (d.placement j).chartCenter = d.regionCenter j ∧
    (d.placement j).chartRadius = d.regionRadius j := fun _ => ⟨rfl, rfl⟩

def ε (j : Fin d.N) : ℝ := (d.placement j).ε₀

theorem eps_admissible : ∀ j, d.ε j ∈ Ioc (0 : ℝ) (d.placement j).ε₀ :=
  fun j => ⟨(d.placement j).eps_pos, le_rfl⟩

theorem eps_time : ∀ j, d.ε j ^ 2 < d.T := by
  intro j
  have h := (d.placement j).eps_time (d.ε j) (d.eps_admissible j)
  change 2 * d.ε j ^ 2 < d.T at h
  nlinarith [sq_nonneg (d.ε j)]

theorem raw_velocity_smooth (j : Fin d.N) :
    ContDiffOn ℝ ∞ (scaledVelocity u (d.placement j).x₀ d.T (d.ε j))
      (Iio d.T ×ˢ (univ : Set Space)) :=
  NSFormalization.Section4.I03.scaled_smoothOn d.packet _ (d.eps_admissible j).1

theorem raw_pressure_smooth (j : Fin d.N) :
    ContDiffOn ℝ ∞ (scaledPressure p (d.placement j).x₀ d.T (d.ε j))
      (Iio d.T ×ˢ (univ : Set Space)) := by
  have h := NSFormalization.Source.PacketScaling.dilate_smoothOn ((d.ε j)⁻¹ ^ 2)
    (inv_pos.mpr (d.eps_admissible j).1) (d.T - d.ε j ^ 2) (d.placement j).x₀
    d.pressure_smooth
  have he : (d.T - d.ε j ^ 2) + (((d.ε j)⁻¹) ^ 2)⁻¹ = d.T := by
    simp only [inv_pow, inv_inv, sub_add_cancel]
  rw [he] at h
  exact h

theorem raw_velocity_slab (j : Fin d.N) :
    SmoothOnClosedSlab (Ico 0 d.T) d.Ω (scaledVelocity u (d.placement j).x₀ d.T (d.ε j)) :=
  ⟨Iio d.T ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    fun _ hz => ⟨hz.1.2, mem_univ _⟩, d.raw_velocity_smooth j⟩

theorem raw_pressure_slab (j : Fin d.N) :
    SmoothOnClosedSlab (Ico 0 d.T) d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j)) :=
  ⟨Iio d.T ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    fun _ hz => ⟨hz.1.2, mem_univ _⟩, d.raw_pressure_smooth j⟩

theorem raw_initial (j : Fin d.N) (x : Space) :
    scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (0, x) = 0 :=
  scaledVelocity_slice_eq_zero (by have := d.eps_time j; linarith) x

theorem raw_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) →
    scaledVelocity u (d.placement j).x₀ d.T (d.ε j) (t, x) = 0 := by
  intro j t ht x hout
  by_contra hne
  apply hout
  exact affineImage_subset_ball (d.eps_admissible j) (d.placement j).eps_space
    (scaledVelocity_tsupp_subset (d.eps_admissible j).1 d.packet.carrier_compact
      d.packet.support (d.placement j).carrier_subset ht.2 (subset_tsupport _ hne))

theorem component_force_support : ∀ j, ∀ t : ℝ, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) →
      scaledForce f (d.placement j).x₀ d.T (d.ε j) (t, x) = 0 := by
  intro j t x hout
  by_contra hne
  apply hout
  exact affineImage_subset_ball (d.eps_admissible j) (d.placement j).eps_space
    (scaledForce_tsupp_subset (d.eps_admissible j).1 (d.placement j).Kstar_compact
      d.force_support (d.placement j).force_projection_subset t (subset_tsupport _ hne))

def component (j : Fin d.N) : ClassicalSolutionOmega ν d.Ω (0 : SpatialField)
    (scaledForce f (d.placement j).x₀ d.T (d.ε j)) d.T where
  velocity := scaledVelocity u (d.placement j).x₀ d.T (d.ε j)
  pressure := domainNormalizePressure d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j))
  horizon_pos := d.hT
  velocity_smooth := d.raw_velocity_slab j
  pressure_smooth := (d.raw_pressure_slab j).domainNormalizePressure d.hΩ.2.1 d.hΩ.1.measurableSet
  initial := fun x _ => d.raw_initial j x
  divergence := fun t ht x _ => scaled_divergence d.divergence (d.eps_admissible j).1 _ ht.2 x
  momentum := by
    intro t ht x _
    rw [residual_domainNormalizePressure]
    exact scaled_momentum d.force_zero d.momentum (d.eps_admissible j).1 _ ht.2 x
  no_slip := by
    intro t ht x hx
    apply d.raw_support j t ht x
    intro hb
    have hn : x ∉ d.Ω := by
      simpa [d.hΩ.1.interior_eq] using hx.2
    exact hn (d.region_interior j (subset_closure hb))
  pressure_gauge := fun t ht => domainNormalizePressure_integral d.hΩ.1 d.hΩ.2.1 d.hΩ.2.2
    ((d.raw_pressure_slab j).integrableOn_slice d.hΩ.2.1 ht)

theorem component_pin : ∀ j,
    (d.component j).velocity = scaledVelocity u (d.placement j).x₀ d.T (d.ε j) ∧
    (d.component j).pressure = domainNormalizePressure d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j)) :=
  fun _ => ⟨rfl, rfl⟩

theorem component_support : ∀ j, ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    x ∉ Metric.ball (d.regionCenter j) (d.regionRadius j) → (d.component j).velocity (t, x) = 0 :=
  d.raw_support

end RegionsOmegaData
end NSFormalization.Section3.T24
