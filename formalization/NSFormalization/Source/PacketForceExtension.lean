import NSFormalization.Source.PacketPressure
import NavierStokes.R3CompactCandidate

/-! # Smooth compact extension of the force by zero into the past -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace NSFormalization.Source.PacketForceExtension
open NavierStokes.ProblemStatement

def zeroPast (f : VelocityField) : VelocityField := fun z => if 0 < z.1 then f z else 0

/-- The quiet positive interval makes the past-zero extension smooth at time
zero. Only future smoothness is required from the original force. -/
theorem zeroPast_smooth {f : VelocityField} {ε : ℝ} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hq : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, f (t, x) = 0) :
    ContDiff ℝ ∞ (zeroPast f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases ht : 0 < z.1
  · have heq : zeroPast f =ᶠ[𝓝 z] f := by
      filter_upwards [((isOpen_lt continuous_const continuous_fst).mem_nhds ht)] with y hy
      simp [zeroPast, hy]
    exact (hf.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem)).congr_of_eventuallyEq heq
  · have heq : zeroPast f =ᶠ[𝓝 z] (fun _ => 0) := by
      have hz : z.1 < ε := lt_of_le_of_lt (le_of_not_gt ht) hε
      filter_upwards [((isOpen_lt continuous_fst continuous_const).mem_nhds hz)] with y hy
      by_cases hy0 : 0 < y.1
      · simp [zeroPast, hy0, hq y.1 ⟨hy0, hy⟩ y.2]
      · simp [zeroPast, hy0]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Uniform compact spatial support and finite future time support become
actual compact spacetime support after extension by zero into the past. -/
theorem zeroPast_compact {f : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hs : NavierStokes.CompactSpatialForceDecay.SupportedIn K f)
    (htime : CompactFutureTimeSupport f) : HasCompactSupport (zeroPast f) := by
  obtain ⟨T, hT, ht⟩ := htime
  apply HasCompactSupport.intro (isCompact_Icc.prod hK)
    (K := Icc (0 : ℝ) T ×ˢ K)
  intro z hz
  by_cases hpos : 0 < z.1
  · simp only [zeroPast, if_pos hpos]
    by_cases hupper : z.1 ≤ T
    · have hx : z.2 ∉ K := fun hx => hz ⟨⟨hpos.le, hupper⟩, hx⟩
      exact hs z.1 hpos.le z.2 hx
    · exact ht z.1 (le_of_lt (lt_of_not_ge hupper)) z.2
  · simp [zeroPast, hpos]

/-- The extended force has its entire closed support at strictly positive time,
thanks to the initial quiet interval. -/
theorem zeroPast_support_positive {f : VelocityField} {ε : ℝ} (hε : 0 < ε)
    (hq : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, f (t, x) = 0) :
    ∀ z ∈ tsupport (zeroPast f), 0 < z.1 := by
  have hs : tsupport (zeroPast f) ⊆ {z : SpaceTime | ε ≤ z.1} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_fst)
    intro z hz
    by_contra hn
    have ht : z.1 < ε := lt_of_not_ge hn
    by_cases hp : 0 < z.1
    · exact hz (by simp [zeroPast, hp, hq z.1 ⟨hp, ht⟩ z.2])
    · exact hz (by simp [zeroPast, hp])
  intro z hz
  exact hε.trans_le (hs hz)

/-- Changing only the past force preserves every compact candidate property;
the PDE is required only at strictly positive times. -/
theorem zeroPast_properties {u f : VelocityField} {p : PressureField} {ε : ℝ}
    (h : NavierStokes.R3CompactCandidate.Properties u p f) (hε : 0 < ε)
    (hq : ∀ t ∈ Ioo (0 : ℝ) ε, ∀ x, f (t, x) = 0) :
    NavierStokes.R3CompactCandidate.Properties u p (zeroPast f) := by
  refine ⟨h.velocity_smooth, h.pressure_smooth,
    (zeroPast_smooth hε h.force_smooth hq).contDiffOn,
    h.velocity_support, h.pressure_support, ?_, h.zero_initial_velocity, ?_,
    h.divergence_free, ?_, h.speed_unbounded⟩
  · obtain ⟨K, hK, hs⟩ := h.force_support
    refine ⟨K, hK, ?_⟩
    intro t ht x hx
    by_cases hp : 0 < t
    · simp [zeroPast, hp, hs t ht x hx]
    · simp [zeroPast, hp]
  · obtain ⟨T, hT, hs⟩ := h.force_time_support
    refine ⟨T, hT, ?_⟩
    intro t ht x
    by_cases hp : 0 < t
    · simp [zeroPast, hp, hs t ht x]
    · simp [zeroPast, hp]
  · intro t ht x
    simpa [zeroPast, ht.1] using h.navier_stokes t ht x

end NSFormalization.Source.PacketForceExtension
