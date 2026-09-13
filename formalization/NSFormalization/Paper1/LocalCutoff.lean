import NSFormalization.Paper1.RadialPotential
import NSFormalization.Source.BackgroundCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! Concrete compact cutoff and time-dependent divergence-free background removal. -/
noncomputable section
namespace NSFormalization.Paper1
open NavierStokes NavierStokes.ProblemStatement Set Filter Metric
open scoped ContDiff Topology

/-- A compact set strictly inside a ball admits a smooth compact cutoff with
an open plateau containing that set. -/
theorem exists_spatial_cutoff {K : Set Space} (hK : IsCompact K)
    {x₀ : Space} {R : ℝ} (hR : 0 < R) (hKR : K ⊆ ball x₀ R) :
    ∃ χ : Space → ℝ, ∃ O : Set Space,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ ball x₀ R ∧
      IsOpen O ∧ K ⊆ O ∧ EqOn χ (fun _ => 1) O := by
  obtain ⟨r₁, hr₁, hK₁⟩ := exists_pos_lt_subset_ball hR hK.isClosed hKR
  obtain ⟨r₂, hr₁₂, hr₂R⟩ := exists_between hr₁.2
  let f : ContDiffBump x₀ := ⟨r₁, r₂, hr₁.1, hr₁₂⟩
  refine ⟨f, ball x₀ r₁, f.contDiff, f.hasCompactSupport, ?_, isOpen_ball, hK₁, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball hr₂R
  · intro x hx
    exact f.one_of_mem_closedBall (ball_subset_closedBall hx)

/-- A temporal bump equal to one on the active interval [T−δ,T+δ] and
supported inside (T−2δ,T+2δ), for δ>0. -/
theorem exists_temporal_cutoff (T δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      EqOn η (fun _ => 1) (Icc (T - δ) (T + δ)) ∧
      tsupport η ⊆ Ioo (T - 2 * δ) (T + 2 * δ) := by
  let f : ContDiffBump T := ⟨δ, 3 * δ / 2, hδ, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · intro t ht
    apply f.one_of_mem_closedBall
    change dist t T ≤ δ
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  · rw [f.tsupport_eq]
    intro t ht
    change dist t T ≤ 3 * δ / 2 at ht
    rw [Real.dist_eq, abs_le] at ht
    constructor <;> linarith [ht.1, ht.2]

/-- The actual spacetime correction, formed from the actual radial potential. -/
def localCorrection (v : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) : VelocityField :=
  fun z => -SpatialCurl.spatialCurl
    (fun p => (η p.1 * χ p.2) • RadialPotential.timePotential v x₀ p) z

theorem localCorrection_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space)
    {χ : Space → ℝ} {η : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (localCorrection v x₀ χ η) :=
  (SpatialCurl.contDiff_spatialCurl
    (((hη.comp contDiff_fst).mul (hχ.comp contDiff_snd)).smul
      (RadialPotential.timePotential_contDiff hv x₀)) (by simp)).neg

theorem localCorrection_divergence {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space)
    {χ : Space → ℝ} {η : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (t : ℝ) (x : Space) : spatialDivergence (localCorrection v x₀ χ η) t x = 0 := by
  have hp : ContDiff ℝ ∞
      (fun y : Space => -((η t * χ y) • RadialPotential.timePotential v x₀ (t, y))) :=
    ((contDiff_const.mul hχ).smul
      ((RadialPotential.timePotential_contDiff hv x₀).comp
        (contDiff_const.prodMk contDiff_id))).neg
  have heq : (fun y => localCorrection v x₀ χ η (t, y)) =
      SpatialCurl.curl (fun y => -((η t * χ y) • RadialPotential.timePotential v x₀ (t, y))) := by
    funext y
    exact (NSFormalization.Source.curl_neg _ y).symm
  change (∑ i : Fin 3, (fderiv ℝ (fun y => localCorrection v x₀ χ η (t, y)) x
    (coordinateVector i)) i) = 0
  rw [heq]
  exact SpatialCurl.divergence_curl (hp.contDiffAt.of_le (by simp))

theorem localCorrection_eq_neg {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ t x, spatialDivergence v t x = 0) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) (t : ℝ) (x : Space)
    (hη : η t = 1) (hχ : ∀ᶠ y in 𝓝 x, χ y = 1) :
    localCorrection v x₀ χ η (t, x) = -v (t, x) := by
  have hcut : ∀ᶠ y in 𝓝 x, η t * χ y = 1 := by
    filter_upwards [hχ] with y hy
    simp [hη, hy]
  change -SpatialCurl.curl (fun y => (η t * χ y) • RadialPotential.timePotential v x₀ (t, y)) x = _
  rw [SpatialCurl.curl_cutoff_eq hcut]
  exact congrArg Neg.neg (congrFun (RadialPotential.spatialCurl_timePotential hv hdiv x₀) (t, x))

theorem localCorrection_slice (v : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) (t : ℝ) (x : Space) :
    localCorrection v x₀ χ η (t, x) =
      Source.cutoffCorrection χ (fun y => η t • RadialPotential.timePotential v x₀ (t, y)) x := by
  unfold localCorrection Source.cutoffCorrection SpatialCurl.spatialCurl
  congr 2
  funext y
  simp only [smul_smul, mul_comm]

theorem localCorrection_zero_of_time (v : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) (t : ℝ) (x : Space) (ht : η t = 0) :
    localCorrection v x₀ χ η (t, x) = 0 := by
  simp [localCorrection, SpatialCurl.spatialCurl, ht]

theorem localCorrection_support (v : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ) :
    tsupport (localCorrection v x₀ χ η) ⊆ tsupport η ×ˢ tsupport χ := by
  apply closure_minimal _ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
  rintro ⟨t, x⟩ hw
  constructor
  · by_contra ht
    exact hw (localCorrection_zero_of_time v x₀ χ η t x
      (image_eq_zero_of_notMem_tsupport ht))
  · by_contra hx
    apply hw
    rw [localCorrection_slice]
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx (Source.cutoffCorrection_support χ _ h)

theorem localCorrection_compact (v : VelocityField) (x₀ : Space)
    (χ : Space → ℝ) (η : ℝ → ℝ)
    (hχ : HasCompactSupport χ) (hη : HasCompactSupport η) :
    HasCompactSupport (localCorrection v x₀ χ η) :=
  (hη.prod hχ).of_isClosed_subset (isClosed_tsupport _)
    (localCorrection_support v x₀ χ η)

/-- A full smooth, compact spacetime removal around an arbitrary compact
spatial packet support. All cutoffs and the radial potential are constructed.
The globally smooth reference can be a smooth extension of a reference on the
fixed compact time window where the correction is supported. -/
theorem exists_local_background_removal {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ t x, spatialDivergence v t x = 0)
    {K : Set Space} (hK : IsCompact K) {x₀ : Space} {R : ℝ}
    (hR : 0 < R) (hKR : K ⊆ ball x₀ R) (T δ : ℝ) (hδ : 0 < δ) :
    ∃ w : VelocityField, ∃ O : Set Space,
      ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      (∀ t x, spatialDivergence w t x = 0) ∧
      tsupport w ⊆ Ioo (T - 2 * δ) (T + 2 * δ) ×ˢ ball x₀ R ∧
      IsOpen O ∧ K ⊆ O ∧
      (∀ t ∈ Icc (T - δ) (T + δ), ∀ x ∈ O,
        ∀ᶠ y in 𝓝 x, v (t, y) + w (t, y) = 0) := by
  obtain ⟨χ, O, hχsmooth, hχcompact, hχsupport, hO, hKO, hχone⟩ :=
    exists_spatial_cutoff hK hR hKR
  obtain ⟨η, hηsmooth, hηcompact, hηone, hηsupport⟩ := exists_temporal_cutoff T δ hδ
  refine ⟨localCorrection v x₀ χ η, O, localCorrection_smooth hv x₀ hχsmooth hηsmooth,
    localCorrection_compact v x₀ χ η hχcompact hηcompact,
    localCorrection_divergence hv x₀ hχsmooth, ?_, hO, hKO, ?_⟩
  · exact (localCorrection_support v x₀ χ η).trans (Set.prod_mono hηsupport hχsupport)
  · intro t ht x hx
    filter_upwards [hO.mem_nhds hx] with y hy
    have hχy : ∀ᶠ z in 𝓝 y, χ z = 1 := by
      filter_upwards [hO.mem_nhds hy] with z hz
      exact hχone hz
    rw [localCorrection_eq_neg hv hdiv x₀ χ η t y (hηone ht) hχy]
    exact add_neg_cancel _

end NSFormalization.Paper1
