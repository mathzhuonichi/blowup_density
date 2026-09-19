import NSFormalization.Section3.T17.Correction
import NSFormalization.Section3.T17.ForceVolume
import NSFormalization.Section3.T17.Energy
import NSFormalization.Section3.T17.Mixed
import NSFormalization.Section3.T17.Sobolev

/-! T17 U12: the 45-field correction at the concrete T16 lattice lift.
G1 is an explicit global smoothness premise. G3 uses raw packet fields.
The completed G4 includes packet support and the requested ball's chart inclusion.
No field of the reconciled API is changed. -/
noncomputable section
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology BigOperators

/-- The completed G4 hypothesis block; `correctionStatement` remains unchanged. -/
def correctionStatementAmended : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

/-- Bundle every estimate at the concrete `correctionData`, using the T16
record for the cutoff premises and placement for the cube and scale bounds. -/
def correctionAPI_of_smooth (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (place : PlacementData u p f K)
    {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (r δ : ℝ)
    (hν : 0 < ν) (hr : 0 < r) (hr2 : r < 1 / 2)
    (hvper : IsPeriodicOn univ v)
    (hball : ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius)
    (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (hpot : LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ
      (correctionData v place.x₀ place.T θ η O θR ε₀))
    (hle : ε₀ ≤ place.ε₀) :
    CorrectionAPI ν place v r δ (correctionData v place.x₀ place.T θ η O θR ε₀) := by
  let D := correctionData v place.x₀ place.T θ η O θR ε₀
  have hθ := hpot.theta_smooth
  have hη := hpot.eta_smooth
  have hθc := hpot.theta_compactSupport
  have hηc := hpot.eta_compactSupport
  have hθsupp := hpot.theta_support
  have hηsupp := hpot.eta_support
  have hεtime := hpot.eps_time
  have hεspace := hpot.eps_space
  have hε₀ : ε₀ ≤ 1 := hle.trans place.eps_le_one
  have hcube : closure (ball place.x₀ r) ⊆ interior fundamentalCube :=
    (closure_mono hball).trans place.chartBall_in_cube
  exact {
    potential := hpot
    localization := localizationAPI
    viscosity_pos := hν
    radius_pos := hr
    ball_in_chart := hball
    eps_le_placement := hle
    reference_periodic := hvper
    correction_profile_smooth := correction_profile_smooth hv place.x₀ place.T D hθ hη
    correction_profile_support := correction_profile_support hv place.x₀ place.T D hθ hη hθsupp hηsupp
    correction_profile_uniform := correction_profile_uniform hv place.x₀ place.T D hθ hη hθc hηc hε₀
    correctionProfileConst := correctionProfileConst hv place.x₀ place.T hθ hη hθc hηc
    correctionProfileConst_nonneg := correctionProfileConst_nonneg hv place.x₀ place.T hθ hη hθc hηc
    force_profile_smooth := force_profile_smooth ν hv place.x₀ place.T D hθ hη
    force_profile_support := force_profile_support ν hv place.x₀ place.T D hθ hη hθsupp hηsupp
    force_profile_uniform := force_profile_uniform ν hv place.x₀ place.T D hθ hη hθc hηc hε₀
    forceProfileConst := forceProfileConst ν hv place.x₀ place.T hθ hη hθc hηc
    forceProfileConst_nonneg := forceProfileConst_nonneg ν hv place.x₀ place.T hθ hη hθc hηc
    correction_profile_identity := correction_profile_identity hv hpot
    force_profile_identity := force_profile_identity ν hv hpot
    force_smooth := force_smooth ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
    force_periodic := force_periodic ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
    force_support := force_support ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
    force_time_length := force_time_length ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
    force_spatial_memLp := force_spatial_memLp ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace
    spatialVolumeConst := spatialVolumeConst θR
    spatialVolumeConst_nonneg := spatialVolumeConst_nonneg hpot.theta_radius_pos.le
    force_spatial_volume := force_spatial_volume ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hpot.theta_radius_pos.le hεtime hεspace
    correctionDerivConst := correctionDerivConst hv place.x₀ place.T hθ hη hθc hηc
    correctionDerivConst_nonneg := correctionDerivConst_nonneg hv place.x₀ place.T hθ hη hθc hηc
    forceDerivConst := forceDerivConst ν hv place.x₀ place.T hθ hη hθc hηc
    forceDerivConst_nonneg := forceDerivConst_nonneg ν hv place.x₀ place.T hθ hη hθc hηc
    correction_derivative_bound := correction_derivative_bound hv place.x₀ place.T O θR ε₀ r hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεspace
    force_derivative_bound := force_derivative_bound ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace
    correction_slice_memLp := correction_slice_memLp hv place.x₀ place.T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    correction_gradient_memLp := correction_gradient_memLp hv place.x₀ place.T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    energyConst := energyConst hv place.x₀ place.T hθ hη hθc hηc
    energyConst_nonneg := energyConst_nonneg hv place.x₀ place.T hθ hη hθc hηc
    correction_energy_bound := correction_energy_bound hv place.x₀ place.T O hθ hη hθc hηc hθsupp hηsupp hcube hε₀ hεspace
    mixedConst := mixedConst ν hv place.x₀ place.T hθ hη hθc hηc
    mixedConst_nonneg := mixedConst_nonneg ν hv place.x₀ place.T hθ hη hθc hηc
    sobolevConst := sobolevConst ν hv place.x₀ place.T hθ hη hθc hηc
    sobolevConst_pos := sobolevConst_pos ν hv place.x₀ place.T hθ hη hθc hηc
    force_mixed_bound := force_mixed_bound ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace hcube hε₀
    forceSobolev_memLp := forceSobolev_memLp ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace
    force_sobolev_bound := force_sobolev_bound ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace }

/-- Choose T16's cutoffs and shrink its threshold to `min ε₁ place.ε₀`.
This retains all T16 bounds and yields both placement compatibility and `ε₀ ≤ 1`. -/
theorem correctionStatementAmended_holds : correctionStatementAmended := by
  intro ν u p f K place v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
  obtain ⟨θR, θ, O, hθR, hθ, hθc, hθsupp, hO, hKO, hθone, hθrange⟩ :=
    exists_originCutoff place.Kstar_compact
  obtain ⟨η, hη, hηc, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₁, hε₁, ht, hs⟩ := exists_threshold hθR hr place.time_pos hδ
  let ε₀ := min ε₁ place.ε₀
  have hε₀ : 0 < ε₀ := lt_min hε₁ place.eps_pos
  have htime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ :=
    fun ε hε => ht ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r :=
    fun ε hε => hs ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hpot := localPotentialAPI v u place.Kstar place.x₀ r place.T δ θ η O θR ε₀
    hr2 place.Kstar_compact hper hv.contDiffOn hdiv
    (fun t ht => (hsupp t ht).trans place.carrier_subset)
    hθ hθc hθrange hO hKO hθone hθR hθsupp hη hηc hηrange hηone hηsupp
    hε₀ htime hspace
  exact ⟨correctionData v place.x₀ place.T θ η O θR ε₀, hpot,
    ⟨correctionAPI_of_smooth ν place hv r δ hν hr hr2 hper hball θ η O θR ε₀ hpot
      (min_le_right _ _)⟩⟩

namespace Nonvacuity

def centre : Space := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

theorem chart_in_cube :
    closure (ball centre (1 / 4 : ℝ)) ⊆ interior fundamentalCube := by
  intro y hy
  have hnorm : ‖y - centre‖ ≤ 1 / 4 :=
    mem_closedBall_iff_norm.mp (closure_ball_subset_closedBall hy)
  rw [interior_fundamentalCube]
  intro i
  have hc := (PiLp.norm_apply_le (y - centre) i).trans hnorm
  change ‖y i - (1 / 2 : ℝ)‖ ≤ 1 / 4 at hc
  rw [Real.norm_eq_abs, abs_le] at hc
  constructor <;> linarith

def place : PlacementData 0 0 0 ∅ where
  T := 1
  time_pos := by norm_num
  chartCenter := centre
  chartRadius := 1 / 4
  chartRadius_pos := by norm_num
  chartBall_in_cube := chart_in_cube
  x₀ := centre
  x₀_mem := by simp
  Kstar := ∅
  Kstar_compact := isCompact_empty
  carrier_subset := Subset.rfl
  force_projection_subset := by simp
  ε₀ := 1 / 4
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have := hε.1
    have := hε.2
    nlinarith
  eps_space := by simp

def reference : SpaceTimeField := fun _ => coordinateVector 0

theorem reference_nonzero : reference ≠ 0 := by
  intro h
  have hv := congrFun h (0, 0)
  have hc := congrArg (fun x : Space => x (0 : Fin 3)) hv
  norm_num [reference, coordinateVector] at hc

/-- A nonzero smooth periodic reference at the cube centre, with positive
viscosity, radius, margin and an admissible scale in the resulting full API. -/
theorem nonvacuous_correction :
    reference ≠ 0 ∧ ∃ D : CutoffData,
      0 < D.ε₀ ∧ D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ ∧
      LocalPotentialAPI reference 0 place.Kstar place.x₀ (1 / 4) place.T 1 D ∧
      Nonempty (CorrectionAPI 1 place reference (1 / 4) 1 D) := by
  obtain ⟨D, hD, hA⟩ := correctionStatementAmended_holds 1 0 0 0 ∅ place reference
    (1 / 4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ _ _ => rfl) contDiff_const
    (by intros; simp [reference, spatialDivergence, spatialDerivative])
    (by simp) (by exact Subset.rfl)
  exact ⟨reference_nonzero, D, hD.eps_pos, ⟨hD.eps_pos, le_rfl⟩, hD, hA⟩

end Nonvacuity

end NSFormalization.Section3.T17
