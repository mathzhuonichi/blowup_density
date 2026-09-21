import NSFormalization.Paper1.PeriodicConcentratedSupport
import NSFormalization.Source.InsertionForceConvergence

/-!
# Fixed-cube support of the actual insertion force

The background correction force inherits the support of the removal field,
which inherits the support of the rescaled spatial cutoff.  Consequently
both it and the concentrated compact packet lie in any prescribed positive
cube for all sufficiently small positive scales.  This spatial assertion
requires neither smoothness nor compactness of the temporal cutoff.
-/

noncomputable section

namespace NSFormalization.Paper1

open Set Filter NavierStokes.ProblemStatement NavierStokes.PeriodicLocalization
open NSFormalization.Source NSFormalization.Source.LocalizedInsertion
open NSFormalization.Source.PhysicalRemoval CorrectionProfile
open scoped Topology

/-- The actual force created by background removal is supported in the
spatially rescaled cutoff, including all of its differential terms. -/
theorem supportedInCube_physicalCorrectionForce_of_bound
    (ν : ℝ) (v : VelocityField) (T : ℝ) {θ : Space → ℝ} (η : ℝ → ℝ)
    (hθc : HasCompactSupport θ) {R ε : ℝ}
    (hR : ∀ y ∈ tsupport θ, ‖y‖ ≤ R) (hε : 0 < ε) :
    SupportedInCube (ε * R)
      (correctionForce ν v (physicalCorrection v 0 T θ η ε)) := by
  intro z hz i
  have hw := correctionForce_support ν v (physicalCorrection v 0 T θ η ε)
    (subset_tsupport _ hz)
  have hx := (localCorrection_support v 0
    (spatialCutoff θ 0 ε) (temporalCutoff η T ε) hw).2
  obtain ⟨y, hy, he⟩ := spatial_cutoff_support hε.ne' 0 hθc hx
  have hyi : |y i| ≤ R := by
    have hi : |y i| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact hi.trans (hR y hy)
  rw [← he]
  simpa only [spaceMap, zero_add, PiLp.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos hε] using mul_le_mul_of_nonneg_left hyi hε.le

/-- Any fixed positive cube eventually contains the actual background
correction force.  Compactness is used only for the spatial cutoff. -/
theorem eventually_supportedInCube_physicalCorrectionForce
    (ν : ℝ) (v : VelocityField) (T : ℝ) {θ : Space → ℝ} (η : ℝ → ℝ)
    (hθc : HasCompactSupport θ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube r (correctionForce ν v (physicalCorrection v 0 T θ η ε)) := by
  obtain ⟨R, hR⟩ := hθc.isCompact.isBounded.exists_norm_le
  have hlim : Tendsto (fun ε : ℝ => ε * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      (show Tendsto (fun ε : ℝ => ε * R) (𝓝 0) (𝓝 (0 * R)) from
        tendsto_id.mul_const R))
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * R < r :=
    hlim.eventually (gt_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hsmall
  intro z hz i
  exact (supportedInCube_physicalCorrectionForce_of_bound ν v T η hθc hR hε z hz i).trans
    hsmall.le

/-- The total physical insertion force has eventual fixed-cube support.
Both summands are the actual fields used by the insertion-family PDE. -/
theorem eventually_supportedInCube_insertionForce
    (ν : ℝ) (v : VelocityField) (T : ℝ) {f : VelocityField}
    (hfc : HasCompactSupport f) {θ : Space → ℝ} (η : ℝ → ℝ)
    (hθc : HasCompactSupport θ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube r (InsertionFamily.force ν f v 0 T θ η ε) := by
  filter_upwards [eventually_supportedInCube_physicalCorrectionForce ν v T η hθc hr,
    eventually_supportedInCube_parabolicForce_inv hfc (fun ε => T - ε ^ 2) hr]
    with ε hcorrection hpacket
  intro z hz i
  by_cases hw : correctionForce ν v (physicalCorrection v 0 T θ η ε) z = 0
  · have hp : parabolicForce ε⁻¹ (T - ε ^ 2) 0 f z ≠ 0 := by
      intro hp
      exact hz (by simp only [InsertionFamily.force, hw, hp, add_zero])
    exact hpacket z hp i
  · exact hcorrection z hw i

/-- The quarter-cube required for exact endpoint periodicization of the
complete insertion force. -/
theorem eventually_supportedInQuarterCube_insertionForce
    (ν : ℝ) (v : VelocityField) (T : ℝ) {f : VelocityField}
    (hfc : HasCompactSupport f) {θ : Space → ℝ} (η : ℝ → ℝ)
    (hθc : HasCompactSupport θ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube (1 / 4) (InsertionFamily.force ν f v 0 T θ η ε) :=
  eventually_supportedInCube_insertionForce ν v T hfc η hθc (by norm_num)

/-! The same correction-force support statement with an arbitrary spatial
center.  The earlier theorem is retained for the insertion convention
centered at the origin; this variant is used by the general background
endpoint adapter. -/

theorem supportedInCube_physicalCorrectionForce_of_bound_center
    (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} (η : ℝ → ℝ) (hθc : HasCompactSupport θ) {R ε : ℝ}
    (hR : ∀ y ∈ tsupport θ, ‖y‖ ≤ R) (hε : 0 < ε) :
    SupportedInCube (‖x₀‖ + ε * R)
      (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) := by
  intro z hz i
  have hw := correctionForce_support ν v (physicalCorrection v x₀ T θ η ε)
    (subset_tsupport _ hz)
  have hx := (localCorrection_support v x₀
    (spatialCutoff θ x₀ ε) (temporalCutoff η T ε) hw).2
  obtain ⟨y, hy, he⟩ := spatial_cutoff_support hε.ne' x₀ hθc hx
  have hyi : |y i| ≤ R := by
    have hi : |y i| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact hi.trans (hR y hy)
  rw [← he]
  have hxi : |x₀ i| ≤ ‖x₀‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x₀ i
  calc
    |(spaceMap ε x₀ y) i| ≤ |x₀ i| + |(ε • y) i| := by
      change |x₀ i + (ε • y) i| ≤ |x₀ i| + |(ε • y) i|
      exact norm_add_le (x₀ i : ℝ) ((ε • y) i : ℝ)
    _ ≤ ‖x₀‖ + ε * R := by
      gcongr
      simpa only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hε]
        using mul_le_mul_of_nonneg_left hyi hε.le

theorem eventually_supportedInCube_physicalCorrectionForce_center
    (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} (η : ℝ → ℝ) (hθc : HasCompactSupport θ)
    {r : ℝ} (hr : 0 < r) (hcenter : ‖x₀‖ < r) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube r (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) := by
  obtain ⟨R, hR⟩ := hθc.isCompact.isBounded.exists_norm_le
  have hlim : Tendsto (fun ε : ℝ => ε * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      (show Tendsto (fun ε : ℝ => ε * R) (𝓝 0) (𝓝 (0 * R)) from
        tendsto_id.mul_const R))
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * R < r - ‖x₀‖ :=
    hlim.eventually (gt_mem_nhds (sub_pos.mpr hcenter))
  filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hsmall
  intro z hz i
  have hbound := supportedInCube_physicalCorrectionForce_of_bound_center
    ν v x₀ T η hθc hR hε z hz i
  exact hbound.trans (by linarith)

theorem eventually_supportedInQuarterCube_physicalCorrectionForce_center
    (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} (η : ℝ → ℝ) (hθc : HasCompactSupport θ)
    (hcenter : ‖x₀‖ < 1 / 4) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube (1 / 4)
        (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) :=
  eventually_supportedInCube_physicalCorrectionForce_center ν v x₀ T η hθc
    (by norm_num) hcenter

end NSFormalization.Paper1
