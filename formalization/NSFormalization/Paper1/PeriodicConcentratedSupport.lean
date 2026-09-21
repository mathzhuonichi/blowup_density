import NSFormalization.Source.PacketScaling
import NavierStokes.PeriodicLocalization

/-!
# Eventual fixed-cube support of the concentrated compact force

The actual parabolic force uses inverse length `ε⁻¹`.  Its spatial support
therefore contracts by `ε`, independently of the physical time translation.
The compactness of the original force supplies a fixed spatial radius; no
smoothness or shrinking-support assumption is needed.
-/

noncomputable section

namespace NSFormalization.Paper1

open Set Filter NavierStokes.ProblemStatement NavierStokes.PeriodicLocalization
open NSFormalization.Source NSFormalization.Source.PacketScaling
open scoped Topology

/-- The explicit support radius of the actual inverse-scale parabolic force. -/
theorem supportedInCube_parabolicForce_inv_of_bound
    {F : VelocityField} (hc : HasCompactSupport F) {R ε : ℝ}
    (hR : ∀ z ∈ tsupport F, ‖z.2‖ ≤ R) (hε : 0 < ε) (t₀ : ℝ) :
    SupportedInCube (ε * R) (parabolicForce ε⁻¹ t₀ 0 F) := by
  intro z hz i
  obtain ⟨y, hy, rfl⟩ := parabolicForce_support hc (inv_pos.mpr hε) t₀ 0
    (subset_tsupport _ hz)
  have hyi : |y.2 i| ≤ R := by
    have hi : |y.2 i| ≤ ‖y.2‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y.2 i
    exact hi.trans (hR y hy)
  simpa only [inv_inv, zero_add, PiLp.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos hε] using mul_le_mul_of_nonneg_left hyi hε.le

/-- Any fixed positive cube contains the actual concentrated force at every
sufficiently small positive scale, with arbitrary scale-dependent time center. -/
theorem eventually_supportedInCube_parabolicForce_inv
    {F : VelocityField} (hc : HasCompactSupport F) (center : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube r (parabolicForce ε⁻¹ (center ε) 0 F) := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image continuous_snd).isBounded.exists_norm_le
  have hb : ∀ z ∈ tsupport F, ‖z.2‖ ≤ R := by
    intro z hz
    exact hR z.2 ⟨z, hz, rfl⟩
  have hlim : Tendsto (fun ε : ℝ => ε * R) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      (show Tendsto (fun ε : ℝ => ε * R) (𝓝 0) (𝓝 (0 * R)) from
        tendsto_id.mul_const R))
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * R < r :=
    hlim.eventually (gt_mem_nhds hr)
  filter_upwards [self_mem_nhdsWithin, hevent] with ε hε hsmall
  intro z hz i
  exact (supportedInCube_parabolicForce_inv_of_bound hc hb hε (center ε) z hz i).trans
    hsmall.le

/-- The fixed quarter-cube required by the periodic density bridge. -/
theorem eventually_supportedInQuarterCube_parabolicForce_inv
    {F : VelocityField} (hc : HasCompactSupport F) (center : ℝ → ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SupportedInCube (1 / 4) (parabolicForce ε⁻¹ (center ε) 0 F) :=
  eventually_supportedInCube_parabolicForce_inv hc center (by norm_num)

end NSFormalization.Paper1
