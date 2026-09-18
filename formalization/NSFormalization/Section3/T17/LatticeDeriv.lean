import NSFormalization.Section3.T16.LatticeLift
noncomputable section
namespace NSFormalization.Section3.T17
open Set Filter Metric
open scoped Topology BigOperators ENNReal
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement
 theorem latticeLift_iteratedFDeriv_eq
    {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r)
    (n : ℕ) (u : Fin n → SpaceTime) :
    ‖iteratedFDeriv ℝ n (latticeLift w) (t, x) u‖ =
      ‖iteratedFDeriv ℝ n w (t, x) u‖ := by
  have hnb : {z : SpaceTime | z.2 ∈ ball x₀ r} ∈ 𝓝 (t, x) :=
    continuousAt_snd.preimage_mem_nhds (isOpen_ball.mem_nhds hx)
  have heq : latticeLift w =ᶠ[𝓝 (t, x)] w := by
    filter_upwards [hnb] with z hz
    exact latticeLift_eq_of_ball hslice hρr hz
  have heqw : latticeLift w =ᶠ[𝓝[(Set.univ : Set SpaceTime)] (t, x)] w := by simpa using heq
  have hd := heqw.iteratedFDerivWithin ℝ n
  have hd0 := hd.self_of_nhdsWithin (by simp : (t, x) ∈ (Set.univ : Set SpaceTime))
  simpa only [iteratedFDerivWithin_univ] using congrArg (fun L => ‖L u‖) hd0
 theorem latticeLift_iteratedFDeriv_norm_le_iSup
    {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r)
    (n : ℕ) (u : Fin n → SpaceTime) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ n (latticeLift w) (t, x) u‖ ≤
      ⨆ z : SpaceTime, ENNReal.ofReal ‖iteratedFDeriv ℝ n w z u‖ := by
  rw [latticeLift_iteratedFDeriv_eq hslice hρr hx n u]
  exact le_iSup (fun z : SpaceTime => ENNReal.ofReal ‖iteratedFDeriv ℝ n w z u‖) (t, x)
end NSFormalization.Section3.T17
