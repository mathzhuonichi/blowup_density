import NSFormalization.Section3.T16.LatticeLift
noncomputable section
namespace NSFormalization.Section3.T17
open Set Filter Metric
open scoped Topology BigOperators ENNReal
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement
/-- The `k = 0` fundamental-ball specialization of `latticeLift_iteratedFDeriv_eq`:
for `x ∈ ball x₀ r` the lift is the single `k = 0` copy `w`, so the derivatives
agree unshifted.  The general arbitrary-`z`, `∃ k` form is
`latticeLift_iteratedFDeriv_eq`. -/
 theorem latticeLift_iteratedFDeriv_eq_ballZero
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
/-- The fundamental-ball `ℝ≥0∞`/`⨆` corollary (from `latticeLift_iteratedFDeriv_eq_ballZero`).
The general arbitrary-`z` form is `latticeLift_iteratedFDeriv_norm_le_iSup`. -/
 theorem latticeLift_iteratedFDeriv_norm_le_iSup_ballZero
    {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r)
    (n : ℕ) (u : Fin n → SpaceTime) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ n (latticeLift w) (t, x) u‖ ≤
      ⨆ z : SpaceTime, ENNReal.ofReal ‖iteratedFDeriv ℝ n w z u‖ := by
  rw [latticeLift_iteratedFDeriv_eq_ballZero hslice hρr hx n u]
  exact le_iSup (fun z : SpaceTime => ENNReal.ofReal ‖iteratedFDeriv ℝ n w z u‖) (t, x)
/-- **U1, general form (arbitrary spacetime point).** For *every* `z : SpaceTime`,
order `n` and direction tuple `u`, the lattice lift's iterated Fréchet derivative
at `z` agrees, in operator/directional norm, with that of the single nearby
Euclidean copy `w (· - (0, latticeVector k))`:
`‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖`.

The witness `k` is existentially quantified.  When a lattice copy sits over `z`
(`∃ k, z.2 - latticeVector k ∈ ball x₀ r`) it is that copy; when `z` is away from
every copy both sides vanish and the witness is `k = 0` (the *no-copy / zero* case).
The `k = 0` fundamental-ball specialization is the earlier
`latticeLift_iteratedFDeriv_eq_ballZero`.

No smoothness is required: eventual agreement of the functions already transports
the iterated derivative (`Filter.EventuallyEq.iteratedFDeriv`), and translation
invariance is `iteratedFDeriv_comp_sub`.  The extra `hlt : ρ < r` separates the
closed support balls (radius `ρ`) from the open copy balls (radius `r`), so the
no-copy case is a genuine neighbourhood of zeros; downstream `ρ = ε·θRadius < r`
(`correction_fields_of_chart`, `hεspace`). -/
theorem latticeLift_iteratedFDeriv_eq
    {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) (hlt : ρ < r)
    (z : SpaceTime) (n : ℕ) (u : Fin n → SpaceTime) :
    ∃ k : NSFormalization.Section3.T10.PeriodicFrequency,
      ‖iteratedFDeriv ℝ n (latticeLift w) z u‖ =
        ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖ := by
  by_cases hcase :
      ∃ k : NSFormalization.Section3.T10.PeriodicFrequency,
        z.2 - latticeVector k ∈ ball x₀ r
  · -- a lattice copy sits over `z`: `latticeLift w` is that single translate near `z`
    obtain ⟨k, hk⟩ := hcase
    refine ⟨k, ?_⟩
    have hnb : {z' : SpaceTime | z'.2 - latticeVector k ∈ ball x₀ r} ∈ 𝓝 z :=
      (continuous_snd.sub continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds hk)
    have heq : latticeLift w =ᶠ[𝓝 z] fun z' => w (z' - (0, latticeVector k)) := by
      filter_upwards [hnb] with z' hz'
      have e1 : latticeLift w z' = latticeLift w (z'.1, z'.2 - latticeVector k) :=
        (isPeriodicOn_sub_latticeVector (latticeLift_periodic w) z'.1 z'.2 k).symm
      have e2 : latticeLift w (z'.1, z'.2 - latticeVector k) =
          w (z'.1, z'.2 - latticeVector k) :=
        latticeLift_eq_of_ball hslice hρr hz'
      have e3 : (z'.1, z'.2 - latticeVector k) = z' - (0, latticeVector k) := by
        have h : z' - ((0 : ℝ), latticeVector k) = (z'.1 - 0, z'.2 - latticeVector k) := rfl
        rw [h, sub_zero]
      rw [e1, e2, e3]
    have hcs : iteratedFDeriv ℝ n (fun z' : SpaceTime => w (z' - (0, latticeVector k))) z =
        iteratedFDeriv ℝ n w (z - (0, latticeVector k)) :=
      iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := w) n ((0 : ℝ), latticeVector k) z
    have hfd := ((heq.iteratedFDeriv ℝ n).self_of_nhds).trans hcs
    exact congrArg (fun L => ‖L u‖) hfd
  · -- no nearby copy: both sides vanish on a neighbourhood of `z`
    rw [not_exists] at hcase
    have hpos : (0 : ℝ) < r - ρ := sub_pos.mpr hlt
    have hzin : z.2 ∈ ball z.2 (r - ρ) := by rw [mem_ball, dist_self]; exact hpos
    have hnb : {z' : SpaceTime | z'.2 ∈ ball z.2 (r - ρ)} ∈ 𝓝 z :=
      continuousAt_snd.preimage_mem_nhds (isOpen_ball.mem_nhds hzin)
    have heqL : latticeLift w =ᶠ[𝓝 z] fun _ : SpaceTime => (0 : Space) := by
      filter_upwards [hnb] with z' hz'
      have hterm : ∀ k : NSFormalization.Section3.T10.PeriodicFrequency,
          w (z'.1, z'.2 - latticeVector k) = 0 := by
        intro k
        by_contra hne
        have hmem : z'.2 - latticeVector k ∈ ball x₀ ρ :=
          hslice z'.1 (z'.2 - latticeVector k) hne
        apply hcase k
        rw [mem_ball, dist_eq_norm] at hmem hz' ⊢
        have hrw : (z.2 - latticeVector k) - x₀ =
            ((z'.2 - latticeVector k) - x₀) - (z'.2 - z.2) := by abel
        rw [hrw]
        calc ‖((z'.2 - latticeVector k) - x₀) - (z'.2 - z.2)‖
            ≤ ‖(z'.2 - latticeVector k) - x₀‖ + ‖z'.2 - z.2‖ := norm_sub_le _ _
          _ < ρ + (r - ρ) := add_lt_add hmem hz'
          _ = r := by ring
      show (∑' k : NSFormalization.Section3.T10.PeriodicFrequency,
          w (z'.1, z'.2 - latticeVector k)) = 0
      exact (tsum_congr hterm).trans tsum_zero
    have heqR : w =ᶠ[𝓝 z] fun _ : SpaceTime => (0 : Space) := by
      filter_upwards [hnb] with z' hz'
      show w z' = 0
      by_contra hne
      have hmem : z'.2 ∈ ball x₀ ρ := hslice z'.1 z'.2 hne
      apply hcase 0
      rw [latticeVector_zero, sub_zero, mem_ball, dist_eq_norm]
      rw [mem_ball, dist_eq_norm] at hmem hz'
      have hrw : z.2 - x₀ = (z'.2 - x₀) - (z'.2 - z.2) := by abel
      rw [hrw]
      calc ‖(z'.2 - x₀) - (z'.2 - z.2)‖
          ≤ ‖z'.2 - x₀‖ + ‖z'.2 - z.2‖ := norm_sub_le _ _
        _ < ρ + (r - ρ) := add_lt_add hmem hz'
        _ = r := by ring
    have hLnorm : ‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = 0 := by
      have h0 : iteratedFDeriv ℝ n (latticeLift w) z = 0 := by
        have h := (heqL.iteratedFDeriv ℝ n).self_of_nhds
        rwa [iteratedFDeriv_fun_zero, Pi.zero_apply] at h
      rw [h0]; simp
    have hRnorm : ‖iteratedFDeriv ℝ n w z u‖ = 0 := by
      have h0 : iteratedFDeriv ℝ n w z = 0 := by
        have h := (heqR.iteratedFDeriv ℝ n).self_of_nhds
        rwa [iteratedFDeriv_fun_zero, Pi.zero_apply] at h
      rw [h0]; simp
    refine ⟨0, ?_⟩
    have hlv0 : ((0 : ℝ), latticeVector (0 : NSFormalization.Section3.T10.PeriodicFrequency)) =
        (0 : SpaceTime) := by rw [latticeVector_zero]; rfl
    rw [hlv0, sub_zero, hLnorm, hRnorm]
/-- **U1 corollary, general form.**  The `ℝ≥0∞`/`⨆` derivative bound of
`CorrectionAPI.correction_derivative_bound` (Spec.lean) transported to the lattice
lift, now for *every* spacetime point `z` (not only the fundamental ball): the
lift's directional iterated-derivative enorm at `z` is dominated by the supremum,
over all Euclidean points `z'`, of the single-copy derivative enorm.  Follows from
`latticeLift_iteratedFDeriv_eq` and `le_iSup` at the nearby copy. -/
theorem latticeLift_iteratedFDeriv_norm_le_iSup
    {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) (hlt : ρ < r)
    (z : SpaceTime) (n : ℕ) (u : Fin n → SpaceTime) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ n (latticeLift w) z u‖ ≤
      ⨆ z' : SpaceTime, ENNReal.ofReal ‖iteratedFDeriv ℝ n w z' u‖ := by
  obtain ⟨k, hk⟩ := latticeLift_iteratedFDeriv_eq hslice hρr hlt z n u
  rw [hk]
  exact le_iSup (fun z' : SpaceTime => ENNReal.ofReal ‖iteratedFDeriv ℝ n w z' u‖)
    (z - (0, latticeVector k))
end NSFormalization.Section3.T17
