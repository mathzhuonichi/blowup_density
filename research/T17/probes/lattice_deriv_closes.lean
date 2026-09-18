import NSFormalization.Section3.T17.LatticeDeriv

/-! Lane 369 (r1) probe — non-vacuity of the general `∃ k` lattice-lift derivative
bridge on the nonzero bump of `research/T16/probes/lattice_lift_closes.lean`,
exercised at a point **outside** the fundamental cube `ball 0 (1/2)`.

`z = (0, latticeVector k₁)` with `k₁ = (1,0,0)` sits at spatial distance `1` from
the origin (outside `ball 0 (1/2)`) yet a lattice copy is centred there, so the
`∃ k` bridge returns that copy and the lift is genuinely nonzero at `z`
(`lift_nonzero_offcube`).  Radii `ρ = 1/4 < r = 1/2` with `r + ρ = 3/4 ≤ 1`. -/

namespace NSFormalization.Section3.T17.Probe369
open Set Metric NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement
open scoped Topology BigOperators ENNReal

noncomputable section

/-- The reviewer bump (`research/T16` probe): nonzero, each spatial slice
supported in `ball 0 (1/4)`. -/
def bumpF : ContDiffBump (0 : Space) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def wBump : SpaceTimeField := fun z => bumpF z.2 • coordinateVector 0

theorem bump_support :
    ∀ (t : ℝ) (y : Space), wBump (t, y) ≠ 0 → y ∈ ball (0 : Space) (1 / 4) := by
  intro t y hy
  have hb : bumpF y ≠ 0 := fun h0 => hy (by simp [wBump, h0])
  have hmem : y ∈ Function.support (fun z => bumpF z) := hb
  rw [bumpF.support_eq] at hmem
  exact hmem

theorem bump_nonzero : wBump (0, (0 : Space)) ≠ 0 := by
  have hf0 : bumpF (0 : Space) = 1 := by
    apply bumpF.one_of_mem_closedBall
    rw [mem_closedBall, dist_self]; exact bumpF.rIn_pos.le
  show bumpF (0 : Space) • coordinateVector 0 ≠ 0
  rw [hf0, one_smul]
  intro hcontra
  have h1 : (coordinateVector 0 : Space) 0 = (0 : Space) 0 := by rw [hcontra]
  simp [coordinateVector] at h1

/-- A copy centre outside the fundamental ball `ball 0 (1/2)`. -/
def k₁ : NSFormalization.Section3.T10.PeriodicFrequency := ![1, 0, 0]

/-- Non-vacuity: the lift is genuinely nonzero at the off-cube copy centre
`latticeVector k₁` (periodicity collapses it to the `k = 0` bump value at 0). -/
theorem lift_nonzero_offcube : latticeLift wBump (0, latticeVector k₁) ≠ 0 := by
  have hper : latticeLift wBump (0, latticeVector k₁) = latticeLift wBump (0, (0 : Space)) := by
    have h := isPeriodicOn_sub_latticeVector (latticeLift_periodic wBump) 0 (latticeVector k₁) k₁
    rw [sub_self] at h
    exact h.symm
  rw [hper]
  have hx0 : (0 : Space) ∈ ball (0 : Space) (1 / 2 : ℝ) := by rw [mem_ball, dist_self]; norm_num
  rw [latticeLift_eq_of_ball bump_support (by norm_num) hx0]
  exact bump_nonzero

/-- **The general `∃ k` shifted-copy derivative equality at an off-cube point.** -/
example (n : ℕ) (u : Fin n → SpaceTime) :
    ∃ k : NSFormalization.Section3.T10.PeriodicFrequency,
      ‖iteratedFDeriv ℝ n (latticeLift wBump) (0, latticeVector k₁) u‖ =
        ‖iteratedFDeriv ℝ n wBump ((0, latticeVector k₁) - (0, latticeVector k)) u‖ :=
  latticeLift_iteratedFDeriv_eq_shift (r := (1 / 2 : ℝ)) bump_support (by norm_num)
    (by norm_num) (0, latticeVector k₁) n u

/-- The general `ℝ≥0∞`/`⨆` corollary applies off-cube too. -/
example (n : ℕ) (u : Fin n → SpaceTime) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ n (latticeLift wBump) (0, latticeVector k₁) u‖ ≤
      ⨆ z' : SpaceTime, ENNReal.ofReal ‖iteratedFDeriv ℝ n wBump z' u‖ :=
  latticeLift_iteratedFDeriv_norm_le_iSup' (r := (1 / 2 : ℝ)) bump_support (by norm_num)
    (by norm_num) (0, latticeVector k₁) n u

/-- The `k = 0` fundamental-ball form (earlier theorem) still closes on the bump. -/
example (n : ℕ) (u : Fin n → SpaceTime) {x : Space} (hx : x ∈ ball (0 : Space) (1 / 2)) :
    ‖iteratedFDeriv ℝ n (latticeLift wBump) (0, x) u‖ =
      ‖iteratedFDeriv ℝ n wBump (0, x) u‖ :=
  latticeLift_iteratedFDeriv_eq bump_support (by norm_num) hx n u

end

end NSFormalization.Section3.T17.Probe369
