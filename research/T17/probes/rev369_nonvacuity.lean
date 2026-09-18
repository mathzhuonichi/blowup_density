import NSFormalization.Section3.T17.LatticeDeriv

open Set Metric
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement

noncomputable section
namespace NSFormalization.Section3.T17.Rev369

def bumpF : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def wBump : SpaceTimeField := fun z => bumpF z.2 • coordinateVector 0

theorem bump_support :
    ∀ t : ℝ, ∀ y : Space, wBump (t, y) ≠ 0 → y ∈ ball (0 : Space) (1 / 4) := by
  intro t y hy
  have hb : bumpF y ≠ 0 := by
    intro h0
    apply hy
    simp [wBump, h0]
  have hmem : y ∈ Function.support (fun z => bumpF z) := hb
  rw [bumpF.support_eq] at hmem
  exact hmem

theorem bump_nonzero : wBump (0, (0 : Space)) ≠ 0 := by
  have hf0 : bumpF (0 : Space) = 1 := by
    apply bumpF.one_of_mem_closedBall
    rw [mem_closedBall, dist_self]
    exact bumpF.rIn_pos.le
  show bumpF (0 : Space) • coordinateVector 0 ≠ 0
  rw [hf0, one_smul]
  intro hcontra
  have h1 : (coordinateVector 0 : Space) 0 = (0 : Space) 0 := by rw [hcontra]
  simp [coordinateVector] at h1

example :
    ‖iteratedFDeriv ℝ 0 (latticeLift wBump) (0, (0 : Space))
        (fun i => Fin.elim0 i)‖ =
      ‖iteratedFDeriv ℝ 0 wBump (0, (0 : Space))
        (fun i => Fin.elim0 i)‖ := by
  apply latticeLift_iteratedFDeriv_eq (w := wBump) (x₀ := (0 : Space))
    (ρ := 1 / 4) (r := 1 / 4) bump_support
  · norm_num
  · rw [mem_ball, dist_self]
    norm_num

end NSFormalization.Section3.T17.Rev369
