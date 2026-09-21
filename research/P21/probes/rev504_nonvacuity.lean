import NSFormalization.Section4.A04.EnstrophyInequality
import NSFormalization.Section4.A04.ZeroSolution

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.C01
open scoped ENNReal

namespace NSFormalization.Section4.A04

private theorem sobolevENorm_zero_toReal (s : ℝ) :
    (D01.sobolevENorm s (0 : Space → Space)).toReal = 0 := by
  change (D01.sobolevENorm s (fun _ : Space => (0 : Space))).toReal = 0
  rw [sobolevENorm_eq (D01.isSobolevDatum_zero s)]
  simp

private theorem zero_norm_bridges (t : ℝ) :
    (D01.sobolevENorm 1 (C01.slice (0 : A02.SpaceTimeField) t)).toReal ^ 2 =
        l2Sq (C01.slice (0 : A02.SpaceTimeField) t) +
          (1 / (2 * Real.pi) ^ 2) * gradientSq (C01.slice (0 : A02.SpaceTimeField) t) ∧
    (D01.sobolevENorm 2 (C01.slice (0 : A02.SpaceTimeField) t)).toReal ^ 2 ≤
        l2Sq (C01.slice (0 : A02.SpaceTimeField) t) +
          2 * (1 / (2 * Real.pi) ^ 2) * gradientSq (C01.slice (0 : A02.SpaceTimeField) t) +
          (1 / (2 * Real.pi) ^ 2) ^ 2 * laplacianSq (C01.slice (0 : A02.SpaceTimeField) t) ∧
    eLpNorm (A05.gradTensor (C01.slice (0 : A02.SpaceTimeField) t)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (gradientSq (C01.slice (0 : A02.SpaceTimeField) t))) := by
  have hz : C01.slice (0 : A02.SpaceTimeField) t = (0 : Space → Space) := rfl
  rw [hz]
  have hs1 := sobolevENorm_zero_toReal (1 : ℝ)
  have hs2 := sobolevENorm_zero_toReal (2 : ℝ)
  have hl2 : l2Sq (0 : Space → Space) = 0 := by simp [l2Sq]
  have hg : gradientSq (0 : Space → Space) = 0 := by simp [gradientSq]
  have hdir (i : Fin 3) : A05.dirDeriv i (0 : Space → Space) = 0 := by
    funext x
    simp [A05.dirDeriv]
  have hlap : laplacianSq (0 : Space → Space) = 0 := by
    have hzero : A05.lap (0 : Space → Space) = 0 := by
      funext x
      simp [A05.lap, hdir]
    rw [laplacianSq, hzero]
    simp
  have hgt : eLpNorm (A05.gradTensor (0 : Space → Space)) 2 volume = 0 := by
    have hzero : A05.gradTensor (0 : Space → Space) = 0 := by
      funext x
      apply PiLp.ext
      intro i
      simp [A05.gradTensor, hdir]
    rw [hzero]
    exact eLpNorm_zero
  rw [hs1, hs2, hl2, hg, hlap, hgt]
  norm_num

/-- Non-vacuity: the main closed-interval theorem applies to the zero solution on
the nonempty interval `[1,2] ⊂ (0,3)`. -/
example :
    ∀ t ∈ Icc (1 : ℝ) 2,
    let κ := 1 / (2 * Real.pi) ^ 2
    let Cν := (2 * κ * A05.gradientL6Const ^ (3 / 2 : ℝ)) ^ 4 /
        (κ * (1 : ℝ) / 2) ^ 3 / κ ^ 3 + (1 + (1 : ℝ)) + (1 + 2 * κ / (1 : ℝ))
    deriv (fun q =>
        (D01.sobolevENorm 1 (C01.slice (zeroSol 1 3 (by norm_num) (by norm_num)).velocity q)).toReal ^ 2) t +
        (1 : ℝ) *
          (D01.sobolevENorm 2 (C01.slice (zeroSol 1 3 (by norm_num) (by norm_num)).velocity t)).toReal ^ 2 ≤
      Cν * (1 +
        (D01.sobolevENorm 1 (C01.slice (zeroSol 1 3 (by norm_num) (by norm_num)).velocity t)).toReal ^ 2) ^ 3 +
        Cν * l2Sq (C01.slice (0 : A02.SpaceTimeField) t) := by
  let w := zeroSol 1 3 (by norm_num) (by norm_num)
  have hb (t : ℝ) := zero_norm_bridges t
  have h := enstrophy_differential_on_Icc (w := w) memForceR_zero (by norm_num)
    (r := 1) (s := 2) (by norm_num) (by norm_num)
    (fun q _ => by simpa [w] using (hb q).1)
    (fun t _ => by simpa [w] using (hb t).2.1)
    (fun t _ => by simpa [w] using (hb t).2.2)
  simpa [w] using h

end NSFormalization.Section4.A04
