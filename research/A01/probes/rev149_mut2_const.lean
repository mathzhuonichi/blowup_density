import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer NEGATIVE check M2 for lane 149: replace the constant `jetSobolevConst (q+1)` by `1`
in `eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal`, keeping the lane's proof.  EXPECTED TO FAIL. -/

noncomputable section
namespace Rev149Mut2
open Set MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space)
open scoped ENNReal ContDiff

set_option autoImplicit false in
theorem reverse_MUT (q n : ℕ) (hn : n ≤ q + 1)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hfin : sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤) :
    (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ 1 * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
  have hle1 : eLpNorm (iteratedFDeriv ℝ n z) 2 volume ≤ jetSobolevENorm (q + 1) z := by
    rw [jetSobolevENorm]
    exact Finset.single_le_sum (f := fun j => eLpNorm (iteratedFDeriv ℝ j z) 2 volume)
      (fun j _ => bot_le) (Finset.mem_range.mpr (by omega))
  have hEN : eLpNorm (iteratedFDeriv ℝ n z) 2 volume
      ≤ ENNReal.ofReal 1 * sobolevENorm ((q + 1 : ℕ) : ℝ) z :=
    hle1.trans (jetSobolevENorm_le_sobolevENorm (q + 1) hz)
  have hrhs_top : ENNReal.ofReal 1 * sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ (ENNReal.ofReal 1 * sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal :=
        ENNReal.toReal_mono hrhs_top hEN
    _ = 1 * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]

end Rev149Mut2
