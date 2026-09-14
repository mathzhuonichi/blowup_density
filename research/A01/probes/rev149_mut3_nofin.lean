import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer NEGATIVE check M3 for lane 149: delete the finiteness hypothesis `hfin` (used only in
the proof body, so `autoImplicit` cannot silently re-bind it).  EXPECTED TO FAIL. -/

noncomputable section
namespace Rev149Mut3
open Set MeasureTheory
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space)
open scoped ENNReal ContDiff

set_option autoImplicit false in
theorem reverse_MUT_nofin (q n : ℕ) (hn : n ≤ q + 1)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z) :
    (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
  have hle1 : eLpNorm (iteratedFDeriv ℝ n z) 2 volume ≤ jetSobolevENorm (q + 1) z := by
    rw [jetSobolevENorm]
    exact Finset.single_le_sum (f := fun j => eLpNorm (iteratedFDeriv ℝ j z) 2 volume)
      (fun j _ => bot_le) (Finset.mem_range.mpr (by omega))
  have hEN : eLpNorm (iteratedFDeriv ℝ n z) 2 volume
      ≤ ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z :=
    hle1.trans (jetSobolevENorm_le_sobolevENorm (q + 1) hz)
  have hrhs_top :
      ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  calc (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ (ENNReal.ofReal (jetSobolevConst (q + 1)) * sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal :=
        ENNReal.toReal_mono hrhs_top hEN
    _ = jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (jetSobolevConst_pos (q + 1)).le]

end Rev149Mut3
