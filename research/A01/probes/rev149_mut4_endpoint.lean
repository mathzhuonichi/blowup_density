import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer NEGATIVE check M4 for lane 149: try to use the widened Grönwall row at the endpoint
`T₀ = T` (the `Icc 0 T` conclusion `HasAprioriBound` actually needs).  EXPECTED TO FAIL. -/

noncomputable section
namespace Rev149Mut4
open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt Cgron MemL1Hm HasSmoothSobolevPath)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open scoped ENNReal ContDiff

set_option autoImplicit false in
theorem endpoint_MUT {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {Kbnd : ℝ} (hT : 0 ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Icc (0 : ℝ) T,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0
            + (NSFormalization.Section4.A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (Cgron m ν * Kbnd) :=
  highOrder_bddAbove_of_kbnd_Icc hν ha hf hf1 w hpath hm hT (lt_irrefl T) hkbnd

end Rev149Mut4
