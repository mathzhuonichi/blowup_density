import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer probe for lane 149, note N1: the widened Grönwall rows can take `hkbnd` on an
*intermediate* horizon `Ico 0 T₁` (`T₀ < T₁ ≤ T`) instead of the full `Ico 0 T`, with the same
two-line proof.  This is strictly more general (`T₁ := T` gives the lane's statements) and lets a
caller keep `Kbnd = 256·R²·T₁` from `kbnd_of_sup_bound` at horizon `T₁` instead of `256·R²·T`. -/

noncomputable section
namespace Rev149Gen
open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt Cgron MemL1Hm HasSmoothSobolevPath)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open scoped ENNReal ContDiff

set_option autoImplicit false in
theorem highOrder_bddAbove_of_kbnd_Icc' {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ T₁ Kbnd : ℝ} (hT₀ : 0 ≤ T₀) (hT₀T₁ : T₀ < T₁) (hT₁T : T₁ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₁,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Icc (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0
            + (NSFormalization.Section4.A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (Cgron m ν * Kbnd) := by
  have hbase := highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm
    (lt_of_le_of_lt hT₀ hT₀T₁) hT₁T hkbnd
  intro t ht
  exact hbase t ⟨ht.1, lt_of_le_of_lt ht.2 hT₀T₁⟩

end Rev149Gen
