import NSFormalization.Source.CompactSlabSobolev
import NSFormalization.Source.InsertionFamily

/-!
# Physical Sobolev persistence for the actual insertion

On every closed presingular slab, the inserted velocity has continuous L2
spatial jets whenever the reference velocity is realized by such a path.
The perturbation hypotheses are derived from the insertion properties.
-/
noncomputable section
open Set MeasureTheory EulerLpTranslation
open scoped ContDiff

namespace NSFormalization.Source.InsertionSobolev
open NavierStokes.ProblemStatement

/-- The actual insertion preserves every continuous physical L2 jet of the
reference path on a closed presingular slab, including its endpoints. -/
theorem exists_inserted_path {ν r T τ b : ℝ} {x₀ : Space}
    {v g V G : VelocityField} {q Q : PressureField}
    (hb : b < T)
    (hvs : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ))
    (h : InsertionFamily.InsertionProperties ν v q g x₀ r T τ V Q G)
    (A : Icc (0 : ℝ) b → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hAv : ∀ t : Icc (0 : ℝ) b, ∀ x, (A t).field x = v (t, x)) :
    ∃ B : Icc (0 : ℝ) b → SmoothL2Field Space,
      (∀ t : Icc (0 : ℝ) b, ∀ x, (B t).field x = V (t, x)) ∧
      ∀ n, Continuous (fun t => (B t).jetLp n) := by
  have hsub : Icc (0 : ℝ) b ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
    fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hb⟩, hz.2⟩
  have hw : ContDiffOn ℝ ∞ (fun z => V z - v z)
      (Icc (0 : ℝ) b ×ˢ (univ : Set Space)) :=
    (h.1.mono hsub).sub (hvs.mono hsub)
  obtain ⟨L, hLc, _, hLs⟩ := h.2.2.2.2.2.1
  exact CompactSlabSobolev.exists_inserted_path hw hLc
    (fun t ht => (hLs t ⟨ht.1, ht.2.trans_lt hb⟩).1)
    A hA hAv (fun _ _ => rfl)

end NSFormalization.Source.InsertionSobolev
