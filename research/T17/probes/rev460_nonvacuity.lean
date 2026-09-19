import NSFormalization.Section3.T17.SlabBridge2

noncomputable section
namespace NSFormalization.Section3.T17.Rev460Nonvacuity

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

/-- The continuation theorem has a concrete nonzero-reference instance with a
positive admissible scale; in particular, none of its interval hypotheses is
being used vacuously. -/
example : Nonvacuity.reference ≠ 0 ∧ ∃ D : CutoffData,
    0 < D.ε₀ ∧ D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ ∧
    LocalPotentialAPI Nonvacuity.reference 0 Nonvacuity.place.Kstar
      Nonvacuity.place.x₀ (1 / 4) Nonvacuity.place.T 1 D ∧
    Nonempty (CorrectionAPI 1 Nonvacuity.place Nonvacuity.reference (1 / 4) 1 D) := by
  obtain ⟨D, hD, hA⟩ := correctionStatementSlab'_holds
    1 0 0 0 ∅ Nonvacuity.place Nonvacuity.reference (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ _ _ => rfl) contDiff_const.contDiffOn
    (by intros; simp [Nonvacuity.reference, spatialDivergence, spatialDerivative])
    (by simp) Subset.rfl
  exact ⟨Nonvacuity.reference_nonzero, D, hD.eps_pos,
    ⟨hD.eps_pos, le_rfl⟩, hD, hA⟩

end NSFormalization.Section3.T17.Rev460Nonvacuity
