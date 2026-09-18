import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T13.TorusIdentity

noncomputable section
namespace NSFormalization.Section3.T12
open Set MeasureTheory
open scoped ENNReal BigOperators
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13

/-- The API norm is definitionally the Haar norm of the canonical lift. -/
theorem periodicLpENorm_eq_eLpNorm_torusLift {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (v : NavierStokes.ProblemStatement.Space → E) :
    periodicLpENorm p v = eLpNorm (torusLift v) p periodicTorusMeasure := rfl

/-- A field supported in the cube has the same norm after restriction. -/
theorem eLpNorm_restrict_eq_of_support {E : Type*} [NormedAddCommGroup E]
    (w : NavierStokes.ProblemStatement.Space → E) (hw : Function.support w ⊆ interior fundamentalCube)
    (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume := by
  apply MeasureTheory.eLpNorm_restrict_eq_of_support_subset
  exact hw.trans interior_subset

/-- The same support transfer for vector-valued fields. -/
theorem eLpNorm_restrict_eq_of_support_vector
    (w : NavierStokes.ProblemStatement.Space → WithLp 2 (Fin 3 → ℝ))
    (hw : Function.support w ⊆ interior fundamentalCube) (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume := by
  exact eLpNorm_restrict_eq_of_support w hw p

/-- Haar and cube norms for a periodic field, under the corresponding norm-density identity.
The density hypothesis is the exact measure-theoretic residue of the fundamental-domain argument. -/
theorem eLpNorm_torusLift_eq_restrict_of_lintegral
    {E : Type*} [NormedAddCommGroup E] (v : NavierStokes.ProblemStatement.Space → E)
    (hv : IsPeriodicSpatial v) (p : ℝ≥0∞)
    (hlin : (∫⁻ z : PeriodicTorus, ‖torusLift v z‖ₑ ^ p.toReal ∂periodicTorusMeasure) =
      ∫⁻ x in fundamentalCube, ‖v x‖ₑ ^ p.toReal ∂(volume : Measure NavierStokes.ProblemStatement.Space))
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (torusLift v) p periodicTorusMeasure =
      eLpNorm v p (volume.restrict fundamentalCube) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm hp0 hpt]
  exact congrArg (fun x : ℝ≥0∞ => x ^ (1 / p.toReal)) hlin

end NSFormalization.Section3.T12
