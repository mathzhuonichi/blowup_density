import NSFormalization.Paper3.AdmissibleForce
import NSFormalization.Paper3.CompactForceAdmissibility
import NSFormalization.Paper3.CompactSobolevRealization
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! Compact physical forces embed in the coherent positive-time algebraic
force class. The target is the complex Hilbert interface, not yet the fully
identified real manuscript class: real-subspace, angular-norm, and one-sided
smoothness identification obligations remain. No restriction on background
support, divergence, or values at time zero is imposed here. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source
open scoped ContDiff ENNReal SchwartzMap

/-- The distribution of a physical compact force, independent of Sobolev order. -/
def compactForceDistribution (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) : ℝ → ForceDistribution :=
  fun t i => (NavierStokesR3.CompactSchwartz.ofCompactSupport
    (fun x => coordinateForce F i (t, x))
    ((coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id))
    (compact_spatial_slice (coordinateForce_compact hc i) t) : 𝓢'(Space, ℂ))

theorem compactForceDistribution_apply (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    compactForceDistribution F hF hc t i ψ =
      ∫ x : Space, ψ x * coordinateForce F i (t, x) := by
  rw [compactForceDistribution, SchwartzMap.coe_apply]
  rfl

/-- Coherent order-specific witnesses for the single physical distribution path. -/
def compactForceDatum (m : ℕ) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) : ℝ → ForceDatum m :=
  fun t i => compactSobolevTimeSlice (m : ℝ) (coordinateForce F i)
    (coordinateForce_smooth hF i) (coordinateForce_compact hc i) t

theorem forceRealization_compactForceDatum (m : ℕ) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (t : ℝ) :
    forceRealization m (compactForceDatum m F hF hc t) =
      compactForceDistribution F hF hc t := by
  funext i
  exact sobolevRealization_compactFourierLp (m : ℝ) _ _ _

theorem admissibleForce_compactForceDistribution (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    AdmissibleForce (compactForceDistribution F hF hc) := by
  intro m
  refine ⟨compactForceDatum m F hF hc, fun t _ =>
    forceRealization_compactForceDatum m F hF hc t, ?_, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro i
    exact contDiff_compactSobolevTimeSlice (m : ℝ)
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i)
  · apply memLp_pi_iff.mpr
    intro i
    exact (memLp_compactSobolevTimeSlice (m : ℝ)
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) 1).restrict _
  · apply memLp_pi_iff.mpr
    intro i
    exact (memLp_compactSobolevTimeSlice (m : ℝ)
      (coordinateForce_smooth hF i) (coordinateForce_compact hc i) 2).restrict _

theorem admissibleForce_add_compact {g : ℝ → ForceDistribution}
    (hg : AdmissibleForce g) (F : VelocityField)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    AdmissibleForce (g + compactForceDistribution F hF hc) :=
  admissibleForce_add hg (admissibleForce_compactForceDistribution F hF hc)

theorem add_compactForceDistribution_sub (g : ℝ → ForceDistribution)
    (F : VelocityField) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (g + compactForceDistribution F hF hc) - g = compactForceDistribution F hF hc :=
  add_sub_cancel_left g _

theorem add_compactForceDistribution_sub_apply (g : ℝ → ForceDistribution)
    (F : VelocityField) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ((g + compactForceDistribution F hF hc) - g) t i ψ =
      ∫ x : Space, ψ x * coordinateForce F i (t, x) := by
  rw [add_compactForceDistribution_sub]
  exact compactForceDistribution_apply F hF hc t i ψ

end NSFormalization.Paper3
