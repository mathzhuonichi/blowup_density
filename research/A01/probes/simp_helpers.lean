import NSFormalization.Section4.A01.RadialPotential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
namespace NSFormalization.Section4.A01.Probe

open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace

-- Candidate A': fderiv_apply_component via EuclideanSpace.proj, closing with rfl
theorem fderiv_apply_component_A {G : Space → Space} {x : Space}
    (hG : DifferentiableAt ℝ G x) (v : Space) (b : Fin 3)
    {H : Space → ℝ} (hH : H = fun y : Space => (G y) b) :
    (fderiv ℝ G x v) b = fderiv ℝ H x v := by
  have heq : H = ⇑(EuclideanSpace.proj b) ∘ G := hH
  rw [heq, ((EuclideanSpace.proj b).hasFDerivAt.comp x hG.hasFDerivAt).fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

end NSFormalization.Section4.A01.Probe
