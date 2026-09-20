import NSFormalization.Section4.A01.ConstructorAssembly

/-! The divergence row closes for lane 190's arbitrary smooth representative;
no pointwise identification with the raw `Lp` coercion is used. -/

noncomputable section

namespace Rev180DivergenceClosed

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement (Space spatialDivergence)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open scoped ContDiff

example {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      spatialDivergence velocity t x = 0 :=
  velocity_divergence u U hU hdiv velocity hslice hc3

end Rev180DivergenceClosed
