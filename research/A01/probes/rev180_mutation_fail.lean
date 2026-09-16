import NSFormalization.Section4.A01.ConstructorAssembly

/-! Reviewer mutation: flip the time sign in the main slice identity.  This is
substantive—the clamped carrier at `-t` need not represent `U t`—and the
original theorem must not prove it. -/

noncomputable section

namespace Rev180MutationFail

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (ClassicalSolutionR SpaceTimeField)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open scoped ContDiff

example {q : ℕ} {S ν : ℝ} (hS : 0 < S)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (f velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (G : SpaceTimeField)
    (hG_int : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x))
    (hG :
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) S,
        MemLp (fun x : Space => G (t, x)) 2 volume ∧
        RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))) :
    ∃ w : ClassicalSolutionR ν
        (fun x : Space => velocity (0, x)) f S,
      w.velocity = velocity ∧
      ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => w.velocity (-t.1, x)) =ᵐ[volume] ⇑(U t) := by
  exact carrierConstructor_of_localTheory hS u U hU hdiv f velocity hslice hsob hc3
    G hG_int hG

end Rev180MutationFail
