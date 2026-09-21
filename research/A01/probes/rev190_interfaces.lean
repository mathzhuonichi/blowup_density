import NSFormalization.Section4.A01.JointRepresentative

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerCylinderSobolevSpace
  EulerLiftedGradientSpace EulerQuadraticSource EulerVolterraConvolution
open scoped ContDiff Topology

/- Lane 180's consumer can destruct the result as `⟨velocity, hslice, hc3⟩`. -/
example {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∃ velocity : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  obtain ⟨velocity, hslice, hc3⟩ :=
    exists_joint_smooth_representative hS U hpaths
  exact ⟨velocity, hslice, hc3⟩

/- Lane 192's all-`j,m` `hsob` output is definitionally the `hpaths` input. -/
example {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hsob : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∃ velocity : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) :=
  exists_joint_smooth_representative hS U hsob

/- Lane 178's `hall` shape is consumed token-for-token. -/
example {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq f) u₀ u t) :
    ∃ velocity : SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S,
        (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
      ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) :=
  exists_joint_smooth_representative_of_hall hν hS U hall

end
