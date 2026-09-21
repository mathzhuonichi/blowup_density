import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.ConstructorPressure

noncomputable section

namespace NSFormalization.Section4.A01.Rev192

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Positive interface probe: the combined named export supplies every cylinder input on one
`u,U`; its all-`j` family also feeds the exact hypothesis shape of lane 190's
`exists_joint_smooth_representative`, whose representative then feeds lane 180. -/
theorem main_output_feeds_constructor
    (joint190 : ∀ {S : ℝ},
      (hS : 0 < S) →
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) →
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) →
      ∃ velocity : SpaceTimeField,
        (∀ t : Icc (0 : ℝ) S,
          (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) ∧
        ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (constructor180 : ∀ {q : ℕ} (hq : 6 ≤ q)
      {f : SpaceTimeField} (hf : D01.MemForceR f) {S ν : ℝ},
      (hν : 0 < ν) →
      (hS : 0 < S) →
      (a : SmoothL2Field Space) →
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) →
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) →
      U ⟨0, le_rfl, hS.le⟩ = a.toLp →
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) →
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) →
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) →
      (velocity : SpaceTimeField) →
      (∀ t : Icc (0 : ℝ) S,
        (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) →
      ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) →
      (ContDiffOn ℝ ∞ (pressureGradientOfVelocity ν f velocity)
          (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
        ∀ t ∈ Ico (0 : ℝ) S,
          MemLp (fun x : Space =>
            pressureGradientOfVelocity ν f velocity (t, x)) 2 volume ∧
          RadialPotential.HasSymmetricJacobian (fun x : Space =>
            pressureGradientOfVelocity ν f velocity (t, x))) →
      ∃ w : ClassicalSolutionR ν
          (fun x : Space => velocity (0, x)) f S,
        w.velocity = velocity ∧
        ∀ t : Icc (0 : ℝ) S,
          (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    {q : ℕ} (hq : 6 ≤ q) {f : SpaceTimeField} {S ν : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p))
    (hpg : ∀ velocity : SpaceTimeField,
      ContDiffOn ℝ ∞ (pressureGradientOfVelocity ν f velocity)
          (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
        ∀ t ∈ Ico (0 : ℝ) S,
          MemLp (fun x : Space =>
            pressureGradientOfVelocity ν f velocity (t, x)) 2 volume ∧
          RadialPotential.HasSymmetricJacobian (fun x : Space =>
            pressureGradientOfVelocity ν f velocity (t, x))) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp := by
  obtain ⟨U, u, hU0, hU, hdiv, hinv, hduh, hsob, hpaths⟩ :=
    constructorInputs_of_bounds hq hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := joint190 hS U hpaths
  have _ := constructor180 hq hf hν hS a u U hU0 hU hdiv hduh hinv hsob
    velocity hslice hc3 (hpg velocity)
  exact ⟨U, hU0⟩

end NSFormalization.Section4.A01.Rev192
