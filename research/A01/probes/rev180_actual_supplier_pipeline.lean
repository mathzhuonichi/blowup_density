import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.JointRepresentative

/-! Positive probe for the landed 192 → 190 → pressure → 180 pipeline.  Lane
192's family-returning theorem and lane 190 are real theorem calls.  The sole
open supplier is `PressureSupply`, scoped to those selected witnesses. -/

noncomputable section

namespace Rev180ActualSupplierPipeline

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

example {q : ℕ} (hq : 6 ≤ q)
    {f : NSFormalization.Section4.A02.SpaceTimeField}
    (hf : NSFormalization.Section4.D01.MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (NSFormalization.Section4.C01.forcePath (S := S) hf)
      (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) (R p))
    (h189 : ∀
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (hpairs : ∀ p (hp : 6 ≤ p),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hp
              (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
                (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                  (S := S) hf) p))
            (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
      (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
      (velocity : NSFormalization.Section4.A02.SpaceTimeField)
      (hslice : ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
      (hc3 : ContDiffOn ℝ ∞ velocity
        (Ico (0 : ℝ) S ×ˢ (univ : Set Space))),
      PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (velocity : NSFormalization.Section4.A02.SpaceTimeField)
      (w : NSFormalization.Section4.A02.ClassicalSolutionR ν
        (fun x : Space => velocity (0, x)) f S),
      w.velocity = velocity ∧
      ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t) := by
  obtain ⟨U, _hU0, hpairs, hpaths⟩ :=
    cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ :=
    exists_joint_smooth_representative hS U hpaths
  have hsupply := h189 U hpairs hpaths velocity hslice hc3
  obtain ⟨w, hw, hslice'⟩ :=
    carrierConstructorFull_of_hyps hq hν hS f hf a ha
      U hpairs hpaths velocity hslice hc3 hsupply
  exact ⟨U, velocity, w, hw, hslice'⟩

end Rev180ActualSupplierPipeline
