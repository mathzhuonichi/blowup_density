import NSFormalization.Section4.A01.ComplementPath

noncomputable section
namespace NSFormalization.Section4.A01
namespace ComplementPath

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {f : A02.SpaceTimeField} {ν S : ℝ}
variable (hf : MemForceR f) (hν : 0 < ν) (hS : 0 < S)
variable (a : SmoothL2Field Space)
variable (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
variable (hpairs : ∀ q (hq : 6 ≤ q),
  ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
    (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
    (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
    (∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
    ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)

-- Substantive mutation: widen every asserted time-regularity interval from
-- `[0,S]` to `[-1,S]`. Reusing the production proof must fail at this change.
example :
    ∃ w : ℝ → (Space → Space),
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (-1 : ℝ) S) ∧
        ∀ t : Icc (-1 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (⇑(residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A) := by
  exact exists_complement_paths hf hν hS a U hpairs

end ComplementPath
end NSFormalization.Section4.A01
