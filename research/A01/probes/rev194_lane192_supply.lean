import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.ComplementPath

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- The producer at lane 192 feeds lane 194 without adapting or strengthening its
-- all-order cylinder-pair conjunct.
example {f : A02.SpaceTimeField} {ν S : ℝ}
    (hf : MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (w : ℝ → (Space → Space)),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) := by
  obtain ⟨U, hU0, hpairs, _hsob⟩ :=
    cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨w, hpaths, _hidentity⟩ :=
    exists_complement_paths hf hν hS a U hpairs
  exact ⟨U, w, hU0, hpaths⟩

end NSFormalization.Section4.A01
