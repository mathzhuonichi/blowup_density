import NSFormalization.Section4.A01.CylinderWiring

noncomputable section

namespace NSFormalization.Section4.A01.Rev192

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Substantive mutation: demand an order-`q+2` cylinder representative where the proved theorem
only supplies order `q+1`. The direct proof must fail. -/
theorem mutated_cylinder_order
    {f : SpaceTimeField} {S ν : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ q (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 2)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0 := by
  obtain ⟨U, hU0, hpairs, _hsob⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  refine ⟨U, hU0, ?_⟩
  intro q hq
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs q hq
  exact ⟨u, hU, hdiv⟩

end NSFormalization.Section4.A01.Rev192
