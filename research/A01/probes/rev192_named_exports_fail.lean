import NSFormalization.Section4.A01.CylinderWiring

noncomputable section

namespace NSFormalization.Section4.A01.Rev192

open Set NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- This intentionally fails: the two requested named exports choose independent `U`s, so the
`hsob` output from the first cannot be applied to the `U` used by `hU`/`hdiv` from the second. -/
theorem named_exports_do_not_feed_one_constructor
    (constructor180 : ∀ {q : ℕ} {S : ℝ},
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) →
      (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) →
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) →
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) → True)
    {q : ℕ} (hq : 6 ≤ q) {f : SpaceTimeField} {S ν : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) : True := by
  obtain ⟨Uhsob, _hU0a, hsob⟩ := hsob_of_bounds hf hν hS a ha R hb
  obtain ⟨u, Upair, _hU0b, hU, hdiv⟩ := hU_hdiv_of_bounds hq hf hν hS a ha R hb
  exact constructor180 u Upair hU hdiv hsob

end NSFormalization.Section4.A01.Rev192
