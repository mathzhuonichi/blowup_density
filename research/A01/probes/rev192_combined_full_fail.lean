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

/- Positive regression check: the combined export retains angular invariance, the exact Duhamel
equation, and all-`j` datum paths for the same `u,U`. -/
example {q : ℕ} (hq : 6 ≤ q) {f : SpaceTimeField} {S ν : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) ∧
      ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  exact constructorInputs_of_bounds hq hf hν hS a ha R hb

example {q : ℕ} (hq : 6 ≤ q) {f : SpaceTimeField} {S ν : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBoundInv hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) ∧
      ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  exact constructorInputs_of_boundsInv hq hf hν hS a ha R hb

end NSFormalization.Section4.A01.Rev192
