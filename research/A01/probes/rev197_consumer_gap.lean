import NSFormalization.Section4.A01.LerayBridge

-- Revised positive consumer probe. The old independent arbitrary A / fc
-- binders could not imply this conclusion. Canonical supply closes it.
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NavierStokes.ProblemStatement NSFormalization.Paper3 NSFormalization.Section4.D01
open NSFormalization.Source NSFormalization.Source.OrdinaryCylinderDescent
open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerLpTranslation EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open EulerSobolevLaplacian EulerSobolevHeatGenerator EulerMeanSmoothRepresentative
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Replay the exact fix6 export at the hard ceiling.
set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : A02.SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
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
    (velocity : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    {m : ℕ} (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q) (Classical.choose (hpairs q hq)) t)) (R t)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0
            (ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩) := by
  exact hprojected_of_cylinder'' hq hν hS f hf a ha U hpairs hpaths
    velocity hslice hc3 hm hm2 B R hB hR

end NSFormalization.Section4.A01
