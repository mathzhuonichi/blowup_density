import NSFormalization.Section4.A01.DatumPathDeriv

noncomputable section

namespace NSFormalization.Section4.A01

open Set
open NSFormalization.Source.ForcedCylinderLocal
open EulerCylinderSobolevSpace EulerLpTranslation EulerLiftedGradientSpace
  EulerQuadraticSource EulerSobolevLaplacian

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Reviewer probe: the lane proof copied verbatim, with the local 400000 override removed.
theorem rev169_cylinderResidual_invariant_default {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S) :
    sobolevTranslation 1 m (0, θ) (cylinderResidual hq hm ν f u t) =
      cylinderResidual hq hm ν f u t := by
  have hu' : sobolevTranslation 1 (m + 2) (0, θ) (restrictOperator 1 hm (u t)) =
      restrictOperator 1 hm (u t) := by
    rw [← restrictOperator_translation, hu θ t]
  have hs := source_translation 1 hq f (0, θ) (hf θ)
    (timeInclusion (le_refl S) t) (u t)
  rw [hu θ t] at hs
  let z : SobolevSpace 1 m := restrictOperator 1 (by omega : m ≤ q)
    ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))
  have hs' : sobolevTranslation 1 m (0, θ) z = z := by
    dsimp only [z]
    rw [← restrictOperator_translation, ← hs]
  change sobolevTranslation 1 m (0, θ)
      (ν • laplacianOperator 1 m (restrictOperator 1 hm (u t)) +
        z) =
    ν • laplacianOperator 1 m (restrictOperator 1 hm (u t)) +
      z
  rw [map_add, map_smul]
  rw [laplacianOperator_translation_local]
  rw [hu']
  rw [hs']

end NSFormalization.Section4.A01
