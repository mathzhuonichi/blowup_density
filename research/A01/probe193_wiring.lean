import NSFormalization.Section4.A01.AprioriFamily
import NSFormalization.Section4.A01.ForceBridge

noncomputable section
namespace NSFormalization.Section4.A01.Probe193

open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01 (IsSobolevDatum)
open NSFormalization.Source.ForcedCylinderLocal
open EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- Copied combined export from lane 192, commit `9ca0a45`, CylinderWiring.lean:139-161.
The sibling module is absent here; this theorem parameter checks composition only.
The reviewer positive and negative probes remain unchanged in probes/. -/
example
    (constructorInputs192 : ∀ {q : ℕ} (hq : 6 ≤ q) {f : A02.SpaceTimeField} {S ν : ℝ} (hf : D01.MemForceR f)
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (_ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) (R : ℕ → ℝ)
    (_hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)),
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
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    {q : ℕ} (hq : 6 ≤ q) {f : A02.SpaceTimeField} {S ν R₆ : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ p, 0 ≤ E p) (hC : ∀ p, 0 ≤ C p)
    (hMG : ∀ p (hp : 6 ≤ p), MildGronwall hp hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (E p) (C p)) :
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
  apply constructorInputs192 hq hf hν hS a ha
    (aprioriRadius a _ _ R₆ E C)
  exact hb_of_base hν hS.le a _ _ u₆ hR h₆ E C hE hC hMG

end NSFormalization.Section4.A01.Probe193
