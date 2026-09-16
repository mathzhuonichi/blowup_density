import NSFormalization.Section4.A01.ConstructorAssembly

/-! The fifth-review mismatch is now superseded.  Its old single-order context
could not produce lane 194's all-order family.  This positive interface check
passes that family, with the same carrier, through `PressureSupply` verbatim. -/

noncomputable section

namespace Rev180PressureSupplyHpairsMismatch

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerQuadraticSource EulerVolterraConvolution EulerSmoothFieldSobolevTime
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

example {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    {f : NSFormalization.Section4.A02.SpaceTimeField} (hf : MemForceR f)
    (a : SmoothL2Field Space)
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
    (velocity : NSFormalization.Section4.A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hsupply : PressureSupply hq hν hS f hf a ha U hpairs hpaths
      velocity hslice hc3) :
    PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3 ∧
      ∀ p (hp : 6 ≤ p),
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
            (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t := by
  exact ⟨hsupply, hpairs⟩

end Rev180PressureSupplyHpairsMismatch
