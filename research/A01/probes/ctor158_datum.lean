import NSFormalization.Section4.A01.EulerPairing
import NSFormalization.Section4.A02.SolutionClass

noncomputable section
namespace Ctor158Probe

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerLpTranslation

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Form producing D01.IsSobolevDatum (exact match of the supply lemma)
theorem datum_slice_D01 {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    {m : ℕ} (hm : m + 3 ≤ q + 1) (t : Icc (0 : ℝ) S) :
    ∃ A : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => velocity (↑t, x)) A :=
  exists_isSobolevDatum_m_of_ae m (U t) (fun x : Space => velocity (↑t, x)) (hslice t)
    (hasWeakDerivsL2_of_cylinder (u t) (fun θ => hu θ t) (U t) (hU t) m hm)

-- Form producing A02.IsSobolevDatum (the ClassicalSolutionR.sobolev field's datum), by defeq
theorem datum_slice_A02 {q : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    {m : ℕ} (hm : m + 3 ≤ q + 1) (t : Icc (0 : ℝ) S) :
    ∃ A : NSFormalization.Paper3.RealVectorSobolev (m : ℝ),
      NSFormalization.Section4.A02.IsSobolevDatum (m : ℝ) (fun x : Space => velocity (↑t, x)) A :=
  exists_isSobolevDatum_m_of_ae m (U t) (fun x : Space => velocity (↑t, x)) (hslice t)
    (hasWeakDerivsL2_of_cylinder (u t) (fun θ => hu θ t) (U t) (hU t) m hm)

#print axioms datum_slice_D01
#print axioms datum_slice_A02

end Ctor158Probe
