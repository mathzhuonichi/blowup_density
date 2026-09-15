import NSFormalization.Section4.A01.InteriorMomentum

noncomputable section

namespace NSFormalization.Section4.A01

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

-- Negative example retained by the fix review: without the composite bridge
-- (projector identification plus physical/cylinder residual agreement), the
-- interior identity is not derivable from these inputs. This file is expected
-- to fail at the final application by leaving precisely `hprojected` as a goal.
example {q m : ℕ}
    (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (fc : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (uc : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (uc t))
    (hduh : ∀ t, uc t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq fc) u₀ uc t)
    (hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (H t.1))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν fc uc t)) (R t))
    (f G : VelocityField)
    (hf : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (A : Icc (0 : ℝ) S → RealVectorSobolev 0)
    (w : Icc (0 : ℝ) S → EulerMeanSolenoidal.L2)
    (hw : ∀ t, IsSobolevDatum 0 (⇑(w t)) (Leray.lerayComplement 0 (A t)))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume] ⇑(w t))
    (hres : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum 0
      (fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x)) (A t)) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      G (t, x) = pressureGradientOfVelocity ν f (jointRepresentative U hpaths) (t, x) := by
  apply interior_momentum_identity hq hm hm2 hν hS u₀ fc uc U hU hduh
    hpaths B R hB hR f G hf hG A w hw hslice hres

end NSFormalization.Section4.A01
