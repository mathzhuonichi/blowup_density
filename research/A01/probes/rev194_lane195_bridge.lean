import NSFormalization.Section4.A01.ComplementPath
import NSFormalization.Section4.A01.ConstructorPressure

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {f : A02.SpaceTimeField} {ν S : ℝ}
variable (hf : MemForceR f) (hν : 0 < ν) (hS : 0 < S)
variable (a : SmoothL2Field Space)
variable (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
variable (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
  ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
  ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
variable (hpairs : ∀ q (hq : 6 ≤ q),
  ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
    (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
    (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
    (∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
    ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)

-- This is lane 195's `hres` premise, with its exact field and datum.
set_option maxHeartbeats 400000 in
example (t : Icc (0 : ℝ) S) :
    IsSobolevDatum 0
      (fun x => momentumResidualOfVelocity ν f
        (jointRepresentative U hpaths) (t.1, x))
      (ComplementPath.residualDatum hf hν hS a U hpairs t) := by
  have hsmooth : ContDiff ℝ ∞
      (fun x => jointRepresentative U hpaths (t.1, x)) := by
    rw [← contDiffOn_univ]
    exact (jointRepresentative_contDiffOn hS U hpaths).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨t.property, mem_univ x⟩)
  have hd := ComplementPath.residualDatum_physicalSlice hf hν hS a U hpairs
    (jointRepresentative U hpaths) t hsmooth
    (jointRepresentative_slice U hpaths t)
  simpa only [momentumResidualOfVelocity, add_comm] using hd

end NSFormalization.Section4.A01
