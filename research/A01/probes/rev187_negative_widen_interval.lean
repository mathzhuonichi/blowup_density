import NSFormalization.Section4.A01.ForcePathSmooth

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanSolenoidal EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerVolterraConvolution EulerSmoothFieldSobolevTime
open scoped ContDiff Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {f : A02.SpaceTimeField} {S : ℝ}

/- Substantive mutation: widen the regularity set below time zero.  Replaying the
lane proof must fail because `MemForceR` supplies `G` only on `futureTimes = Ici 0`. -/
theorem mutated_forcePath_sobolevPath_contDiffOn
    (hf : D01.MemForceR f) (hS : 0 < S) (q : ℕ) :
    ContDiffOn ℝ ∞
      (extendPath S hS.le
        (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q))
      (Icc (-1 : ℝ) S) := by
  obtain ⟨G, hpath, hGc, _, _⟩ := hf.2 q
  have hcomp : ContDiffOn ℝ ∞ (datumSobolevCLM q ∘ G) (Icc (-1 : ℝ) S) :=
    (datumSobolevCLM q).contDiff.comp_contDiffOn hGc |>.mono fun _ ht => ht.1
  apply hcomp.congr
  intro t ht
  simp only [extendPath, projIcc_of_mem hS.le, sobolevPath, ContinuousMap.coe_mk,
    Function.comp_apply]
  exact (datumSobolevCLM_eq_ordinarySobolev q (C01.forcePath hf ⟨t, by omega⟩) (G t)
    (hpath t (by omega))).symm

end NSFormalization.Section4.A01
