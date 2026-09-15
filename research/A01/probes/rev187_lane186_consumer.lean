import NSFormalization.Section4.A01.CommonHorizon
import NSFormalization.Section4.A01.ForcePathSmooth
import NSFormalization.Section4.A04.ZeroSolution

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01 (IsSobolevDatum)
open scoped Topology ContDiff NNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- Lane 187 supplies lane 186's exact `hfs` input with the canonical force carrier. -/
example (huniq : MildUniqueness)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a
      (C01.forcePath (S := S) hf) (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
          ContDiffOn ℝ ∞
              (extendPath S hS.le
                (sobolevPath (C01.forcePath (S := S) hf)
                  (C01.forcePath_jetLp_continuous (S := S) hf) q))
              (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq
              (sobolevPath (C01.forcePath (S := S) hf)
                (C01.forcePath_jetLp_continuous (S := S) hf) q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t := by
  apply compatible_carriers_of_bounds huniq hν hS a ha
    (C01.forcePath (S := S) hf) (C01.forcePath_jetLp_continuous (S := S) hf) R hb
  intro q _hq
  exact forcePath_sobolevPath_contDiffOn hf hS q

/- Any two existential datum paths representing the same slice reconstruct identically. -/
example (q : ℕ) (A : SmoothL2Field Space)
    (G H : RealVectorSobolev (q : ℝ))
    (hG : IsSobolevDatum (q : ℝ) A.field G)
    (hH : IsSobolevDatum (q : ℝ) A.field H) :
    datumSobolevCLM q G = datumSobolevCLM q H := by
  rw [datumSobolevCLM_eq_ordinarySobolev q A G hG,
    datumSobolevCLM_eq_ordinarySobolev q A H hH]

/- The zero-force witness has a genuinely nonempty positive horizon. -/
example : D01.MemForceR (0 : A02.SpaceTimeField) ∧ Nonempty (Icc (0 : ℝ) 1) := by
  exact ⟨A04.memForceR_zero, ⟨⟨0, by norm_num⟩⟩⟩

end NSFormalization.Section4.A01
