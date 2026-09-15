import NSFormalization.Section4.A01.AprioriInvariance

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerBoundedMildContinuation EulerDivergenceFreeHeat EulerUniformHeatLocal
open EulerTimePathGluing EulerQuadraticMildPasting
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms HasAprioriBoundInv
#print axioms HasAprioriBound.toInv
#print axioms forced_global_mild_core_of_boundInv
#print axioms forced_global_of_boundInv
#print axioms localTheory_on_prescribed_horizon_of_boundInv

-- Positive-time non-vacuity of the full consumer: for concrete zero datum and force,
-- ν = 1, q = 6, S = 1, an invariant bound supplies both paths and all seven clauses.
example :
    let R := ‖ordinarySobolev 7 (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff‖
    HasAprioriBoundInv (by omega : 6 ≤ 6) (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) R →
    ∃ (u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (6 + 1)))
      (U : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)),
      ‖u‖ ≤ R ∧
      u ⟨0, le_rfl, by norm_num⟩ =
        ordinarySobolev 7 (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
          (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff ∧
      U ⟨0, le_rfl, by norm_num⟩ =
        (SmoothL2Field.zeroField : SmoothL2Field Space).toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
      (coefficients 1 (by omega : 6 ≤ 6)
        (sobolevPath (fun _ : Icc (0 : ℝ) 1 =>
          (SmoothL2Field.zeroField : SmoothL2Field Space))
          (fun _ => continuous_const) 6))
      (ordinarySobolev 7 (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
        (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) u t) ∧
      ∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 7 (0, θ) (u t) = u t := by
  dsimp only
  intro hbound
  let R := ‖ordinarySobolev 7 (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
    (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff‖
  exact forced_global_of_boundInv (q := 6) (by omega) (ν := 1) (S := 1) (R := R)
    (by norm_num) (by norm_num) (norm_nonneg _) SmoothL2Field.zeroField
    (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
    (fun _ => SmoothL2Field.zeroField) (fun _ => continuous_const)
    le_rfl hbound

end NSFormalization.Section4.A01
