import NSFormalization.Section4.A01.CommonHorizon

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open EulerGainedMildFormula EulerDuhamelDifferentiation EulerSobolevHeatGenerator
open scoped Topology ContDiff NNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

#print axioms restrict_heat
#print axioms restrict_forced_source
#print axioms restrict_duhamel
#print axioms restrict_mildPath
#print axioms commonSource
#print axioms quadraticDuhamel_eq_mildPath
#print axioms lower_forced_mild
#print axioms MildUniqueness
#print axioms compatible_carriers_of_boundsInv
#print axioms compatible_carriers_of_bounds
#print axioms compatible_carriers_hall

-- An inhabited positive-horizon, all-order zero solution; no uniqueness or bound assumption.
example : ∃ U : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2),
    U ⟨0, le_rfl, by norm_num⟩ = 0 ∧
    ∀ q (hq : 6 ≤ q), ∃ u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q+1)),
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      ∀ t, u t = quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
        (coefficients 1 hq 0) 0 u t := by
  refine ⟨0, rfl, ?_⟩
  intro q hq
  refine ⟨0, ?_, ?_⟩
  · intro t
    change ordinaryLift 0 = (valueOperator 1 (q+1)) 0
    simp only [map_zero]
  · intro t
    simp [quadraticDuhamel, source_eq]

-- The same non-vacuity with the canonical smooth datum a := 0 and F := 0.
example (q : ℕ) (hq : 6 ≤ q) :
    let a : SmoothL2Field Space := SmoothL2Field.zeroField
    let F : Icc (0 : ℝ) 1 → SmoothL2Field Space := fun _ => SmoothL2Field.zeroField
    ∀ t : Icc (0 : ℝ) 1,
      (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 (q+1))) t =
        quadraticDuhamel 1 1 (by norm_num) (by norm_num) le_rfl
          (coefficients 1 hq (sobolevPath F (by intro n; dsimp [F]; exact continuous_const) q))
          (ordinarySobolev (q+1) a.toLp a.translation_contDiff) 0 t := by
  have hz : (SmoothL2Field.zeroField : SmoothL2Field Space).toLp = 0 := by
    apply Lp.ext
    filter_upwards [(SmoothL2Field.zeroField : SmoothL2Field Space).toLp_ae,
      Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx hx0
    exact hx.trans hx0.symm
  have ho (n : ℕ) : ordinarySobolev n
      (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
    apply value_injective 1
    calc
      _ = ordinaryLift (SmoothL2Field.zeroField : SmoothL2Field Space).toLp :=
        ordinarySobolev_value n _ _
      _ = ordinaryLift 0 := congrArg ordinaryLift hz
      _ = 0 := ordinaryLift.map_zero
      _ = _ := ((valueOperator 1 n).map_zero).symm

  have hf : sobolevPath (fun _ : Icc (0 : ℝ) 1 =>
      (SmoothL2Field.zeroField : SmoothL2Field Space)) (fun _ => continuous_const) q = 0 := by
    apply ContinuousMap.ext
    intro t
    exact ho q
  dsimp only
  intro t
  rw [ho, hf]
  simp [quadraticDuhamel, source_eq]

end NSFormalization.Section4.A01
