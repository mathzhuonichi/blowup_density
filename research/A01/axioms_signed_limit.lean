import NSFormalization.Section4.A01.SignedLimit

set_option format.width 240

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open EulerTimeLp EulerRegularizedTopBlocks
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private theorem zero_value : (SmoothL2Field.zeroField : SmoothL2Field Space).toLp = 0 := by
  apply Lp.ext
  filter_upwards [(SmoothL2Field.zeroField : SmoothL2Field Space).toLp_ae,
    Lp.coeFn_zero Space 2 volume] with x hx hz
  exact hx.trans hz.symm

private theorem zero_sob (q : ℕ) : ordinarySobolev q
    (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
    (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply value_injective 1
  simp only [ordinarySobolev_value, zero_value, map_zero]
  rfl

private theorem zero_mild (q : ℕ) (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (hTS : T ≤ 1) : ∀ t,
    (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) t =
      quadraticDuhamel 1 1 (by norm_num) hT hTS
        (coefficients 1 hq (sobolevPath
          (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
          (fun _ => continuous_const) q))
        (ordinarySobolev (q+1) (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
          (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) 0 t := by
  intro t
  simp only [quadraticDuhamel, source_eq, ContinuousMap.zero_apply, zero_sob,
    map_zero, sobolevPath, ContinuousMap.coe_mk, sub_zero, intervalIntegral.integral_zero,
    add_zero]

-- All maximal limits and all competitors are covered, not merely a chosen zero path.
private theorem zero_forcing (q : ℕ) (hq : 6 ≤ q) (E A : ℝ) :
    ForcingFamilyBound hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) E A := by
  intro T hT hTS u hu U _
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  apply Filter.Eventually.of_forall
  intro r
  simp [extendPath, energyRootPath_apply, euclideanWordNorm_eq]

private theorem zero_passage (q : ℕ) (hq : 6 ≤ q) :
    CylinderSignedEnergyPassage hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) := by
  intro T hT hTS u hu U hU ε hε
  dsimp only
  intro t ht
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild q hq hT hTS)
  subst u
  have hn (n : ℕ) : maximalApproximation 1 q T n
      (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) = 0 := by
    apply ContinuousMap.ext
    intro s
    simp [maximalApproximation, EulerMildWordEquation.mapPath]
  have hp : pathLp T hT (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (2+q))) = 0 := by
    apply Lp.ext
    filter_upwards [pathLp_ae T hT (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (2+q))),
      Lp.coeFn_zero (SobolevSpace 1 (2+q)) 2 (timeMeasure T)] with s hs hz
    simpa [extendPath] using hs.trans hz.symm
  have hU0 : U = 0 := by
    apply tendsto_nhds_unique hU
    simpa only [hn, hp] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : TimeLp T (SobolevSpace 1 (2+q))))
        Filter.atTop (𝓝 0))
  subst U
  have hg : energyGradientNorm (0 : TimeLp T (SobolevSpace 1 (2+q))) =ᵐ[timeMeasure T] 0 := by
    filter_upwards [Lp.coeFn_zero (SobolevSpace 1 ((q+1)+1)) 2 (timeMeasure T)] with s hs
    simp only [energyGradientNorm, EulerSobolevWordValueIdentity.reindexMaximalTime, map_zero, hs]
    simp
  have hquot : (fun s =>
      (extendPath T hT (energyRootPath (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))) s *
        cylinderEnergyForcing hq hT hTS
          (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
          (fun _ => continuous_const) 0 0 s -
        1 * (energyGradientNorm (0 : TimeLp T (SobolevSpace 1 (2+q))) s)^2) /
          Real.sqrt ((extendPath T hT (energyRootPath (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))) s)^2+ε^2))
      =ᵐ[volume.restrict (Icc 0 t)] 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right ht.2) hg] with s hs
    simp [extendPath, energyRootPath_apply, euclideanWordNorm_eq, hs]
  have hquot' := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hquot
  rw [← uIoc_of_le ht.1] at hquot'
  have hqi := intervalIntegrable_congr_ae hquot'
  have hi : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 t := intervalIntegrable_const
  refine ⟨hqi.mpr hi, ?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict hquot']
  simp [extendPath, energyRootPath_apply, euclideanWordNorm_eq]

example (q : ℕ) (hq : 6 ≤ q) :
    FiniteMildEnergy hq (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) (max 1 (mildNormConstant q)) 0 :=
  finiteMildEnergy_of_forcingBound' hq (by norm_num) _ _ _ _ (le_max_right _ _)
    (zero_forcing q hq _ _) (zero_passage q hq)

-- Negative control: at r=0 a negative forcing constant cannot survive division.
example : (0 : ℝ)*0 ≤ 0*0*0+(-1)*0 ∧
    ¬ ((0*0-1*0^2)/Real.sqrt (0^2+1^2) ≤ 0^2/(4*1)*0+(-1)) := by norm_num
-- Nonzero scalar absorption with the sharp Young coefficient.
example : ((1 : ℝ)*1-1*1^2)/Real.sqrt (1^2+1^2) ≤ 1^2/(4*1)*1+0 :=
  signed_quotient_absorption (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

#print axioms strong_time_square_integral_limit
#print axioms mapped_time_square_integral_limit
#print axioms maximal_word_square_integral_limit
#print axioms signed_quotient_absorption
#print axioms CylinderSignedEnergyPassage
#print axioms cylinderSignedRootLimit_of_forcingBound
#print axioms finiteMildEnergy_of_forcingBound'
#print axioms zero_value
#print axioms zero_sob
#print axioms zero_mild
#print axioms zero_forcing
#print axioms zero_passage
end NSFormalization.Section4.A01
