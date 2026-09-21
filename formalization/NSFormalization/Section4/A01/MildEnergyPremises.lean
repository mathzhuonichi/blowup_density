import NSFormalization.Section4.A01.MildGronwall
import NSFormalization.Section4.A01.ForcedSourceUpgrade
import Euler.MildMajorantEnergy
import Euler.ConstantCorrectionData

/-! Cylinder representatives for the finite-order mild energy argument. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution EulerTimeLp
  EulerRegularizedTopBlocks EulerSobolevMaximalRegularity EulerSobolevWordConstraints
  EulerTimeSobolevTransport EulerAsymmetricTransport EulerSobolevTransport
  EulerTimeCorrectionSource EulerRegularizedEnergyFamily EulerRegularizedForcingWord
  EulerTransportL2Time EulerWeightedForcingTime EulerSobolevEnergyPaths
  EulerRegularizedMetricPaths EulerWeightedCylinderEnergy EulerSpatialSobolevInverse
open NSFormalization.Source.ForcedCylinderLocal
open ForcedMaximalRegularity
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Dependent Sobolev bilinear continuity needs additional elaboration fuel.
set_option maxHeartbeats 400000 in
/-- The raw residual is the physical force minus spatial advection. -/
def energyRawPath {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :
    C(Icc (0 : ℝ) T, SobolevSpace 1 q) :=
  f.comp (timeInclusion hTS) -
    ⟨fun t => advection 1 hq (u t) (u t),
      ((advection 1 hq).continuous.comp u.continuous).clm_apply u.continuous⟩

/-- The cylinder Leray complement of the raw residual; no endpoint time derivative is used. -/
def energyPressurePath {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :=
  (sobolevGradientProjection 1 q 1 0).compLeftContinuous ℝ _ (energyRawPath hq hTS f u)

/-- The pressure is a gradient at every time, including zero. -/
theorem energyPressurePath_gradient {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) T) :
    value 1 (energyPressurePath hq hTS f u t) ∈ gradientSpace 1 1 0 :=
  (gradientSpace 1 1 0).starProjection_apply_mem _

/-- Higher raw residual, with one derivative supplied by Bochner maximal regularity. -/
def energyRawTime {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1))) : TimeLp T (SobolevSpace 1 (q+1)) :=
  pathLp T hT (f.comp (timeInclusion hTS)) -
    transportTime 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W

/-- Higher pressure is the same Leray complement on the Bochner residual. -/
def energyPressureTime {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1))) : TimeLp T (SobolevSpace 1 (q+1)) :=
  (sobolevGradientProjection 1 (q+1) 1 0).compLpL 2 (timeMeasure T)
    (energyRawTime hq hT hTS f u W)

-- Rewriting the dependent transport restriction is elaboration intensive.
set_option maxHeartbeats 400000 in
/-- The raw residual restricts to the continuous residual of the original equation. -/
theorem energyRawTime_restriction {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1)))
    (hW : (fun t => truncateOperator 1 (q+1) (W t)) =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => truncateOperator 1 q (energyRawTime hq hT hTS f u W t)) =ᵐ[timeMeasure T]
      extendPath T hT (energyRawPath hq hTS
        ((truncateOperator 1 q).compLeftContinuous ℝ _ f) u) := by
  filter_upwards [Lp.coeFn_sub (pathLp T hT (f.comp (timeInclusion hTS)))
    (transportTime 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W),
    pathLp_ae T hT (f.comp (timeInclusion hTS)),
    transportTime_ae 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W, hW] with t hs hf ha hw
  have ht := restrict_transport_state 1 hq (velocityComponents 1 0)
    (velocityComponents_norm 1 0 (by norm_num) (by simp))
    (extendPath T hT u t) (extendPath T hT u t) (W t) hw
  have hh := hs.trans (congrArg₂ (fun x y : SobolevSpace 1 (q+1) => x - y) hf ha)
  have hr := congrArg (truncateOperator 1 q) hh
  exact hr.trans ((map_sub (truncateOperator 1 q) _ _).trans
    (congrArg₂ (fun x y : SobolevSpace 1 q => x - y) rfl ht))

-- Projection and path coercions require additional dependent elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Navier–Stokes pressure restriction, using only the standard a.e. state restriction. -/
theorem energyPressureTime_restriction {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (W : TimeLp T (SobolevSpace 1 ((q+1)+1)))
    (hW : (fun t => truncateOperator 1 (q+1) (W t)) =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => truncateOperator 1 q (energyPressureTime hq hT hTS f u W t)) =ᵐ[timeMeasure T]
      extendPath T hT (energyPressurePath hq hTS
        ((truncateOperator 1 q).compLeftContinuous ℝ _ f) u) := by
  filter_upwards [(sobolevGradientProjection 1 (q+1) 1 0).coeFn_compLpL
    (energyRawTime hq hT hTS f u W), energyRawTime_restriction hq hT hTS f u W hW] with t hp hr
  change truncateOperator 1 q (((sobolevGradientProjection 1 (q+1) 1 0).compLpL 2
    (timeMeasure T) (energyRawTime hq hT hTS f u W)) t) = _
  rw [hp]
  apply value_injective 1
  change gradientProjection 1 1 0 (value 1 (energyRawTime hq hT hTS f u W t)) =
    gradientProjection 1 1 0 (value 1 (extendPath T hT
      (energyRawPath hq hTS ((truncateOperator 1 q).compLeftContinuous ℝ _ f) u) t))
  have hv := congrArg (value 1) hr
  rw [value_truncateOperator] at hv
  exact congrArg (gradientProjection 1 1 0) hv


/-- Every mild competitor preserves the datum's standard solenoidal constraint. -/
theorem energy_velocity_divergenceFree {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f)
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0 := by
  have h := EulerDivergenceFreeHeat.mild_solution_preserves_gradient_zero 1 1 0 ν hν T hT
    (ordinarySobolev (q+1) a.toLp a.translation_contDiff)
    ((EulerDivergenceFreeHeat.gradientEvaluation_zero_iff 1 1 0 _).mpr
      (NSFormalization.Source.OrdinaryForcedLocal.initial_divergenceFree (q+1) a ha))
    (coefficients 1 hq f |>.comp (timeInclusion hTS)).apply
    (coefficients 1 hq f |>.comp (timeInclusion hTS)).continuous
    (fun t v => by
      change gradientProjection 1 1 0 (value 1 ((coefficients 1 hq f).apply _ v)) = 0
      rw [source_eq]
      exact leray_gradient_zero 1 _) u hu
  exact fun t => (EulerDivergenceFreeHeat.gradientEvaluation_zero_iff 1 1 0 _).mp (h t)

/-- Maximal regularity retains the actual approximation limit, which the energy theorem needs. -/
theorem energy_maximal_limit {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u₀ : SobolevSpace 1 (q+1)) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f) u₀ u t) :
    ∃ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (𝓝 U) :=
  exists_maximal_mild_limit 1 ν hν T hT u₀ (nonlinearSource hq hTS f u) u hu

/-- The identity metric on the cylinder, with its literal zero spatial derivatives. -/
def energyIdentity : SmoothCoefficient 1 :=
  EulerConstantCorrection.coefficient 1 (ContinuousLinearMap.id ℝ Space)

/-- Full word energy at order q+1, with one external index of weight one. -/
def energyRootPath {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) : C(Icc (0 : ℝ) T, ℝ) :=
  EulerMetricPathConvergence.weightedMetricPath T
    (fun _ : Unit => gevreyWeightPath T (ContinuousMap.const _ 1) 0)
    (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const)
    (energyValueFamily 1 (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val)
      (fun _ W => W.2) (fun _ W => Nat.le_of_lt_succ W.1.isLt) T u)

/-- The complete word family has exactly the Euclidean norm used by lane 196. -/
theorem energyRootPath_apply {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) T) :
    energyRootPath u t = euclideanWordNorm (u t) := by
  simp only [energyRootPath, EulerMetricPathConvergence.weightedMetricPath_apply,
    gevreyWeightPath, ContinuousMap.coe_mk, EulerPacketWeights.weight,
    pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul,
    Finset.univ_unique, Finset.sum_singleton]
  change EulerFiniteMetricEnergy.familyMetricNorm energyIdentity.operator _ = _
  rw [show energyIdentity.operator = ContinuousLinearMap.id ℝ (LiftL2 1) from
    EulerConstantCorrection.coefficient_operator_id 1]
  apply congrArg (EulerFiniteMetricEnergy.familyMetricNorm (ContinuousLinearMap.id ℝ (LiftL2 1)))
  funext W
  change value 1 (EulerMildTopWord.boundedWordBlock 1 0 W.1.val
    (by omega : 0 + W.1.val ≤ q+1) W.2 (u t)) = (u t).val W
  rw [EulerMildTopWord.boundedWordBlock_value]
  rfl

/-- The limiting full-word forcing norm; this is the vendor's Z without alteration. -/
def energyForcingNorm {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (F P : TimeLp T (SobolevSpace 1 (q+1))) : TimeLp T ℝ :=
  weightedForcingTime T hT
    (fun _ : Unit => gevreyWeightPath T (ContinuousMap.const _ 1) 0)
    (forcingFamilyTime 1 (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val)
      (fun _ W => W.2) (fun _ W => Nat.le_of_lt_succ W.1.isLt) T hT
      (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
      (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) U F P)

/-- Identity-metric specialization of the vendor estimate, keeping its limiting Z explicit.
The inputs are restrictions of the mild equation, solenoidality, gradient pressure,
and strong Bochner approximation and restriction, respectively. -/
theorem energy_estimate_of_representatives {q : ℕ} (hq : 6 ≤ q) {ν T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T)
    (u₀ : SobolevSpace 1 (q+1)) (f p : C(Icc (0 : ℝ) T, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hsol : ∀ r, u r = EulerSobolevHeat.heatOperator 1 (q+1) (2*ν*r.val).toNNReal u₀ +
      ∫ v in (0 : ℝ)..r.val, EulerSobolevHeat.heatKernel 1 q ν hν v (extendPath T hT f (r.val-v)))
    (hu : ∀ r, value 1 (u r) ∈ divergenceFreeSpace 1 1 0)
    (hp : ∀ r, value 1 (p r) ∈ gradientSpace 1 1 0)
    (U : TimeLp T (SobolevSpace 1 (2+q))) (F P : TimeLp T (SobolevSpace 1 (q+1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U))
    (hF : (fun r => truncateOperator 1 q (F r)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun r => truncateOperator 1 q (P r)) =ᵐ[timeMeasure T] extendPath T hT p) :
    ∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
      energyRootPath u ⟨t, h0s.trans hst, htT⟩ - energyRootPath u ⟨s, h0s, hst.trans htT⟩ ≤
        ∫ r in Icc s t, energyForcingNorm hq hT u U F P r ∂timeMeasure T := by
  intro s t h0s hst htT
  let B := fun r : Icc (0 : ℝ) T =>
    (EulerCylinderSobolevSpace.sobolevEmbeddingConstant 1 (q+1) * ‖u r‖).toNNReal
  have hB : ∀ r, ∀ᵐ x ∂liftMeasure 1, ‖value 1 (u r) x‖ ≤ B r := by
    intro r
    filter_upwards [EulerCylinderSobolevSpace.value_ae_bound 1 (by omega : 3 ≤ q+1) (u r)] with x hx
    exact hx.trans (Real.le_coe_toNNReal _)
  have H := EulerMildMajorantEnergy.mild_majorized_energy_subinterval 1 (by omega : 3 ≤ q+1)
    T hT s t h0s hst htT
    (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val) (fun _ W => W.2)
    (fun _ W => Nat.le_of_lt_succ W.1.isLt) (fun _ => 0) ν hν 1 0 1 (by norm_num)
    (ContinuousMap.const _ 1) (ContinuousMap.const _ 0) (fun _ => by norm_num)
    (fun r _ => hasDerivAt_const r 1)
    (fun _ => energyIdentity) (fun _ => energyIdentity) continuous_const continuous_const
    (ContinuousMap.const _ 0) (fun r _ => hasDerivAt_const r _)
    (fun _ _ _ _ => rfl)
    (fun _ _ v => by simp [energyIdentity, EulerConstantCorrection.coefficient])
    (fun _ _ _ => rfl) B u u u₀ f p hsol hu hp hu hB U F P hU hF hP
    (ContinuousMap.const _ 0) (ContinuousMap.const _ 0) (ContinuousMap.const _ 1)
    (fun _ => by simp [viscousGrowthCoefficient, energyIdentity, EulerConstantCorrection.coefficient,
      EulerCylinderViscousEnergy.transportEnergyConstant, EulerCylinderViscousEnergy.heatEnergyConstant])
    (fun _ => by simp)
    (fun _ => by simp [energyIdentity, EulerConstantCorrection.coefficient])
  dsimp only at H
  have hk : (pathLp T hT (ContinuousMap.const _ (1 : ℝ)) : ℝ → ℝ) =ᵐ[timeMeasure T] fun _ => 1 :=
    pathLp_ae T hT (ContinuousMap.const _ 1)
  have hi : (∫ r in Icc s t, pathLp T hT (ContinuousMap.const _ (1 : ℝ)) r *
      energyForcingNorm hq hT u U F P r ∂timeMeasure T) =
      ∫ r in Icc s t, energyForcingNorm hq hT u U F P r ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hk] with r hr
    rw [hr, one_mul]
  simp only [extendPath, ContinuousMap.const_apply, zero_mul, intervalIntegral.integral_zero,
    zero_add] at H
  change energyRootPath u _ - energyRootPath u _ ≤
    ∫ r in Icc s t, pathLp T hT (ContinuousMap.const _ (1 : ℝ)) r *
      energyForcingNorm hq hT u U F P r ∂timeMeasure T at H
  rw [hi] at H
  exact H


/-- Adjacent restrictions of a smooth force agree on the entire closed window. -/
theorem energy_force_restriction {S : ℝ}
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (q : ℕ) :
    (truncateOperator 1 q).compLeftContinuous ℝ _ (sobolevPath F hF (q+1)) =
      sobolevPath F hF q := by
  apply ContinuousMap.ext
  intro t
  exact restrict_sobolev (by omega : q ≤ q+1) (F t)

/-- Canonical full-word forcing norm of the Navier–Stokes cylinder competitor. -/
def cylinderEnergyForcing {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q))) : TimeLp T ℝ :=
  let W := EulerSobolevWordValueIdentity.reindexMaximalTime 1 q T U
  energyForcingNorm hq hT u U
    (ForcedSourceUpgrade.sourceTime hq hT hTS (sobolevPath F hF (q+1)) u W)
    (energyPressureTime hq hT hTS (sobolevPath F hF (q+1)) u W)

-- Assemble dependent Sobolev representatives without changing their orders.
set_option maxHeartbeats 400000 in
/-- Integrated root-energy estimate for every mild competitor and every subinterval.
All vendor premises are constructed; no additional analytic input is assumed.
The force may in particular be `C01.forcePath hf` with its canonical continuity proof. -/
theorem mild_energy_estimate_of_cylinder {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) :
    ∃ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) ∧
      ∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
        energyRootPath u ⟨t, h0s.trans hst, htT⟩ - energyRootPath u ⟨s, h0s, hst.trans htT⟩ ≤
          ∫ r in Icc s t, cylinderEnergyForcing hq hT hTS F hF u U r ∂timeMeasure T := by
  obtain ⟨U, hU⟩ := energy_maximal_limit hq hν hT hTS _ (sobolevPath F hF q) u hu
  let W := EulerSobolevWordValueIdentity.reindexMaximalTime 1 q T U
  have hW := EulerSobolevWordValueIdentity.reindexMaximalTime_restriction 1 T hT u U hU
  have hsource := ForcedSourceUpgrade.sourceTime_restriction hq hT hTS (sobolevPath F hF (q+1)) u W hW
  have hpressure := energyPressureTime_restriction hq hT hTS (sobolevPath F hF (q+1)) u W hW
  rw [energy_force_restriction] at hsource hpressure
  refine ⟨U, hU, ?_⟩
  exact energy_estimate_of_representatives hq hν hT _
    (nonlinearSource hq hTS (sobolevPath F hF q) u)
    (energyPressurePath hq hTS (sobolevPath F hF q) u) u hu
    (energy_velocity_divergenceFree hq hν hT hTS a ha _ u hu)
    (energyPressurePath_gradient hq hTS _ u) U _ _ hU hsource hpressure


/-- Full gradient family norm of the genuine higher Bochner representative. -/
def energyGradientNorm {q : ℕ} {T : ℝ} (U : TimeLp T (SobolevSpace 1 (2+q))) (t : ℝ) : ℝ :=
  let v := EulerSobolevWordValueIdentity.reindexMaximalTime 1 q T U t
  Real.sqrt (∑ i : Fin 4, ∑ W : SobolevWord (q+1),
    ‖(derivativeOperator 1 (q+1) i v).val W‖^2)

/-- Lane 199's tame forcing-family obligation, restricted to actual mild solutions
and their strong maximal limits. Multiplication by the root gives exactly the
`A * 16 * low * sqrt(x) * g` pairing shape, with the genuine full gradient norm.
The intended proof uses `outerProductTame`, `outerSobolevNormAt_le`, and the
word forcing identification; an abstract tensor bound alone does not prove it. -/
def ForcingFamilyBound {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      ∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r

/-- Lane 199's envelope obligation, restricted to actual mild solutions with their
integrated root estimate and tame forcing bound. This includes recovering a
usable dissipative inequality: dissipation has already been dropped in the
vendor root estimate. It is not asserted to follow by scalar differentiation
of that estimate. The envelope is differentiable only in the open time window. -/
def EnvelopeConversion {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      (∀ s t (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T),
        energyRootPath u ⟨t, h0s.trans hst, htT⟩ - energyRootPath u ⟨s, h0s, hst.trans htT⟩ ≤
          ∫ r in Icc s t, cylinderEnergyForcing hq hT hTS F hF u U r ∂timeMeasure T) →
      (∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r) →
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧ (∀ t, ‖u t‖ ≤ Real.sqrt (x t)) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤
        E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T,
        (1/2) * d t + ν * (g t)^2 ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u t)‖) * Real.sqrt (extendPath T hT x t) * g t +
          (E * ‖sobolevPath F hF (q+1)‖) * Real.sqrt (extendPath T hT x t)

/-- The proved estimate plus precisely the two lane-199 obligations supplies
`FiniteMildEnergy`; no additional premises package is needed. -/
theorem finiteMildEnergy_of_estimate {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ)
    (hforcing : ForcingFamilyBound hq hν a F hF E A)
    (henvelope : EnvelopeConversion hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A := by
  intro T hT hTS u hu
  obtain ⟨U, hU, hest⟩ := mild_energy_estimate_of_cylinder hq hν a ha F hF T hT hTS u hu
  exact henvelope T hT hTS u hu U hU hest (hforcing T hT hTS u hu U hU)

end NSFormalization.Section4.A01
