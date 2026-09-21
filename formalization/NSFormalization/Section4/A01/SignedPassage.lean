import NSFormalization.Section4.A01.SignedLimit

/-! The unabsorbed signed energy inequality for the maximal-approximation limit.
The varying inverse-root weight acts continuously on time L². Dissipation is
retained as the squared norm of the complete derivative-word family. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
  EulerQuadraticSourceLimit EulerTimeLp EulerRegularizedTopBlocks
  EulerRegularizedWordEquation EulerRegularizedWordTime EulerRegularizedForcingWord
  EulerRegularizedEnergyFamily EulerFiniteMetricEnergy EulerMetricPathConvergence
  EulerTransportL2Time EulerRegularizedMetricPaths EulerWeightedCylinderEnergy
  EulerSpatialSobolevInverse EulerSobolevMetricTransport EulerSobolevEnergyPaths
  ForcedMaximalRegularity EulerWeightedForcingTime EulerMildTopWord
  EulerSobolevWordValueIdentity
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology InnerProductSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Actual full energy-word regularization, before taking a scalar norm. -/
def signedWordPath {q : ℕ} {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (W : SobolevWord (q+1)) :=
  regularizedWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T u

/-- The full root of the finite-level energy. -/
def signedApproximationRoot {q : ℕ} {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) : C(Icc (0 : ℝ) T, ℝ) :=
  metricPath T (ContinuousMap.const _ (ContinuousLinearMap.id ℝ (LiftL2 1)))
    (regularizedValueFamily 1 (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val)
      (fun _ W => W.2) (fun _ W => Nat.le_of_lt_succ W.1.isLt) n T u ())

/-- No heat dissipation has been discarded in this continuous scalar path. -/
def signedApproximationDissipation {q : ℕ} {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => ∑ W : SobolevWord (q+1), ∑ i : Fin 4,
      ‖word 1 (signedWordPath n u W t) (by norm_num : 1 ≤ 2) (fun _ => i)‖^2,
    continuous_finsetSum _ fun W _ => continuous_finsetSum _ fun i _ =>
      (((wordOperator 1 (⟨⟨1, by norm_num⟩, fun _ => i⟩ : SobolevWord 2)).continuous.comp
        (signedWordPath n u W).continuous).norm.pow 2)⟩

/-- Actual regularized source-plus-transport-plus-pressure forcing norm. -/
def signedApproximationForcing {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace 1 q)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => familyNorm (fun W : SobolevWord (q+1) =>
      forcingWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
        (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
        (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) u f p t),
    EulerFamilyNormTime.familyNorm_lipschitz.continuous.comp
      (continuous_pi fun W => (forcingWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
        (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
        (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) u f p).continuous)⟩

/-- Literal full energy norm, with no cardinality comparison constant. -/
theorem signedApproximationRoot_apply {q : ℕ} {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) T) :
    signedApproximationRoot n u t =
      familyNorm (fun W => value 1 (signedWordPath n u W t)) := by
  simp only [signedApproximationRoot, metricPath, ContinuousMap.coe_mk,
    ContinuousMap.const_apply, familyMetricNorm, familyEnergy,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  rfl

/-- Uniform convergence includes both endpoints and zero energy. -/
theorem signedApproximationRoot_tendsto {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :
    Filter.Tendsto (fun n => signedApproximationRoot n u) Filter.atTop (𝓝 (energyRootPath u)) := by
  have h := metricPath_tendsto T (ContinuousMap.const _ (ContinuousLinearMap.id ℝ (LiftL2 1)))
    _ _ (regularizedValueFamily_tendsto 1
      (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val)
      (fun _ W => W.2) (fun _ W => Nat.le_of_lt_succ W.1.isLt) T u ())
  convert h using 1
  · rfl
  apply congrArg nhds
  apply ContinuousMap.ext
  intro t
  rw [energyRootPath_apply, euclideanWordNorm_eq]
  simp only [metricPath, ContinuousMap.coe_mk, ContinuousMap.const_apply,
    familyMetricNorm, familyEnergy, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro W _
  congr 2
  symm
  exact EulerMildTopWord.boundedWordBlock_value 1 _ _ _ _ _

/-- Identity transport cancels at finite Sobolev regularity. -/
theorem signed_transport_zero {q : ℕ} (hq : 3 ≤ q)
    (z : SobolevSpace 1 q) (e : SobolevSpace 1 1)
    (hz : value 1 z ∈ divergenceFreeSpace 1 1 0) :
    ⟪value 1 e, transportOperator 1 hq 1 0 z e⟫_ℝ = 0 := by
  let B := (sobolevEmbeddingConstant 1 q * ‖z‖).toNNReal
  have hB : ∀ᵐ x ∂liftMeasure 1, ‖value 1 z x‖ ≤ B := by
    filter_upwards [value_ae_bound 1 hq z] with x hx
    exact hx.trans (Real.le_coe_toNNReal _)
  have h := metric_transport_bound 1 hq 1 0 energyIdentity z e
    (fun _ _ _ => rfl) hz B hB
  have he : |⟪value 1 e, transportOperator 1 hq 1 0 z e⟫_ℝ| ≤ 0 := by
    rw [show energyIdentity.operator = ContinuousLinearMap.id ℝ (LiftL2 1) from
      EulerConstantCorrection.coefficient_operator_id 1] at h
    simpa [energyIdentity, EulerConstantCorrection.coefficient] using h
  exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))

/-- Pressure and transport vanish before the Cauchy--Schwarz bound; no tame
estimate for a regularized forcing family is assumed. -/
theorem signed_source_pairing_le {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace 1 q))
    (hu : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (hp : ∀ t, value 1 (p t) ∈ gradientSpace 1 1 0) (t : Icc (0 : ℝ) T) :
    (∑ W : SobolevWord (q+1), ⟪value 1 (signedWordPath n u W t),
      sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T f t⟫_ℝ) ≤
        signedApproximationRoot n u t * signedApproximationForcing hq n u f p t := by
  let e := fun W : SobolevWord (q+1) => signedWordPath n u W t
  let g := fun W : SobolevWord (q+1) => forcingWordPath 1
    (Nat.le_of_lt_succ W.1.isLt) n W.2 T
    (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
    (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) u f p t
  have he (W : SobolevWord (q+1)) :
      ⟪value 1 (e W), g W⟫_ℝ = ⟪value 1 (e W),
        sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T f t⟫_ℝ := by
    have ht := signed_transport_zero (by omega : 3 ≤ q+1) (u t)
      (truncateOperator 1 1 (e W)) (hu t)
    rw [value_truncateOperator] at ht
    have hp' := pressure_pairing_zero 1 1 0
      (regularizedWordBlock_gradient 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 1 0 (p t) (hp t))
      (regularized_word_divergenceFree 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 1 0 (u t) (hu t))
    rw [real_inner_comm] at hp'
    dsimp only [g]
    rw [forcingWordPath_apply, transportL2Path_apply]
    change ⟪value 1 (e W), _ + _ + energyIdentity.operator _⟫_ℝ = _
    rw [show energyIdentity.operator = ContinuousLinearMap.id ℝ (LiftL2 1) from
      EulerConstantCorrection.coefficient_operator_id 1]
    simp only [ContinuousLinearMap.id_apply, inner_add_right]
    change _ + ⟪value 1 (e W), transportOperator 1 _ 1 0 (u t)
      (truncateOperator 1 1 (e W))⟫_ℝ + _ = _
    rw [ht, add_zero]
    change ⟪value 1 (e W), sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T f t⟫_ℝ +
      ⟪value 1 (e W), value 1 (regularizedWordBlock 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 (p t))⟫_ℝ = _
    change ⟪value 1 (e W), value 1 (regularizedWordBlock 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 (p t))⟫_ℝ = 0 at hp'
    rw [hp', add_zero]
  rw [signedApproximationRoot_apply]
  change _ ≤ familyNorm (fun W => value 1 (e W)) * familyNorm g
  calc
    _ = ∑ W, ⟪value 1 (e W), g W⟫_ℝ := Finset.sum_congr rfl (fun W _ => (he W).symm)
    _ ≤ ∑ W, ‖value 1 (e W)‖ * ‖g W‖ := Finset.sum_le_sum (fun _ _ => real_inner_le_norm _ _)
    _ ≤ _ := family_cauchy_schwarz _ _

/-- FTC after division by a strictly positive regularized root. Only interior
derivatives are needed, so the conclusion includes both closed endpoints. -/
theorem signed_scalar_integral {T ν ε : ℝ} (_hT : 0 ≤ T) (hε : 0 < ε)
    (x p d z : ℝ → ℝ) (hx : Continuous x) (_hp : Continuous p)
    (hd : Continuous d) (hz : Continuous z) (hx0 : ∀ s, 0 ≤ x s)
    (hder : ∀ s ∈ Ioo 0 T, HasDerivAt x (2 * p s - 2 * ν * d s) s)
    (hbound : ∀ s ∈ Icc 0 T, p s ≤ Real.sqrt (x s) * z s) :
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s => (Real.sqrt (x s) * z s - ν*d s) /
        Real.sqrt (x s+ε^2)) volume 0 t ∧
      Real.sqrt (x t+ε^2) ≤ Real.sqrt (x 0+ε^2) +
        ∫ s in (0 : ℝ)..t, (Real.sqrt (x s)*z s-ν*d s)/Real.sqrt (x s+ε^2) := by
  have hpos (s : ℝ) : 0 < x s+ε^2 := add_pos_of_nonneg_of_pos (hx0 s) (sq_pos_of_pos hε)
  have hc : Continuous (fun s => (Real.sqrt (x s)*z s-ν*d s)/Real.sqrt (x s+ε^2)) :=
    ((hx.sqrt.mul hz).sub (continuous_const.mul hd)).div
      ((hx.add continuous_const).sqrt) (fun s => (Real.sqrt_pos.mpr (hpos s)).ne')
  intro t ht
  refine ⟨hc.intervalIntegrable _ _, ?_⟩
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1
    ((hx.add continuous_const).sqrt.continuousOn)
    (fun s hs => (((hder s ⟨hs.1, hs.2.trans_le ht.2⟩).add_const (ε^2)).sqrt
      (hpos s).ne').hasDerivWithinAt)
    (hc.integrableOn_Icc) (fun s hs => ?_)
  · simpa only [Pi.add_apply] using (sub_le_iff_le_add.mp h).trans_eq (add_comm _ _)
  · have hb := hbound s ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hsqrt := Real.sqrt_pos.mpr (hpos s)
    change (2*p s-2*ν*d s)/(2*Real.sqrt (x s+ε^2)) ≤ _
    rw [div_le_div_iff₀ (by positivity) hsqrt]
    nlinarith

/-- The actual level-n signed regularized-root inequality, with the complete
negative gradient square retained. -/
theorem regularized_signed_energy_inequality {q : ℕ} (hq : 6 ≤ q) (n : ℕ)
    {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (p : C(Icc (0 : ℝ) T, SobolevSpace 1 q))
    (hp : ∀ t, value 1 (p t) ∈ gradientSpace 1 1 0) {ε : ℝ} (hε : 0 < ε) :
    let r := extendPath T hT (signedApproximationRoot n u)
    let z := extendPath T hT (signedApproximationForcing hq n u
      (sourcePath (D.comp (timeInclusion hTS)) u) p)
    let d := extendPath T hT (signedApproximationDissipation n u)
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s => (r s*z s-ν*d s)/Real.sqrt ((r s)^2+ε^2)) volume 0 t ∧
      Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) +
        ∫ s in (0 : ℝ)..t, (r s*z s-ν*d s)/Real.sqrt ((r s)^2+ε^2) := by
  let e := fun (W : SobolevWord (q+1)) s => value 1 (extendPath T hT (signedWordPath n u W) s)
  let f := fun (W : SobolevWord (q+1)) s => extendPath T hT
    (sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
      (sourcePath (D.comp (timeInclusion hTS)) u)) s
  let x := fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1)) (fun W => e W s)
  let b := fun s => ∑ W, ⟪e W s, f W s⟫_ℝ
  have he (W) : Continuous (e W) :=
    (valueOperator 1 2).continuous.comp (extendPath_continuous T hT (signedWordPath n u W))
  have hf (W) : Continuous (f W) := extendPath_continuous T hT _
  have hx : Continuous x := continuous_finsetSum _ (fun W _ => (he W).inner (he W))
  have hb : Continuous b := continuous_finsetSum _ (fun W _ => (he W).inner (hf W))
  have hx0 (s) : 0 ≤ x s := by
    dsimp [x, familyEnergy]
    simp only [real_inner_self_eq_norm_sq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq (s) : (extendPath T hT (signedApproximationRoot n u) s)^2 = x s := by
    change (signedApproximationRoot n u _)^2 = _
    rw [signedApproximationRoot_apply, familyNorm_sq]
    simp only [x, familyEnergy, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    rfl
  have hroot (s) : Real.sqrt (x s) = extendPath T hT (signedApproximationRoot n u) s := by
    rw [← hsq, Real.sqrt_sq]
    exact Real.sqrt_nonneg _
  have hder (s) (hs : s ∈ Ioo 0 T) : HasDerivAt x
      (2*b s-2*ν*extendPath T hT (signedApproximationDissipation n u) s) s := by
    have hh := regularized_full_energy_hasDerivAt n hν hT hTS D u₀ u hu s hs
    convert hh using 1
    · rfl
    · dsimp only [b, e, f, signedApproximationDissipation, extendPath, ContinuousMap.coe_mk]
      simp only [toJet_word 1 _ (by norm_num : 1 ≤ 2)]
      rfl
  have hbound (s) (_hs : s ∈ Icc 0 T) : b s ≤ Real.sqrt (x s) *
      extendPath T hT (signedApproximationForcing hq n u
        (sourcePath (D.comp (timeInclusion hTS)) u) p) s := by
    rw [hroot]
    exact signed_source_pairing_le hq n u _ p hdiv hp _
  have H := signed_scalar_integral hT hε x b
    (extendPath T hT (signedApproximationDissipation n u))
    (extendPath T hT (signedApproximationForcing hq n u
      (sourcePath (D.comp (timeInclusion hTS)) u) p)) hx hb
    (extendPath_continuous T hT _) (extendPath_continuous T hT _) hx0 hder hbound
  simpa only [hsq, hroot] using H

/-- Restriction to a fixed subinterval is continuous in scalar time L². -/
theorem signed_subintervalWeight_tendsto {T a b : ℝ} {v : ℕ → TimeLp T ℝ}
    {w : TimeLp T ℝ} (h : Filter.Tendsto v Filter.atTop (𝓝 w)) :
    Filter.Tendsto (fun n => EulerTimeLpSubinterval.subintervalWeight T a b (v n))
      Filter.atTop (𝓝 (EulerTimeLpSubinterval.subintervalWeight T a b w)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp h)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (EulerTimeLpSubinterval.subintervalWeight T a b (v n))
    (EulerTimeLpSubinterval.subintervalWeight T a b w), Lp.coeFn_sub (v n) w,
    EulerTimeLpSubinterval.subintervalWeight_ae T a b (v n),
    EulerTimeLpSubinterval.subintervalWeight_ae T a b w] with s hs hv hn hw
  simp only [hs, hv, Pi.sub_apply, hn, hw]
  by_cases hmem : s ∈ Icc a b <;> simp [hmem]

/-- A varying continuous coefficient and a strong L² forcing have convergent
products on every closed subinterval. No pointwise domination is asserted. -/
theorem signed_forcing_integral_tendsto {T t : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T)
    (c : ℕ → C(Icc (0 : ℝ) T, ℝ)) (c₀ : C(Icc (0 : ℝ) T, ℝ))
    (z : ℕ → C(Icc (0 : ℝ) T, ℝ)) (Z : TimeLp T ℝ)
    (hc : Filter.Tendsto c Filter.atTop (𝓝 c₀))
    (hz : Filter.Tendsto (fun n => pathLp T hT (z n)) Filter.atTop (𝓝 Z)) :
    IntervalIntegrable (fun s => extendPath T hT c₀ s * Z s) volume 0 t ∧
    Filter.Tendsto (fun n => ∫ s in (0 : ℝ)..t,
      extendPath T hT (c n) s * extendPath T hT (z n) s) Filter.atTop
      (𝓝 (∫ s in (0 : ℝ)..t, extendPath T hT c₀ s * Z s)) := by
  have hi := (Lp.memLp (pathLp T hT c₀)).integrable_mul (Lp.memLp Z)
  have hie : (fun s => pathLp T hT c₀ s * Z s) =ᵐ[timeMeasure T]
      (fun s => extendPath T hT c₀ s * Z s) := by
    filter_upwards [pathLp_ae T hT c₀] with s hs
    rw [hs]
  have hi₀ : IntegrableOn (fun s => extendPath T hT c₀ s * Z s) (Icc 0 T) := hi.congr hie
  have hint : IntegrableOn (fun s => extendPath T hT c₀ s * Z s) (Icc 0 t) :=
    hi₀.mono_set (Icc_subset_Icc_right ht.2)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr hint, ?_⟩
  have H := (signed_subintervalWeight_tendsto (a := 0) (b := t)
    (pathLp_tendsto T hT c c₀ hc)).inner (𝕜 := ℝ) hz
  rw [EulerTimeLpSubinterval.subinterval_inner_eq] at H
  have heq : (∫ s in Icc 0 t, pathLp T hT c₀ s * Z s ∂timeMeasure T) =
      ∫ s in (0 : ℝ)..t, extendPath T hT c₀ s * Z s := by
    rw [integral_congr_ae (ae_restrict_of_ae hie)]
    change (∫ s, _ ∂(volume.restrict (Icc 0 T)).restrict (Icc 0 t)) = _
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc_right ht.2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
  simpa only [EulerTimeLpSubinterval.subinterval_path_inner T hT 0 t le_rfl ht.1 ht.2,
    heq] using H

/-- Uniform root convergence survives the regularized quotient coefficient. -/
def signedRootCoefficient {T : ℝ} (ε : ℝ) (hε : 0 < ε)
    (r : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => r t / Real.sqrt ((r t)^2+ε^2), r.continuous.div
    ((r.continuous.pow 2).add continuous_const).sqrt (fun _ => by positivity)⟩

theorem signedRootCoefficient_tendsto {T ε : ℝ} (hε : 0 < ε)
    {r : ℕ → C(Icc (0 : ℝ) T, ℝ)} {r₀ : C(Icc (0 : ℝ) T, ℝ)}
    (hr : Filter.Tendsto r Filter.atTop (𝓝 r₀)) :
    Filter.Tendsto (fun n => signedRootCoefficient ε hε (r n)) Filter.atTop
      (𝓝 (signedRootCoefficient ε hε r₀)) := by
  have hc : Continuous (signedRootCoefficient (T := T) ε hε) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.div ((continuous_eval.pow 2).add continuous_const).sqrt
      (fun _ => by positivity)
  exact hc.continuousAt.tendsto.comp hr

/-- Strong forcing convergence for the very same maximal representative used
in the target. The pressure/source representatives are supplied by lane 198. -/
theorem signedApproximationForcing_tendsto {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
      Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => pathLp T hT (signedApproximationForcing hq n u
      (nonlinearSource hq hTS (sobolevPath F hF q) u)
      (energyPressurePath hq hTS (sobolevPath F hF q) u))) Filter.atTop
      (𝓝 (cylinderEnergyForcing hq hT hTS F hF u U)) := by
  let W := EulerSobolevWordValueIdentity.reindexMaximalTime 1 q T U
  have hW := EulerSobolevWordValueIdentity.reindexMaximalTime_restriction 1 T hT u U hU
  have hs := ForcedSourceUpgrade.sourceTime_restriction hq hT hTS
    (sobolevPath F hF (q+1)) u W hW
  have hp := energyPressureTime_restriction hq hT hTS
    (sobolevPath F hF (q+1)) u W hW
  rw [energy_force_restriction] at hs hp
  have H := regularizedWeightedForcing_tendsto 1
    (fun (_ : Unit) (W : SobolevWord (q+1)) => W.1.val)
    (fun _ W => W.2) (fun _ W => Nat.le_of_lt_succ W.1.isLt) T hT
    (fun _ => gevreyWeightPath T (ContinuousMap.const _ 1) 0)
    (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
    (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) u _ _ U _ _ hU hs hp
  convert H using 1
  · funext n
    congr 1
    apply ContinuousMap.ext
    intro t
    simp only [EulerWeightedForcingTime.weightedForcingPath_apply, Finset.univ_unique,
      Finset.sum_singleton, gevreyWeightPath, ContinuousMap.coe_mk,
      ContinuousMap.const_apply, EulerPacketWeights.weight, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, div_one, one_mul]
    rfl
  · rfl

/-- Joint continuity of a varying continuous scalar weight acting on time L². -/
theorem signed_scalar_multiplier_tendsto {T : ℝ} (hT : 0 ≤ T)
    {c : ℕ → C(Icc (0 : ℝ) T, ℝ)} {c₀ : C(Icc (0 : ℝ) T, ℝ)}
    {v : ℕ → TimeLp T ℝ} {v₀ : TimeLp T ℝ}
    (hc : Filter.Tendsto c Filter.atTop (𝓝 c₀)) (hv : Filter.Tendsto v Filter.atTop (𝓝 v₀)) :
    Filter.Tendsto (fun n => scalarTimeMultiplier T hT (c n) (v n)) Filter.atTop
      (𝓝 (scalarTimeMultiplier T hT c₀ v₀)) := by
  have hb (n : ℕ) : ‖scalarTimeMultiplier T hT (c n) (v n) - scalarTimeMultiplier T hT c₀ (v n)‖ ≤
      ‖c n-c₀‖ * ‖v n‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (scalarTimeMultiplier T hT (c n) (v n))
      (scalarTimeMultiplier T hT c₀ (v n)), scalarTimeMultiplier_ae T hT (c n) (v n),
      scalarTimeMultiplier_ae T hT c₀ (v n)] with s hs hn h₀
    simp only [hs, Pi.sub_apply, hn, h₀, ← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm (c n-c₀) _) (norm_nonneg _)
  have hz : Filter.Tendsto (fun n => ‖c n-c₀‖ * ‖v n‖) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_iff_norm_sub_tendsto_zero.mp hc).mul hv.norm
  have he := tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hb hz)
  have hh := he.add ((scalarTimeMultiplier T hT c₀).continuous.continuousAt.tendsto.comp hv)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hh

/-- Weighted squared norms converge on subintervals by scalar L² pairings. -/
theorem signed_weighted_square_limit {V : Type*} [NormedAddCommGroup V]
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc (0 : ℝ) T)
    {c : ℕ → C(Icc (0 : ℝ) T, ℝ)} {c₀ : C(Icc (0 : ℝ) T, ℝ)}
    {v : ℕ → TimeLp T V} {v₀ : TimeLp T V}
    (hc : Filter.Tendsto c Filter.atTop (𝓝 c₀)) (hv : Filter.Tendsto v Filter.atTop (𝓝 v₀)) :
    IntervalIntegrable (fun s => extendPath T hT c₀ s * ‖v₀ s‖^2) volume 0 t ∧
    Filter.Tendsto (fun n => ∫ s in (0 : ℝ)..t, extendPath T hT (c n) s * ‖v n s‖^2)
      Filter.atTop (𝓝 (∫ s in (0 : ℝ)..t, extendPath T hT c₀ s * ‖v₀ s‖^2)) := by
  let N : TimeLp T V → TimeLp T ℝ := lipschitzWith_one_norm.compLp (norm_zero)
  have hN : Filter.Tendsto (fun n => N (v n)) Filter.atTop (𝓝 (N v₀)) :=
    (lipschitzWith_one_norm.continuous_compLp norm_zero).continuousAt.tendsto.comp hv
  have hNa (w : TimeLp T V) : (N w : ℝ → ℝ) =ᵐ[timeMeasure T] fun s => ‖w s‖ :=
    lipschitzWith_one_norm.coeFn_compLp norm_zero w
  let M := fun (a : C(Icc (0 : ℝ) T, ℝ)) (w : TimeLp T V) => scalarTimeMultiplier T hT a (N w)
  have hMa (a : C(Icc (0 : ℝ) T, ℝ)) (w : TimeLp T V) :
      (fun s => M a w s * N w s) =ᵐ[timeMeasure T] fun s => extendPath T hT a s * ‖w s‖^2 := by
    filter_upwards [scalarTimeMultiplier_ae T hT a (N w), hNa w] with s hm hn
    rw [hm, hn, pow_two, mul_assoc]
  have hi : IntegrableOn (fun s => extendPath T hT c₀ s * ‖v₀ s‖^2) (Icc 0 T) :=
    ((Lp.memLp (M c₀ v₀)).integrable_mul (Lp.memLp (N v₀))).congr (hMa c₀ v₀)
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
    (hi.mono_set (Icc_subset_Icc_right ht.2)), ?_⟩
  have he (a : C(Icc (0 : ℝ) T, ℝ)) (w : TimeLp T V) :
      ⟪EulerTimeLpSubinterval.subintervalWeight T 0 t (M a w), N w⟫_ℝ =
        ∫ s in (0 : ℝ)..t, extendPath T hT a s * ‖w s‖^2 := by
    rw [EulerTimeLpSubinterval.subinterval_inner_eq,
      integral_congr_ae (ae_restrict_of_ae (hMa a w))]
    change (∫ s, _ ∂(volume.restrict (Icc 0 T)).restrict (Icc 0 t)) = _
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc_right ht.2),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
  have H := (signed_subintervalWeight_tendsto (a := 0) (b := t)
    (signed_scalar_multiplier_tendsto hT hc hN)).inner (𝕜 := ℝ) hN
  change Filter.Tendsto (fun n => ⟪EulerTimeLpSubinterval.subintervalWeight T 0 t (M (c n) (v n)), N (v n)⟫_ℝ)
    Filter.atTop (𝓝 ⟪EulerTimeLpSubinterval.subintervalWeight T 0 t (M c₀ v₀), N v₀⟫_ℝ) at H
  simpa only [he] using H

/-- Every energy word and each of its four derivatives as one Hilbert family. -/
def signedGradientOperator (q : ℕ) : SobolevSpace 1 (2+q) →L[ℝ]
    PiLp 2 (fun _ : SobolevWord (q+1) × Fin 4 => LiftL2 1) :=
  EulerFamilyNormTime.familyHilbertMap.comp (ContinuousLinearMap.pi fun Wi =>
    ((valueOperator 1 0).comp (derivativeOperator 1 0 Wi.2)).comp
      (boundedWordBlock 1 1 Wi.1.1.val (by have := Wi.1.1.isLt; omega) Wi.1.2))

/-- The coordinate is the genuine derivative with its direction prepended. -/
theorem signedGradientOperator_apply {q : ℕ} (v : SobolevSpace 1 (2+q))
    (W : SobolevWord (q+1)) (i : Fin 4) : signedGradientOperator q v (W,i) =
      word 1 v (by have := W.1.isLt; omega) (Fin.cons i W.2) := by
  change value 1 (derivativeOperator 1 0 i (boundedWordBlock 1 1 W.1.val _ W.2 v)) = _
  have h := derivativeOperator_hasDerivAt 1 i (boundedWordBlock 1 1 W.1.val
    (by have := W.1.isLt; omega) W.2 v)
  rw [boundedWordBlock_value] at h
  exact h.unique (word_hasDerivAt 1 v (by have := W.1.isLt; omega) W.2 i)

/-- Appending or prepending directions enumerates the same full word family. -/
theorem signedGradientOperator_norm_sq {q : ℕ} (v : SobolevSpace 1 (2+q)) :
    ‖signedGradientOperator q v‖^2 = ∑ i : Fin 4, ∑ W : SobolevWord (q+1),
      ‖(derivativeOperator 1 (q+1) i (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) v)).val W‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [signedGradientOperator_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4)))]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro m _
  let f := fun w : Fin (m.val+1) → Fin 4 => ‖word 1 v (by have := m.isLt; omega) w‖^2
  change (∑ w : Fin m.val → Fin 4, ∑ i : Fin 4, f (Fin.cons i w)) =
    ∑ w : Fin m.val → Fin 4, ∑ i : Fin 4, f (Fin.snoc w i)
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  have hc := (Fin.consEquiv (fun _ : Fin (m.val+1) => Fin 4)).sum_comp f
  have hs := (Fin.snocEquiv (fun _ : Fin (m.val+1) => Fin 4)).sum_comp f
  rw [Fintype.sum_prod_type] at hc hs
  exact hc.trans hs.symm

/-- The finite-level dissipation is exactly the Hilbert gradient-family norm. -/
theorem signedApproximationDissipation_eq {q : ℕ} {T : ℝ} (n : ℕ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) T) :
    signedApproximationDissipation n u t = ‖signedGradientOperator q (maximalApproximation 1 q T n u t)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro W _
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  have h := congrArg (fun p : C(Icc (0 : ℝ) T, SobolevSpace 1 1) => p t)
    (regularizedWordPath_first_eq 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T u)
  change truncateOperator 1 1 (signedWordPath n u W t) =
    boundedWordBlock 1 1 W.1.val _ W.2 (maximalApproximation 1 q T n u t) at h
  change word 1 (signedWordPath n u W t) _ (fun _ => i) =
    value 1 (derivativeOperator 1 0 i (boundedWordBlock 1 1 W.1.val _ W.2
      (maximalApproximation 1 q T n u t)))
  rw [← h]
  change (signedWordPath n u W t).val ⟨⟨1, _⟩, fun _ => i⟩ =
    (signedWordPath n u W t).val ⟨⟨1, _⟩, Fin.snoc Fin.elim0 i⟩
  congr 2

/-- Identification with the prescribed maximal-limit gradient representative. -/
theorem signedGradientOperator_ae {q : ℕ} {T : ℝ} (U : TimeLp T (SobolevSpace 1 (2+q))) :
    (fun s => ‖((signedGradientOperator q).compLpL 2 (timeMeasure T) U) s‖^2) =ᵐ[timeMeasure T]
      fun s => (energyGradientNorm U s)^2 := by
  filter_upwards [(signedGradientOperator q).coeFn_compLpL U,
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U] with s hs hr
  rw [hs, signedGradientOperator_norm_sq]
  change reindexMaximalTime 1 q T U s = _ at hr
  simp only [energyGradientNorm, hr]
  symm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The inverse regularized-root weight is a continuous function of the entire
continuous path, in its uniform topology. -/
def signedInverseRoot {T : ℝ} (ε : ℝ) (hε : 0 < ε)
    (r : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun t => (Real.sqrt ((r t)^2+ε^2))⁻¹,
    ((r.continuous.pow 2).add continuous_const).sqrt.inv₀ (fun t => by
      change Real.sqrt ((r t)^2+ε^2) ≠ 0
      positivity)⟩

/-- Strong time L² and uniform root convergence retain the full dissipation,
with the varying inverse root, on every closed subinterval. -/
theorem maximal_weighted_dissipation_limit {q : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
      Filter.atTop (𝓝 U)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    let r := extendPath T hT (energyRootPath u)
    IntervalIntegrable (fun s => (energyGradientNorm U s)^2 /
      Real.sqrt ((r s)^2+ε^2)) volume 0 t ∧
    Filter.Tendsto (fun n => ∫ s in (0 : ℝ)..t,
      extendPath T hT (signedApproximationDissipation n u) s /
        Real.sqrt ((extendPath T hT (signedApproximationRoot n u) s)^2+ε^2))
      Filter.atTop (𝓝 (∫ s in (0 : ℝ)..t,
        (energyGradientNorm U s)^2 / Real.sqrt ((r s)^2+ε^2))) := by
  let D := signedGradientOperator q
  let v := fun n => D.compLpL 2 (timeMeasure T) (pathLp T hT (maximalApproximation 1 q T n u))
  let V := D.compLpL 2 (timeMeasure T) U
  let c := fun n => signedInverseRoot ε hε (signedApproximationRoot n u)
  let c₀ := signedInverseRoot ε hε (energyRootPath u)
  have hcont : Continuous (signedInverseRoot (T := T) ε hε) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_eval.pow 2).add continuous_const).sqrt.inv₀ (fun p => by
      change Real.sqrt ((p.1 p.2)^2+ε^2) ≠ 0
      positivity)
  have hc : Filter.Tendsto c Filter.atTop (𝓝 c₀) :=
    hcont.continuousAt.tendsto.comp (signedApproximationRoot_tendsto u)
  have hv : Filter.Tendsto v Filter.atTop (𝓝 V) :=
    (D.compLpL 2 (timeMeasure T)).continuous.continuousAt.tendsto.comp hU
  obtain ⟨hi, hl⟩ := signed_weighted_square_limit hT ht hc hv
  have hsub {f g : ℝ → ℝ} (h : f =ᵐ[timeMeasure T] g) :
      f =ᵐ[volume.restrict (uIoc 0 t)] g := by
    rw [uIoc_of_le ht.1]
    exact ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)) h
  have he : (fun s => extendPath T hT c₀ s * ‖V s‖^2) =ᵐ[volume.restrict (uIoc 0 t)]
      (fun s => (energyGradientNorm U s)^2 /
        Real.sqrt ((extendPath T hT (energyRootPath u) s)^2+ε^2)) := by
    apply hsub
    filter_upwards [signedGradientOperator_ae U] with s hs
    change _ * ‖((signedGradientOperator q).compLpL 2 (timeMeasure T) U) s‖^2 = _
    rw [hs]
    exact (div_eq_inv_mul _ _).symm
  have hen (n : ℕ) : (fun s => extendPath T hT (c n) s * ‖v n s‖^2)
      =ᵐ[volume.restrict (uIoc 0 t)] fun s =>
        extendPath T hT (signedApproximationDissipation n u) s /
          Real.sqrt ((extendPath T hT (signedApproximationRoot n u) s)^2+ε^2) := by
    apply hsub
    filter_upwards [D.coeFn_compLpL (pathLp T hT (maximalApproximation 1 q T n u)),
      pathLp_ae T hT (maximalApproximation 1 q T n u)] with s hd hp
    change _ * ‖(D.compLpL 2 (timeMeasure T) (pathLp T hT (maximalApproximation 1 q T n u))) s‖^2 = _
    rw [hd, hp]
    change _ * ‖signedGradientOperator q (maximalApproximation 1 q T n u (projIcc 0 T hT s))‖^2 = _
    rw [← signedApproximationDissipation_eq]
    exact (div_eq_inv_mul _ _).symm
  refine ⟨(intervalIntegrable_congr_ae he).mp hi, ?_⟩
  have hne := fun n => intervalIntegral.integral_congr_ae_restrict (hen n)
  have hle := intervalIntegral.integral_congr_ae_restrict he
  simpa only [hne, hle] using hl

/-- Unconditional signed passage for every solenoidal mild competitor and its
actual strong maximal limit, including both closed endpoints. -/
theorem cylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) :
    CylinderSignedEnergyPassage hq hν a ha F hF := by
  intro T hT hTS u hu U hU ε hε
  dsimp only
  intro t ht
  let r := extendPath T hT (energyRootPath u)
  let rn := fun n => extendPath T hT (signedApproximationRoot n u)
  let zn := fun n => signedApproximationForcing hq n u
    (nonlinearSource hq hTS (sobolevPath F hF q) u)
    (energyPressurePath hq hTS (sobolevPath F hF q) u)
  let dn := fun n => extendPath T hT (signedApproximationDissipation n u)
  let Z := cylinderEnergyForcing hq hT hTS F hF u U
  let gn := fun n s => dn n s / Real.sqrt ((rn n s)^2+ε^2)
  let g := fun s => (energyGradientNorm U s)^2 / Real.sqrt ((r s)^2+ε^2)
  let fn := fun n s => rn n s / Real.sqrt ((rn n s)^2+ε^2) * extendPath T hT (zn n) s
  let f := fun s => r s / Real.sqrt ((r s)^2+ε^2) * Z s
  have hr := signedApproximationRoot_tendsto u
  obtain ⟨hfi, hfl⟩ := signed_forcing_integral_tendsto hT ht
    (fun n => signedRootCoefficient ε hε (signedApproximationRoot n u))
    (signedRootCoefficient ε hε (energyRootPath u)) zn Z
    (signedRootCoefficient_tendsto hε hr)
    (signedApproximationForcing_tendsto hq hT hTS F hF u U hU)
  change IntervalIntegrable f volume 0 t at hfi
  change Filter.Tendsto (fun n => ∫ s in (0 : ℝ)..t, fn n s) Filter.atTop
    (𝓝 (∫ s in (0 : ℝ)..t, f s)) at hfl
  obtain ⟨hgi, hgl⟩ := maximal_weighted_dissipation_limit hT u U hU hε t ht
  change IntervalIntegrable g volume 0 t at hgi
  change Filter.Tendsto (fun n => ∫ s in (0 : ℝ)..t, gn n s) Filter.atTop
    (𝓝 (∫ s in (0 : ℝ)..t, g s)) at hgl
  have hident : (fun s => (r s*Z s-ν*(energyGradientNorm U s)^2)/Real.sqrt ((r s)^2+ε^2)) =
      (fun s => f s-ν*g s) := by funext s; dsimp [f, g]; ring
  change IntervalIntegrable (fun s => (r s*Z s-ν*(energyGradientNorm U s)^2)/
      Real.sqrt ((r s)^2+ε^2)) volume 0 t ∧ _
  rw [hident]
  refine ⟨hfi.sub (hgi.const_mul ν), ?_⟩
  have hleft (s : ℝ) : Filter.Tendsto (fun n => Real.sqrt ((rn n s)^2+ε^2))
      Filter.atTop (𝓝 (Real.sqrt ((r s)^2+ε^2))) :=
    (((((continuous_eval_const (projIcc 0 T hT s)).continuousAt.tendsto.comp hr).pow 2).add
      tendsto_const_nhds).sqrt)
  have hnl (n : ℕ) : Real.sqrt ((rn n t)^2+ε^2) ≤ Real.sqrt ((rn n 0)^2+ε^2) +
      ((∫ s in (0 : ℝ)..t, fn n s) - ν*(∫ s in (0 : ℝ)..t, gn n s)) := by
    have hn := (regularized_signed_energy_inequality hq n hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u hu
      (energy_velocity_divergenceFree hq hν hT hTS a ha _ u hu)
      (energyPressurePath hq hTS (sobolevPath F hF q) u)
      (energyPressurePath_gradient hq hTS _ u) hε t ht).2
    have hfn : Continuous (fn n) :=
      (extendPath_continuous T hT (signedRootCoefficient ε hε (signedApproximationRoot n u))).mul
        (extendPath_continuous T hT (zn n))
    have hgn : Continuous (gn n) := (extendPath_continuous T hT _).div
      (((extendPath_continuous T hT _).pow 2).add continuous_const).sqrt (fun _ => by positivity)
    have hid : (fun s => (rn n s*extendPath T hT (zn n) s-ν*dn n s)/
        Real.sqrt ((rn n s)^2+ε^2)) = (fun s => fn n s-ν*gn n s) := by
      funext s; dsimp [fn, gn]; ring
    change Real.sqrt ((rn n t)^2+ε^2) ≤ Real.sqrt ((rn n 0)^2+ε^2) +
      ∫ s in (0 : ℝ)..t, (rn n s*extendPath T hT (zn n) s-ν*dn n s)/
        Real.sqrt ((rn n s)^2+ε^2) at hn
    rw [hid, intervalIntegral.integral_sub (hfn.intervalIntegrable _ _)
      ((hgn.intervalIntegrable _ _).const_mul ν), intervalIntegral.integral_const_mul] at hn
    exact hn
  have hl := le_of_tendsto_of_tendsto' (hleft t)
    ((hleft 0).add (hfl.sub (hgl.const_mul ν))) hnl
  rw [intervalIntegral.integral_sub hfi (hgi.const_mul ν), intervalIntegral.integral_const_mul]
  exact hl

/-- Root comparison after the proved signed passage; only the forcing bound
and its scalar sign condition remain. -/
theorem cylinderSignedRootLimit_of_forcingBound' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    CylinderSignedRootLimit hq hν a ha F hF E A :=
  cylinderSignedRootLimit_of_forcingBound hq hν a ha F hF hb hFB
    (cylinderSignedEnergyPassage hq hν a ha F hF)

/-- Finite-energy assembly retains the necessary initial normalization. -/
theorem finiteMildEnergy_of_forcingBound'' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A :=
  finiteMildEnergy_of_forcingBound' hq hν a ha F hF hE hFB
    (cylinderSignedEnergyPassage hq hν a ha F hF)

end NSFormalization.Section4.A01
