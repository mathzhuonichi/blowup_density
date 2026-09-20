import NSFormalization.Section4.A01.MildEnergyPremises
import Euler.RegularizedForcingRepresentative

/-! Full finite-word forcing: exact cancellation and a single spatial analytic residual.
The constants below are explicit candidate constants; their general-data validity is
conditional on `CylinderCommutatorBound`, not asserted unconditionally. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution EulerTimeLp
  EulerRegularizedTopBlocks EulerSobolevMaximalRegularity EulerSobolevWordConstraints
  EulerTimeSobolevTransport EulerAsymmetricTransport EulerSobolevTransport
  EulerRegularizedEnergyFamily EulerTransportL2Time EulerRegularizedMetricPaths
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerMildTopWord
  EulerSobolevWordValueIdentity EulerSobolevEnergyPaths
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Exact full-family comparison constant from lane 196. -/
def E (q : ℕ) : ℝ := mildNormConstant q

/-- Candidate commutator constant, with the full-family and tensor tame factors explicit.
No viscosity dependence is needed before Young absorption. -/
def A (q : ℕ) : ℝ := mildNormConstant q * (1 + A03.outerTameConst (q+1))

theorem E_nonneg (q : ℕ) : 0 ≤ E q := mildNormConstant_nonneg q

theorem A_nonneg (q : ℕ) : 0 ≤ A q :=
  mul_nonneg (mildNormConstant_nonneg q) (by have := A03.outerTameConst_pos (q+1); linarith)

/-- The nonlinear word family after exact Leray-complement cancellation.
Both arguments are finite-order Sobolev elements, never classical solutions. -/
def cylinderCommutator {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) :
    SobolevWord (q+1) → LiftL2 1 := fun w =>
  transportL2Bilinear 1 (by omega : 3 ≤ q+1) 1 0 v
    (boundedWordBlock 1 1 w.1.val (by have := w.1.isLt; omega) w.2 V) -
  (asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
    (velocityComponents_norm 1 0 (by norm_num) (by simp)) v
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w

/-- Leray source plus its pressure complement reconstructs the raw residual exactly. -/
theorem source_pressure_cancel (q : ℕ) (f b : SobolevSpace 1 (q+1)) :
    leray 1 (q+1) (f-b) + sobolevGradientProjection 1 (q+1) 1 0 (f-b) = f-b := by
  change (f-b) - sobolevGradientProjection 1 (q+1) 1 0 (f-b) + _ = _
  exact sub_add_cancel _ _

/-- Literal source-free spatial residual, with the actual derivative norm and restriction.
This is the ONE unproved analytic input. In particular it contains no force,
no time evolution, no all-order smooth representative, and no energy envelope. -/
def CylinderCommutatorBound (q : ℕ) (hq : 6 ≤ q) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    familyNorm (cylinderCommutator hq v V) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
          ‖(derivativeOperator 1 (q+1) i
            (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)

/-- Literal representative of the raw residual, without projection. -/
theorem energyRawTime_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (V : TimeLp T (SobolevSpace 1 ((q+1)+1))) :
  (energyRawTime hq hT hTS f u V : ℝ → SobolevSpace 1 (q+1)) =ᵐ[timeMeasure T] fun r =>
    extendPath T hT (f.comp (timeInclusion hTS)) r -
      asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
        (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u r) (V r) := by
  filter_upwards [Lp.coeFn_sub (pathLp T hT (f.comp (timeInclusion hTS)))
    (transportTime 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u V),
    pathLp_ae T hT (f.comp (timeInclusion hTS)),
    transportTime_ae 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u V] with r hs hf ht
  exact hs.trans (congrArg₂ (fun x y => x-y) hf ht)

-- The full dependent word specialization requires additional reduction fuel.
set_option maxHeartbeats 400000 in
/-- Identity metric, full words, literal source/transport/pressure representative. -/
theorem energyForcingNorm_ae {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (F P : TimeLp T (SobolevSpace 1 (q+1))) :
    (energyForcingNorm hq hT u U F P : ℝ → ℝ) =ᵐ[timeMeasure T] fun r =>
      familyNorm (fun w : SobolevWord (q+1) => (F r).val w +
        transportL2Bilinear 1 (by omega : 3 ≤ q+1) 1 0 (extendPath T hT u r)
          (boundedWordBlock 1 1 w.1.val (by have := w.1.isLt; omega) w.2 (U r)) +
        (P r).val w) := by
  have hz := EulerRegularizedForcingRepresentative.weighted_forcing_ae 1
    (fun (_ : Unit) (w : SobolevWord (q+1)) => w.1.val) (fun _ w => w.2)
    (fun _ w => Nat.le_of_lt_succ w.1.isLt) T hT
    (fun _ => gevreyWeightPath T (ContinuousMap.const _ 1) 0)
    (transportL2Path 1 (by omega : 3 ≤ q+1) 1 0 T u)
    (metricOperatorPath 1 T (fun _ => energyIdentity) continuous_const) U F P
  filter_upwards [hz] with r hr
  rw [show energyForcingNorm hq hT u U F P r = _ from hr]
  simp only [Finset.univ_unique, Finset.sum_singleton, gevreyWeightPath,
    extendPath, ContinuousMap.coe_mk, EulerPacketWeights.weight,
    pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, div_one,
    ContinuousMap.const_apply, one_mul]
  apply congrArg familyNorm
  funext w
  change _ + _ + energyIdentity.operator _ = _
  rw [show energyIdentity.operator = ContinuousLinearMap.id ℝ (LiftL2 1) from
    EulerConstantCorrection.coefficient_operator_id 1]
  rfl

-- Projection and Bochner representative coercions require additional reduction fuel.
set_option maxHeartbeats 400000 in
/-- Source and pressure cancel before taking any word-family norm. -/
theorem sourceTime_add_pressureTime_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (V : TimeLp T (SobolevSpace 1 ((q+1)+1))) :
    (fun r => ForcedSourceUpgrade.sourceTime hq hT hTS f u V r +
      energyPressureTime hq hT hTS f u V r) =ᵐ[timeMeasure T] fun r =>
        extendPath T hT (f.comp (timeInclusion hTS)) r -
        asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
          (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u r) (V r) := by
  let R := energyRawTime hq hT hTS f u V
  filter_upwards [(leray 1 (q+1)).coeFn_compLpL R,
    (sobolevGradientProjection 1 (q+1) 1 0).coeFn_compLpL R,
    energyRawTime_ae hq hT hTS f u V] with r hs hp hr
  have he : leray 1 (q+1) (R r) + sobolevGradientProjection 1 (q+1) 1 0 (R r) = R r :=
    sub_add_cancel _ _
  exact (congrArg₂ (fun x y : SobolevSpace 1 (q+1) => x+y) hs hp).trans (he.trans hr)

/-- Algebraic rearrangement before taking norms. -/
theorem forcing_array_rearrange {q : ℕ} (s p f b : SobolevSpace 1 (q+1))
    (t : SobolevWord (q+1) → LiftL2 1) (h : s+p = f-b) :
    (fun w => s.val w + t w + p.val w) = f.val + (t-b.val) := by
  funext w
  have hw : s.val w + p.val w = f.val w - b.val w := congrArg (fun z => z.val w) h
  change _ = f.val w + (t w - b.val w)
  rw [add_right_comm, hw]
  abel

-- Full dependent word-family elaboration needs extra reduction fuel.
set_option maxHeartbeats 400000 in
/-- The original Z is exactly the physical force-word family plus the commutator.
This identity holds without a mild equation or a choice of maximal limit. -/
theorem cylinderEnergyForcing_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q))) :
    (cylinderEnergyForcing hq hT hTS F hF u U : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun r => familyNorm ((extendPath T hT
        ((sobolevPath F hF (q+1)).comp (timeInclusion hTS)) r).val +
        cylinderCommutator hq (extendPath T hT u r) (U r)) := by
  let f := sobolevPath F hF (q+1)
  let V := reindexMaximalTime 1 q T U
  have hz := energyForcingNorm_ae hq hT u U
    (ForcedSourceUpgrade.sourceTime hq hT hTS f u V)
    (energyPressureTime hq hT hTS f u V)
  filter_upwards [hz, sourceTime_add_pressureTime_ae hq hT hTS f u V,
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U]
    with r hz hc hv
  rw [show cylinderEnergyForcing hq hT hTS F hF u U r = _ from hz]
  apply congrArg familyNorm
  change V r = _ at hv
  have hb := congrArg (fun z : SobolevSpace 1 ((q+1)+1) =>
    extendPath T hT (f.comp (timeInclusion hTS)) r -
      asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
        (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u r) z) hv
  exact forcing_array_rearrange _ _ _ _ _ (hc.trans hb)

/-- The physical source costs exactly lane 196's full word-family constant. -/
theorem force_word_norm_le {q : ℕ} {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1))) (r : ℝ) :
    familyNorm (extendPath T hT (f.comp (timeInclusion hTS)) r).val ≤ E q * ‖f‖ := by
  have he : familyNorm (extendPath T hT (f.comp (timeInclusion hTS)) r).val =
      euclideanWordNorm (extendPath T hT (f.comp (timeInclusion hTS)) r) := by
    rw [euclideanWordNorm_eq]
    rfl
  rw [he]
  exact (euclideanWordNorm_bounds _).2.trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) (E_nonneg q))

/-- Exact `ForcingFamilyBound` target, conditional solely on the stated finite spatial estimate. -/
theorem forcingFamilyBound_of_cylinder {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hcomm : CylinderCommutatorBound q hq) :
    ForcingFamilyBound hq hν a F hF (E q) (A q) := by
  intro T hT hTS u _hu U hU
  have hrestriction := EulerSobolevMaximalRegularity.maximal_limit_restriction 1 T hT u U hU
  filter_upwards [cylinderEnergyForcing_ae hq hT hTS F hF u U, hrestriction,
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U]
    with r hz hr hv
  have hc := hcomm (extendPath T hT u r) (U r) hr
  have hg : Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
      ‖(derivativeOperator 1 (q+1) i
        (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) (U r))).val w‖^2) =
      energyGradientNorm U r := by
    unfold energyGradientNorm
    change reindexMaximalTime 1 q T U r = _ at hv
    rw [hv]
  rw [hg] at hc
  have hadd (v w : SobolevWord (q+1) → LiftL2 1) :
      familyNorm (v+w) ≤ familyNorm v + familyNorm w := by
    rw [EulerFamilyNormTime.familyNorm_eq_piLp, EulerFamilyNormTime.familyNorm_eq_piLp,
      EulerFamilyNormTime.familyNorm_eq_piLp, map_add]
    exact norm_add_le _ _
  have hb := (hadd _ _).trans (add_le_add (force_word_norm_le hT hTS
    (sobolevPath F hF (q+1)) r) hc)
  rw [← hz] at hb
  have hx : 0 ≤ extendPath T hT (energyRootPath u) r := by
    change 0 ≤ energyRootPath u _
    rw [energyRootPath_apply, euclideanWordNorm_eq]
    exact Real.sqrt_nonneg _
  calc
    _ ≤ extendPath T hT (energyRootPath u) r *
        (E q * ‖sobolevPath F hF (q+1)‖ +
          A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u r)‖) * energyGradientNorm U r) :=
      mul_le_mul_of_nonneg_left hb hx
    _ = _ := by ring

end NSFormalization.Section4.A01
