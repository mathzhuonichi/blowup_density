import NSFormalization.Section4.A01.RootComparison

/-! Conditional signed passage. The remaining input is an unabsorbed, positive-
regularization energy inequality on the actual maximal limit. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal EulerQuadraticSourceLimit
  EulerTimeLp EulerRegularizedTopBlocks
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Strong time L² convergence preserves the full square integral. This applies
also to a derivative-word family once its strong convergence is supplied. -/
theorem strong_time_square_integral_limit {V : Type*} [NormedAddCommGroup V]
    {T : ℝ} {v : ℕ → TimeLp T V} {w : TimeLp T V}
    (h : Filter.Tendsto v Filter.atTop (𝓝 w)) :
    Filter.Tendsto (fun n => ∫ s, ‖v n s‖^2 ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ s, ‖w s‖^2 ∂timeMeasure T)) := by
  simpa only [← norm_sq_eq_integral] using h.norm.pow 2

/-- Spatial bounded maps commute with strong time-square passage, with the
literal pointwise representatives under the integral. -/
theorem mapped_time_square_integral_limit {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T : ℝ} (D : V →L[ℝ] W) {v : ℕ → TimeLp T V} {w : TimeLp T V}
    (h : Filter.Tendsto v Filter.atTop (𝓝 w)) :
    Filter.Tendsto (fun n => ∫ s, ‖D (v n s)‖^2 ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ s, ‖D (w s)‖^2 ∂timeMeasure T)) := by
  have he (z : TimeLp T V) :
      (∫ s, ‖(D.compLpL 2 (timeMeasure T) z) s‖^2 ∂timeMeasure T) =
        ∫ s, ‖D (z s)‖^2 ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [D.coeFn_compLpL z] with s hs
    rw [hs]
  simpa only [Function.comp_apply, he] using strong_time_square_integral_limit
    ((D.compLpL 2 (timeMeasure T)).continuous.continuousAt.tendsto.comp h)

/-- Every derivative word through q+2 has convergent square integral along the
actual maximal approximations. In particular this includes the extra gradient
of every energy word through q+1. No uniform tame bound in n is used. -/
theorem maximal_word_square_integral_limit {q m : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (hm : m ≤ 2+q) (w : Fin m → Fin 4)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
      Filter.atTop (𝓝 U)) :
    Filter.Tendsto (fun n => ∫ s,
      ‖word 1 (extendPath T hT (maximalApproximation 1 q T n u) s) hm w‖^2
        ∂timeMeasure T) Filter.atTop
      (𝓝 (∫ s, ‖word 1 (U s) hm w‖^2 ∂timeMeasure T)) := by
  let D := (valueOperator 1 0).comp
    (EulerMildTopWord.boundedWordBlock 1 0 m (by omega : 0+m ≤ 2+q) w)
  have hD (v : SobolevSpace 1 (2+q)) : D v = word 1 v hm w := by
    exact EulerMildTopWord.boundedWordBlock_value 1 _ _ _ _ _
  have h := mapped_time_square_integral_limit D hU
  simp only [hD] at h
  have he (n : ℕ) :
      (∫ s, ‖word 1 (pathLp T hT (maximalApproximation 1 q T n u) s) hm w‖^2
        ∂timeMeasure T) = ∫ s,
      ‖word 1 (extendPath T hT (maximalApproximation 1 q T n u) s) hm w‖^2
        ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [pathLp_ae T hT (maximalApproximation 1 q T n u)] with s hs
    rw [hs]
  simpa only [he] using h

/-- Young absorption before division. The forcing constant must be nonnegative;
no positivity of the unregularized root is required. -/
theorem signed_quotient_absorption {ν k r g z b ε : ℝ}
    (hν : 0 < ν) (hr : 0 ≤ r) (hb : 0 ≤ b) (hε : 0 < ε)
    (h : r*z ≤ k*r*g+b*r) :
    (r*z-ν*g^2) / Real.sqrt (r^2+ε^2) ≤ k^2/(4*ν)*r+b := by
  have hsq := sq_nonneg (2*ν*g-k*r)
  have hden : 0 < 4*ν := by positivity
  have hy : r*z-ν*g^2 ≤ k^2/(4*ν)*r^2+b*r := by
    have he : k^2/(4*ν)*(4*ν) = k^2 := div_mul_cancel₀ _ hden.ne'
    nlinarith [hsq]
  have hs : 0 < Real.sqrt (r^2+ε^2) := by positivity
  have hrs : r ≤ Real.sqrt (r^2+ε^2) := by
    have hh := Real.sqrt_le_sqrt (show r^2 ≤ r^2+ε^2 by nlinarith [sq_nonneg ε])
    simpa only [Real.sqrt_sq hr] using hh
  have hk : 0 ≤ k^2/(4*ν)*r+b := by positivity
  rw [div_le_iff₀ hs]
  calc
    r*z-ν*g^2 ≤ (k^2/(4*ν)*r+b)*r := by nlinarith [hy]
    _ ≤ (k^2/(4*ν)*r+b)*Real.sqrt (r^2+ε^2) :=
      mul_le_mul_of_nonneg_left hrs hk

/-- ONE analytic obligation: retain dissipation through the maximal limit at
fixed positive epsilon. Integrability is explicit. This makes no assumption on
E or A and does not assume a tame estimate, absorption, or root comparison.
Transport/pressure cancellation and the weighted gradient-square passage still
have to be proved to construct this predicate for general data. -/
def CylinderSignedEnergyPassage {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  let _solenoidal := ha
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation 1 q T n u))
        Filter.atTop (𝓝 U) →
    ∀ ε : ℝ, 0 < ε →
      let r := extendPath T hT (energyRootPath u)
      let H := fun s => (r s * cylinderEnergyForcing hq hT hTS F hF u U s -
        ν * (energyGradientNorm U s)^2) / Real.sqrt ((r s)^2+ε^2)
      ∀ t ∈ Icc (0 : ℝ) T,
        IntervalIntegrable H volume 0 t ∧
        Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) + ∫ s in (0 : ℝ)..t, H s

/-- The signed quotient estimate implies lane 201's exact residual. The scalar
sign condition is explicit: hFB alone places no constraint on E at a zero root. -/
theorem cylinderSignedRootLimit_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hb : 0 ≤ E * ‖sobolevPath F hF (q+1)‖)
    (hFB : ForcingFamilyBound hq hν a F hF E A)
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    CylinderSignedRootLimit hq hν a ha F hF E A := by
  intro T hT hTS u hu U hU _ t ht
  let r := extendPath T hT (energyRootPath u)
  let k := cylinderEnvelopeDriver hq hT A u
  let b := E * ‖sobolevPath F hF (q+1)‖
  have hr (s : ℝ) : 0 ≤ r s := by
    dsimp [r, extendPath]
    rw [energyRootPath_apply]
    exact Real.sqrt_nonneg _
  have hc : Continuous (fun s => k s^2/(4*ν)*r s+b) :=
    (((cylinderEnvelopeDriver_continuous hq hT A u).pow 2).div_const _).mul
      (extendPath_continuous T hT (energyRootPath u)) |>.add continuous_const
  have hh (ε : ℝ) (hε : 0 < ε) :
      Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) +
        ∫ s in (0 : ℝ)..t, (k s^2/(4*ν)*r s+b) := by
    obtain ⟨hi, he⟩ := hpass T hT hTS u hu U hU ε hε t ht
    apply he.trans
    apply add_le_add_right
    apply intervalIntegral.integral_mono_ae_restrict ht.1 hi (hc.intervalIntegrable _ _)
    have hf := hFB T hT hTS u hu U hU
    have hf' := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc_right ht.2) hf
    filter_upwards [hf'] with s hs
    exact signed_quotient_absorption hν (hr s) hb hε hs
  have hl : Continuous (fun ε : ℝ => Real.sqrt ((r t)^2+ε^2)) := by fun_prop
  have hu' : Continuous (fun ε : ℝ => Real.sqrt ((r 0)^2+ε^2) +
      ∫ s in (0 : ℝ)..t, (k s^2/(4*ν)*r s+b)) := by fun_prop
  have hlim := le_of_tendsto_of_tendsto
    (hl.continuousAt.continuousWithinAt.tendsto (s := Ioi 0) (x := 0))
    (hu'.continuousAt.continuousWithinAt.tendsto (s := Ioi 0) (x := 0))
    (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => hh ε hε)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq (hr t), Real.sqrt_sq (hr 0)] at hlim
  simpa only [r, k, b, extendPath, projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)]
    using hlim

/-- Assembly retains lane 201's necessary initial normalization. -/
theorem finiteMildEnergy_of_forcingBound' {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hFB : ForcingFamilyBound hq hν a F hF E A)
    (hpass : CylinderSignedEnergyPassage hq hν a ha F hF) :
    FiniteMildEnergy hq hν a ha F hF E A := by
  exact finiteMildEnergy_of_forcingBound hq hν a ha F hF hE
    (cylinderSignedRootLimit_of_forcingBound hq hν a ha F hF
      (mul_nonneg ((mildNormConstant_nonneg q).trans hE) (norm_nonneg _)) hFB hpass) hFB
end NSFormalization.Section4.A01
