import NSFormalization.Section4.A01.MildEnergyPremises

/-! The scalar dissipative envelope. The cylinder comparison remains an explicit input. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open EulerQuadraticSourceLimit EulerCylinderSobolev EulerMetricHeatEnergy EulerSpatialSobolevInverse EulerLiftedWeakDerivative
  EulerPressureSpatialRegularity EulerFiniteMetricEnergy
open scoped InnerProductSpace

/-- Identity metric retains the entire negative gradient square, without Young's inequality. -/
theorem identity_jetLaplacian_pairing (f : LiftL2 1)
    (J : SpatialJet 1 standardDirection 2 f) :
    ⟪f, jetLaplacian 1 J⟫_ℝ = - ∑ i : Fin 4, ‖J.word (fun _ : Fin 1 => i)‖^2 := by
  have hfirst (i : Fin 4) : HasDerivAt
      (fun t => translation 1 (translationPath 1 (standardDirection i) t) f)
      (J.word (fun _ : Fin 1 => i)) 0 := by
    have hw : Fin.cons i (Fin.elim0 : Fin 0 → Fin 4) = (fun _ : Fin 1 => i) := by
      funext j
      fin_cases j
      rfl
    simpa only [SpatialJet.word_zero, hw] using
      J.word_hasDerivAt (by omega : 0 < 2) (Fin.elim0 : Fin 0 → Fin 4) i
  have hsecond (i : Fin 4) : HasDerivAt
      (fun t => translation 1 (translationPath 1 (standardDirection i) t)
        (J.word (fun _ : Fin 1 => i))) (J.word (fun _ : Fin 2 => i)) 0 := by
    convert J.word_hasDerivAt (by omega : 1 < 2) (fun _ : Fin 1 => i) i using 1
    congr 1
    funext j
    cases j using Fin.cases <;> rfl
  have hz (i : Fin 4) : directionalCoefficientOperator 1 energyIdentity
      (standardDirection i) f = 0 := by
    apply norm_le_zero_iff.mp
    simpa [energyIdentity, EulerConstantCorrection.coefficient] using
      directionalCoefficientOperator_bound 1 energyIdentity (standardDirection i) f
  have hi (i : Fin 4) := metric_second_derivative_identity 1 energyIdentity
    (standardDirection i) f _ _ (hfirst i) (hsecond i)
  simp only [hz, inner_zero_left, sub_zero] at hi
  simp only [energyIdentity, EulerConstantCorrection.coefficient_operator_id,
    ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at hi
  simp only [jetLaplacian, inner_sum, hi, Finset.sum_neg_distrib]

/-- The exact signed full-word identity. Its derivative premises can be supplied
by `regularized_word_hasDerivAt_clamped`; no transport or pressure bound is used. -/
theorem full_word_energy_hasDerivAt {q : ℕ} (e : SobolevWord (q+1) → ℝ → LiftL2 1)
    (t ν : ℝ) (f : SobolevWord (q+1) → LiftL2 1)
    (J : ∀ W, SpatialJet 1 standardDirection 2 (e W t))
    (he : ∀ W, HasDerivAt (e W) (ν • jetLaplacian 1 (J W) + f W) t) :
    HasDerivAt (fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1)) (fun W => e W s))
      (2 * ∑ W, ⟪e W t, f W⟫_ℝ -
        2 * ν * ∑ W, ∑ i : Fin 4, ‖(J W).word (fun _ : Fin 1 => i)‖^2) t := by
  have h := family_energy_hasDerivAt
    (fun _ => ContinuousLinearMap.id ℝ (LiftL2 1)) e t ν 0
    (fun W => ν • jetLaplacian 1 (J W) + f W) (fun _ => 0) (fun _ => 0) f
    (fun W => jetLaplacian 1 (J W)) (hasDerivAt_const t _) he
    (fun _ _ => rfl) (fun W => by simp [add_comm]) (fun _ => by simp)
  convert h using 1
  simp only [zero_apply, ContinuousLinearMap.id_apply,
    inner_zero_left, inner_zero_right, zero_add, mul_zero, sub_zero, inner_add_right,
    real_inner_smul_right, identity_jetLaplacian_pairing]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

/-- The signed identity for the actual regularized mild competitor, at the full
energy order. This supplies the regularized starting point, not its signed limit. -/
theorem regularized_full_energy_hasDerivAt {q : ℕ} (n : ℕ)
    {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let v := fun (W : SobolevWord (q+1)) r => extendPath T hT
      (EulerRegularizedWordEquation.regularizedWordPath 1
        (Nat.le_of_lt_succ W.1.isLt) n W.2 T u) r
    let f := fun W : SobolevWord (q+1) => extendPath T hT
      (EulerRegularizedWordTime.sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
        (sourcePath (D.comp (timeInclusion hTS)) u)) t
    HasDerivAt (fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1))
      (fun W => value 1 (v W s)))
      (2 * ∑ W, ⟪value 1 (v W t), f W⟫_ℝ -
        2 * ν * ∑ W, ∑ i : Fin 4, ‖(toJet 1 (v W t)).word (fun _ : Fin 1 => i)‖^2) t := by
  dsimp only
  apply full_word_energy_hasDerivAt
  intro W
  exact EulerRegularizedForcingWord.regularized_word_hasDerivAt_clamped 1
    (Nat.le_of_lt_succ W.1.isLt) n W.2 ν hν T hT u₀
    (sourcePath (D.comp (timeInclusion hTS)) u) u hu t ht

/-- Variation of constants for the scalar comparison equation. -/
def energyComparison (α : ℝ → ℝ) (b c t : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, α s) *
    (c + b * ∫ s in (0 : ℝ)..t, Real.exp (-(∫ r in (0 : ℝ)..s, α r)))

/-- The comparison solves the ODE at every real time. -/
theorem energyComparison_hasDerivAt {α : ℝ → ℝ} (hα : Continuous α)
    (b c t : ℝ) : HasDerivAt (energyComparison α b c)
      (α t * energyComparison α b c t + b) t := by
  have hd (s : ℝ) : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, α r) (α s) s :=
    intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable _ _)
      hα.aestronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt
  have hc : Continuous (fun s => Real.exp (-(∫ r in (0 : ℝ)..s, α r))) :=
    Real.continuous_exp.comp
      ((continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).neg)
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : Real.exp (∫ r in (0 : ℝ)..t, α r) *
      Real.exp (-(∫ r in (0 : ℝ)..t, α r)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  convert (hd t).exp.mul ((hi.const_mul b).const_add c) using 1 <;>
    first | rfl | (dsimp [energyComparison]; linear_combination -b * he)

theorem energyComparison_zero (α : ℝ → ℝ) (b c : ℝ) :
    energyComparison α b c 0 = c := by simp [energyComparison]

/-- The explicit comparison is the unique global solution of `y' = α y + b`
with the prescribed value at zero. -/
theorem energyComparison_unique {α : ℝ → ℝ} (hα : Continuous α) {b c : ℝ}
    {y : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (α t * y t + b) t) (hy0 : y 0 = c) :
    y = energyComparison α b c := by
  let A := fun t : ℝ => ∫ s in (0 : ℝ)..t, α s
  let z := fun t => Real.exp (-A t) * (y t - energyComparison α b c t)
  have hA (t : ℝ) : HasDerivAt A (α t) t :=
    intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable _ _)
      hα.aestronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt
  have hz (t : ℝ) : HasDerivAt z 0 t := by
    convert (hA t).neg.exp.mul
      ((hy t).sub (energyComparison_hasDerivAt hα b c t)) using 1
    all_goals first | rfl | (simp only [Pi.neg_apply, Pi.sub_apply]; ring)
  funext t
  have hconst : z t = z 0 := is_const_of_deriv_eq_zero
    (fun s => (hz s).differentiableAt) (fun s => (hz s).deriv) t 0
  have hz0 : z 0 = 0 := by simp [z, A, hy0, energyComparison_zero]
  rw [hz0] at hconst
  exact sub_eq_zero.mp (mul_eq_zero.mp hconst |>.resolve_left (Real.exp_ne_zero _))

theorem energyComparison_nonneg (α : ℝ → ℝ) {b c t : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ t) : 0 ≤ energyComparison α b c t := by
  apply mul_nonneg (Real.exp_pos _).le
  exact add_nonneg hc (mul_nonneg hb (intervalIntegral.integral_nonneg_of_forall ht
    (fun _ => (Real.exp_pos _).le)))

/-- Exact completion of the square; the envelope gradient is an algebraic witness. -/
theorem energyComparison_balance {ν : ℝ} (hν : 0 < ν) (k b y : ℝ) :
    (1/2 : ℝ) * (2*y*(k^2/(4*ν)*y+b)) + ν*(k*y/(2*ν))^2 =
      k*y*(k*y/(2*ν)) + b*y := by
  field_simp
  ring

/-- Squaring a nonnegative scalar ODE solution supplies the exact dissipative envelope. -/
theorem squared_comparison_envelope {T ν b c : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℝ → ℝ) (y : C(Icc (0 : ℝ) T, ℝ))
    (hy : ∀ t, 0 ≤ y t) (hy0 : y ⟨0, le_rfl, hT⟩ ≤ c)
    (hyd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT y)
      (k t^2/(4*ν)*extendPath T hT y t+b) t) :
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧ (∀ t, Real.sqrt (x t) = y t) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤ c ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T, (1/2)*d t + ν*(g t)^2 =
        k t*Real.sqrt (extendPath T hT x t)*g t + b*Real.sqrt (extendPath T hT x t) := by
  let x : C(Icc (0 : ℝ) T, ℝ) := ⟨fun t => (y t)^2, y.continuous.pow 2⟩
  let v := extendPath T hT y
  refine ⟨x, fun t => 2*v t*(k t^2/(4*ν)*v t+b), fun t => k t*v t/(2*ν),
    fun t => sq_nonneg _, fun t => Real.sqrt_sq (hy t), ?_, ?_, ?_⟩
  · exact (Real.sqrt_sq (hy _)).le.trans hy0
  · intro t ht
    convert (hyd t ht).pow 2 using 1 <;> first | rfl | (norm_num; ring)
  · intro t _
    change (1/2 : ℝ)*(2*v t*(k t^2/(4*ν)*v t+b)) + ν*(k t*v t/(2*ν))^2 = _
    have hs : Real.sqrt (extendPath T hT x t) = v t := Real.sqrt_sq (hy _)
    rw [hs]
    exact energyComparison_balance hν _ _ _

/-- No regularity of the dominated root is needed to construct the envelope. -/
theorem comparison_envelope {T ν b c : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℝ → ℝ) (hk : Continuous k) :
    ∃ (x : C(Icc (0 : ℝ) T, ℝ)) (d g : ℝ → ℝ),
      (∀ t, 0 ≤ x t) ∧
      (∀ t, Real.sqrt (x t) = energyComparison (fun s => k s^2/(4*ν)) b c t) ∧
      Real.sqrt (x ⟨0, le_rfl, hT⟩) ≤ c ∧
      (∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT x) (d t) t) ∧
      ∀ t ∈ Ioo 0 T, (1/2)*d t + ν*(g t)^2 =
        k t*Real.sqrt (extendPath T hT x t)*g t + b*Real.sqrt (extendPath T hT x t) := by
  let α := fun s => k s^2/(4*ν)
  have hα : Continuous α := (hk.pow 2).div_const _
  let y : C(Icc (0 : ℝ) T, ℝ) := ⟨fun t => energyComparison α b c t,
    (continuous_iff_continuousAt.mpr
      (fun t => (energyComparison_hasDerivAt hα b c t).continuousAt)).comp continuous_subtype_val⟩
  apply squared_comparison_envelope hT hν k y
    (fun t => energyComparison_nonneg α hb hc t.property.1)
    (by simp [y, energyComparison_zero])
  intro t ht
  have heq : extendPath T hT y =ᶠ[nhds t] energyComparison α b c := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simp only [extendPath, y, ContinuousMap.coe_mk, projIcc_of_mem hT
      (show s ∈ Icc 0 T from ⟨hs.1.le, hs.2.le⟩)]
  have hd := (energyComparison_hasDerivAt hα b c t).congr_of_eventuallyEq heq
  convert hd using 1 <;> first | rfl | rw [heq.eq_of_nhds]

/-- The continuous coefficient in the comparison ODE, before squaring and dividing by 4ν. -/
def cylinderEnvelopeDriver {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (A : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) (t : ℝ) : ℝ :=
  A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u t)‖)

theorem cylinderEnvelopeDriver_continuous {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (hT : 0 ≤ T)
    (A : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))) :
    Continuous (cylinderEnvelopeDriver hq hT A u) :=
  continuous_const.mul (continuous_const.mul
    (((restrictOperator 1 (Nat.succ_le_succ hq)).continuous.comp
      (extendPath_continuous T hT u)).norm))

/-- Exact remaining signed-limit/comparison obligation. This is NOT proved here.
It asks only for domination by a fixed explicit scalar function, with constants
chosen before the window and the competitor. -/
def CylinderRootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ t, energyRootPath u t ≤
      energyComparison (fun s => (cylinderEnvelopeDriver hq hT A u s)^2/(4*ν))
        (E * ‖sobolevPath F hF (q+1)‖)
        (E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖) t

/-- The explicit scalar comparison is sufficient; no Bochner derivative is assumed. -/
theorem finiteMildEnergy_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A := by
  intro T hT hTS u hu
  obtain ⟨x, d, g, hx, hxy, hx0, hd, hg⟩ := comparison_envelope hT hν
    (mul_nonneg hE (norm_nonneg (sobolevPath F hF (q+1))))
    (mul_nonneg hE (norm_nonneg (ordinarySobolev (q+1) a.toLp a.translation_contDiff)))
    (cylinderEnvelopeDriver hq hT A u) (cylinderEnvelopeDriver_continuous hq hT A u)
  refine ⟨x, d, g, hx, ?_, hx0, hd, fun t ht => (hg t ht).le⟩
  intro t
  rw [hxy]
  exact (euclideanWordNorm_bounds (u t)).1.trans
    (by simpa only [energyRootPath_apply] using hcomparison T hT hTS u hu t)

/-- Conditional conversion with lane 198's conclusion unchanged. The integrated
estimate and forcing bound can be bypassed once the stronger comparison is supplied. -/
theorem envelopeConversion_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    EnvelopeConversion hq hν a F hF E A := by
  intro T hT hTS u hu _U _hU _hest _hforcing
  exact finiteMildEnergy_of_rootComparison hq hν a ha F hF hE hcomparison T hT hTS u hu

/-- Lane 196's Grönwall conclusion, still conditional on the signed comparison. -/
theorem mildGronwall_of_rootComparison {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ} (hE : 0 ≤ E)
    (hcomparison : CylinderRootComparison hq hν a F hF E A) :
    MildGronwall hq hν a ha F hF E (A^2/(4*ν)) :=
  mildGronwall hq hν a ha F hF hE
    (finiteMildEnergy_of_rootComparison hq hν a ha F hF hE hcomparison)

/-- Base-family assembly with the same one comparison obligation at each order. -/
theorem hb_of_base_of_rootComparison {ν S R₆ : ℝ} (hν : 0 < ν) (hS : 0 ≤ S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath F hF 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E A : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (hcomparison : ∀ q (hq : 6 ≤ q), CylinderRootComparison hq hν a F hF (E q) (A q)) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF
      (aprioriRadius a F hF R₆ E (fun q => A q^2/(4*ν)) q) :=
  hb_of_base' hν hS a ha F hF u₆ hR h₆ E A hE
    (fun q hq => finiteMildEnergy_of_rootComparison hq hν a ha F hF (hE q) (hcomparison q hq))

end NSFormalization.Section4.A01
