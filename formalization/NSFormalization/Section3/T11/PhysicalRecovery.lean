import NSFormalization.Section3.T11.ConvolutionBound
import NSFormalization.Section3.T11.CriterionBridge

/-! # Physical Fourier recovery on the canonical coefficient carrier

The order in every inverse weight is explicit: `PeriodicSobolev` has a phantom
index. This module never uses a measurable L² representative as a pointwise
physical field.

Partial U9d delivery: no general classical recovery theorem is asserted. The
all-order mild bootstrap, pressure reconstruction and general PDE identities
remain open. Every result here is unconditional; no named analytic input is
introduced. The affine constant family additionally has full classical recovery.
-/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped BigOperators ContDiff ComplexConjugate ENNReal NNReal

local instance recoveryNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance recoveryNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- The unweighted coefficient; the order is part of the formula. -/
def torusPhysicalCoeff (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (periodicFrequencyWeight k ^ (-s / 2) : ℝ) * A.1 i k

/-- Removing the datum weight recovers the physical Fourier coefficient. -/
theorem torusPhysicalCoeff_eq {s : ℝ} {a : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s a A)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff s A i k = periodicFourierCoeff (fun x ↦ (a x i : ℂ)) k := by
  have hw : 0 < periodicFrequencyWeight k := by unfold periodicFrequencyWeight; positivity
  rw [torusPhysicalCoeff, hA.2.2]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  rw [← Real.rpow_add hw, show -s / 2 + s / 2 = 0 by ring]
  simp

/-- H³ unweighted coefficients are absolutely summable, on arbitrary data. -/
theorem torusPhysicalCoeff_summable (A : PeriodicSobolev 3) (i : Fin 3) :
    Summable (fun k ↦ ‖torusPhysicalCoeff 3 A i k‖) := by
  have hw (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
    unfold periodicFrequencyWeight; positivity
  have hs : Summable (fun k : PeriodicFrequency ↦
      (periodicFrequencyWeight k ^ (-(3 : ℝ) / 2)) ^ 2) := by
    have he (k : PeriodicFrequency) :
        (periodicFrequencyWeight k ^ (-(3 : ℝ) / 2)) ^ 2 =
          (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hw k).le]
      norm_num [Real.rpow_neg (hw k).le]
    simp_rw [he, torus_weight_eq]
    exact NSFormalization.Paper1.PeriodicInverseWeightSummable.summable_inverse_weight_cube
  let w : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun k ↦ periodicFrequencyWeight k ^ (-(3 : ℝ) / 2),
      memℓp_gen (by simpa [Real.norm_eq_abs] using hs)⟩
  let b : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun k ↦ ‖A.1 i k‖, memℓp_gen (by
      simpa using (lp.memℓp (A.1 i)).summable (by norm_num))⟩
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two) w b
  simpa [torusPhysicalCoeff, w, b, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    using hh.1

/-- Reality is retained when removing an even real Sobolev weight. -/
theorem torusPhysicalCoeff_neg (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff s A i (-k) = conj (torusPhysicalCoeff s A i k) := by
  have he : periodicFrequencyWeight (-k) = periodicFrequencyWeight k := by
    simp [periodicFrequencyWeight]
  simp [torusPhysicalCoeff, he, A.2 i k]

/-- Actual Fourier series, before taking real components. -/
def torusPhysicalComponent (A : PeriodicSobolev 3) (i : Fin 3) (x : Space) : ℂ :=
  ∑' k, torusPhysicalCoeff 3 A i k * NSFormalization.Paper1.periodicCharacter k x

/-- Canonical physical velocity slice, defined at every point. -/
def torusPhysicalField (A : PeriodicSobolev 3) : SpatialField :=
  fun x ↦ WithLp.toLp 2 (fun i ↦ (torusPhysicalComponent A i x).re)

/-- The same reconstruction applied slice by slice to a coefficient path. -/
def torusPhysicalVelocity (u : ℝ → PeriodicSobolev 3) : SpaceTimeField :=
  fun z ↦ torusPhysicalField (u z.1) z.2

/-- Every Fourier character has modulus one. -/
theorem torusCharacter_norm (k : PeriodicFrequency) (x : Space) :
    ‖NSFormalization.Paper1.periodicCharacter k x‖ = 1 := by
  rw [NSFormalization.Paper1.periodicCharacter_eq_mFourier]
  change ‖∏ i, fourier (k i) (x i : UnitAddCircle)‖ = 1
  simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

/-- Absolute convergence holds at every physical point. -/
theorem torusPhysicalComponent_summable (A : PeriodicSobolev 3) (i : Fin 3) (x : Space) :
    Summable (fun k ↦ torusPhysicalCoeff 3 A i k *
      NSFormalization.Paper1.periodicCharacter k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, torusCharacter_norm, mul_one] using torusPhysicalCoeff_summable A i

/-- Fourier inversion is continuous in space already at order three. -/
theorem torusPhysicalComponent_continuous (A : PeriodicSobolev 3) (i : Fin 3) :
    Continuous (torusPhysicalComponent A i) := by
  apply continuous_tsum (u := fun k ↦ ‖torusPhysicalCoeff 3 A i k‖)
    (fun k ↦ continuous_const.mul (NSFormalization.Paper1.periodicCharacter_smooth k).continuous)
    (torusPhysicalCoeff_summable A i)
  intro k x
  dsimp only [Pi.mul_apply]
  simp only [norm_mul, torusCharacter_norm, mul_one, le_refl]

/-- Reconstruction has unit spatial periods. -/
theorem torusPhysicalField_periodic (A : PeriodicSobolev 3) :
    IsPeriodicSpatial (torusPhysicalField A) := by
  intro x j
  apply WithLp.ofLp_injective 2
  funext i
  change (∑' k, _ * NSFormalization.Paper1.periodicCharacter k (x + coordinateVector j)).re =
    (∑' k, _ * NSFormalization.Paper1.periodicCharacter k x).re
  congr 1
  apply tsum_congr
  intro k
  rw [NSFormalization.Paper1.periodicCharacter_periodic k x j]

/-- The reconstructed real vector field is continuous. -/
theorem torusPhysicalField_continuous (A : PeriodicSobolev 3) :
    Continuous (torusPhysicalField A) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i ↦ Complex.continuous_re.comp (torusPhysicalComponent_continuous A i))

/-- Inversion recovers every continuous physical field having this H³ datum. -/
theorem torusPhysicalField_eq {a : SpatialField} {A : PeriodicSobolev 3}
    (ha : Continuous a) (hA : IsPeriodicDatum 3 a A) : torusPhysicalField A = a := by
  funext x
  apply WithLp.ofLp_injective 2
  funext i
  have hs (j : Fin 3) : Summable (periodicFourierCoeff (fun y ↦ (a y j : ℂ))) := by
    have he : torusPhysicalCoeff 3 A j = periodicFourierCoeff (fun y ↦ (a y j : ℂ)) :=
      funext (torusPhysicalCoeff_eq hA j)
    rw [← he]
    exact (torusPhysicalCoeff_summable A j).of_norm
  have hi := periodic_component_eq_tsum hA.1 ha hs i x
  change (∑' k, torusPhysicalCoeff 3 A i k *
    NSFormalization.Paper1.periodicCharacter k x).re = a x i
  simpa only [torusPhysicalCoeff_eq hA, NSFormalization.Paper1.periodicCharacter,
    NSFormalization.Paper1.periodicPhase_apply, Complex.ofReal_re] using
      (congrArg Complex.re hi).symm

/-- Initial recovery uses the mild initial identity and datum inversion. -/
theorem torusPhysicalVelocity_initial {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {a : SpatialField} {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hu : TorusForcedMildOn C A P T u) (x : Space) :
    torusPhysicalVelocity u (0, x) = a x := by
  change torusPhysicalField (u 0) x = a x
  rw [hu.initial, torusPhysicalField_eq ha.1.continuous hA]

/-- Periodicity requires no time regularity or equation. -/
theorem torusPhysicalVelocity_periodic (u : ℝ → PeriodicSobolev 3) :
    IsPeriodicOn univ (torusPhysicalVelocity u) :=
  fun t _ x j ↦ torusPhysicalField_periodic (u t) x j

/-- Conjugate reflection makes the Fourier sum real, without taking an a.e. representative. -/
theorem torusPhysicalComponent_conj (A : PeriodicSobolev 3) (i : Fin 3) (x : Space) :
    conj (torusPhysicalComponent A i x) = torusPhysicalComponent A i x := by
  unfold torusPhysicalComponent
  rw [Complex.conj_tsum]
  have he (k : PeriodicFrequency) :
      conj (torusPhysicalCoeff 3 A i k * NSFormalization.Paper1.periodicCharacter k x) =
        torusPhysicalCoeff 3 A i (-k) * NSFormalization.Paper1.periodicCharacter (-k) x := by
    rw [map_mul, torusPhysicalCoeff_neg]
    simp only [NSFormalization.Paper1.periodicCharacter_eq_mFourier, UnitAddTorus.mFourier_neg]
  simp_rw [he]
  exact (Equiv.neg PeriodicFrequency).tsum_eq (fun k ↦
    torusPhysicalCoeff 3 A i k * NSFormalization.Paper1.periodicCharacter k x)

/-- Complexification of a recovered real component is the original Fourier series. -/
theorem torusPhysicalField_component (A : PeriodicSobolev 3) (i : Fin 3) (x : Space) :
    (torusPhysicalField A x i : ℂ) = torusPhysicalComponent A i x := by
  exact Complex.conj_eq_iff_re.mp (torusPhysicalComponent_conj A i x)

/-- Quotient-torus expression of the reconstructed component. -/
theorem torusPhysicalComponent_lift (A : PeriodicSobolev 3) (i : Fin 3)
    (q : PeriodicTorus) :
    torusLift (torusPhysicalComponent A i) q =
      ∑' k, torusPhysicalCoeff 3 A i k * UnitAddTorus.mFourier k q := by
  have hz := (UnitAddTorus.measurableEquivPiIoc
    (0 : NavierStokes.PeriodicIntegration.Coords)).symm_apply_apply q
  change (fun j ↦ (((UnitAddTorus.measurableEquivPiIoc
    (0 : NavierStokes.PeriodicIntegration.Coords) q).val j : ℝ) : UnitAddCircle)) = q at hz
  simp only [torusLift, NSFormalization.Paper1.torusLift, torusPhysicalComponent,
    NSFormalization.Paper1.periodicCharacter_eq_mFourier,
    NavierStokes.PeriodicIntegration.toSpace_apply, hz]

/-- Pointwise modulus of the quotient Fourier characters. -/
theorem torusMFourier_norm (k : PeriodicFrequency) (q : PeriodicTorus) :
    ‖UnitAddTorus.mFourier k q‖ = 1 := by
  change ‖∏ i, fourier (k i) (q i)‖ = 1
  simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

/-- Computing a Fourier coefficient of the inverse series recovers its input. -/
theorem torusPhysicalComponent_coeff (A : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (torusPhysicalComponent A i) k = torusPhysicalCoeff 3 A i k := by
  let f : PeriodicFrequency → PeriodicTorus → ℂ := fun l q ↦
    torusPhysicalCoeff 3 A i l * UnitAddTorus.mFourier (l-k) q
  have hf (l : PeriodicFrequency) : Integrable (f l) periodicTorusMeasure := by
    have hc : Continuous (f l) :=
      continuous_const.mul (UnitAddTorus.mFourier (l-k)).continuous
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
      (μ := periodicTorusMeasure) isCompact_univ
  have hnorm (l : PeriodicFrequency) (q : PeriodicTorus) :
      ‖f l q‖ = ‖torusPhysicalCoeff 3 A i l‖ := by
    simp only [f, norm_mul, torusMFourier_norm, mul_one]
  have hs : Summable (fun l ↦ ∫ q, ‖f l q‖ ∂periodicTorusMeasure) := by
    simpa only [hnorm, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
      torusPhysicalCoeff_summable A i
  change (∫ q, UnitAddTorus.mFourier (-k) q •
    torusLift (torusPhysicalComponent A i) q ∂periodicTorusMeasure) = _
  simp_rw [torusPhysicalComponent_lift, smul_eq_mul, ← tsum_mul_left]
  have he (q : PeriodicTorus) (l : PeriodicFrequency) :
      UnitAddTorus.mFourier (-k) q *
        (torusPhysicalCoeff 3 A i l * UnitAddTorus.mFourier l q) = f l q := by
    simp only [f, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm hf hs]
  simp only [f, integral_const_mul, integral_mFourier, sub_eq_zero,
    mul_ite, mul_one, mul_zero]
  exact tsum_ite_eq k _

/-- The recovered slice has exactly the original weighted datum. -/
theorem torusPhysicalField_datum (A : PeriodicSobolev 3) :
    IsPeriodicDatum 3 (torusPhysicalField A) A := by
  refine ⟨torusPhysicalField_periodic A, ?_, ?_⟩
  · apply Integrable.of_eval_piLp
    intro i
    have hc : Continuous (torusLift (torusPhysicalComponent A i)) := by
      apply NSFormalization.Paper1.continuous_torusLift (torusPhysicalComponent_continuous A i)
      intro x j
      unfold torusPhysicalComponent
      apply tsum_congr
      intro k
      rw [NSFormalization.Paper1.periodicCharacter_periodic k x j]
    have hi : Integrable (torusLift (torusPhysicalComponent A i)) periodicTorusMeasure := by
      simpa using hc.continuousOn.integrableOn_compact
        (μ := periodicTorusMeasure) isCompact_univ
    exact hi.re
  · intro i k
    simp_rw [torusPhysicalField_component]
    rw [torusPhysicalComponent_coeff, torusPhysicalCoeff]
    have hw : 0 < periodicFrequencyWeight k := by unfold periodicFrequencyWeight; positivity
    simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    rw [← Real.rpow_add hw, show (3 : ℝ) / 2 + -3 / 2 = 0 by ring]
    simp

/-- The representation part of U9d holds on every time set, without bootstrap. -/
theorem torusPhysicalVelocity_datum (u : ℝ → PeriodicSobolev 3) (I : Set ℝ) :
    IsPeriodicSobolevPathOn 3 I (torusPhysicalVelocity u) u :=
  fun t _ ↦ torusPhysicalField_datum (u t)

/-- The inverse H³ weight as a genuine square-summable sequence. -/
def torusRecoveryWeight : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 := by
  refine ⟨fun k ↦ periodicFrequencyWeight k ^ (-(3 : ℝ) / 2), memℓp_gen ?_⟩
  have hw (k : PeriodicFrequency) : 0 < periodicFrequencyWeight k := by
    unfold periodicFrequencyWeight; positivity
  have he (k : PeriodicFrequency) :
      ‖periodicFrequencyWeight k ^ (-(3 : ℝ) / 2)‖ ^ 2 =
        (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹ := by
    rw [Real.norm_eq_abs, sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (hw k).le]
    norm_num [Real.rpow_neg (hw k).le]
  change Summable (fun k ↦ ‖periodicFrequencyWeight k ^ (-(3 : ℝ) / 2)‖ ^ 2)
  have hs : Summable (fun k : PeriodicFrequency ↦ (periodicFrequencyWeight k ^ (3 : ℕ))⁻¹) := by
    simpa only [torus_weight_eq] using
      NSFormalization.Paper1.PeriodicInverseWeightSummable.summable_inverse_weight_cube
  exact hs.congr (fun k ↦ by simpa only [Real.rpow_two] using (he k).symm)

/-- A uniform bound for the entire inverse series, not just individual modes. -/
theorem torusPhysicalCoeff_norm_sum_le (A : PeriodicSobolev 3) (i : Fin 3) :
    (∑' k, ‖torusPhysicalCoeff 3 A i k‖) ≤ ‖torusRecoveryWeight‖ * ‖A‖ := by
  let b : lp (fun _ : PeriodicFrequency ↦ ℝ) 2 :=
    ⟨fun k ↦ ‖A.1 i k‖, memℓp_gen (by
      simpa using (lp.memℓp (A.1 i)).summable (by norm_num))⟩
  have hh := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal by
      simpa using Real.HolderConjugate.two_two) torusRecoveryWeight b
  have hb : ‖b‖ = ‖A.1 i‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp [b]
  have h := hh.2
  simp only [hb] at h
  have h' : (∑' k, ‖torusPhysicalCoeff 3 A i k‖) ≤ ‖torusRecoveryWeight‖ * ‖A.1 i‖ := by
    simpa [torusPhysicalCoeff, torusRecoveryWeight, b, norm_mul,
      Complex.norm_real, Real.norm_eq_abs] using h
  exact h'.trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le A.1 i) (norm_nonneg _))

/-- Absolute convergence in the uniform norm on the compact torus. -/
theorem torusPhysicalTorus_summable (A : PeriodicSobolev 3) (i : Fin 3) :
    Summable (fun k ↦ torusPhysicalCoeff 3 A i k • UnitAddTorus.mFourier k) := by
  apply Summable.of_norm
  simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
    torusPhysicalCoeff_summable A i

/-- A bounded real-linear Fourier inverse into continuous complex torus components. -/
def torusPhysicalComponentCLM (i : Fin 3) :
    PeriodicSobolev 3 →L[ℝ] C(PeriodicTorus, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun A ↦ ∑' k, torusPhysicalCoeff 3 A i k • UnitAddTorus.mFourier k
      map_add' := by
        intro A B
        have he (k : PeriodicFrequency) : torusPhysicalCoeff 3 (A+B) i k =
            torusPhysicalCoeff 3 A i k + torusPhysicalCoeff 3 B i k := by
          change (_ : ℂ) * (A.1 i k + B.1 i k) = _
          exact mul_add _ _ _
        change (∑' k, torusPhysicalCoeff 3 (A+B) i k • UnitAddTorus.mFourier k) = _
        rw [← (torusPhysicalTorus_summable A i).tsum_add (torusPhysicalTorus_summable B i)]
        apply tsum_congr
        intro k
        rw [he]
        ext q
        change (torusPhysicalCoeff 3 A i k + torusPhysicalCoeff 3 B i k) *
          UnitAddTorus.mFourier k q = torusPhysicalCoeff 3 A i k * UnitAddTorus.mFourier k q +
            torusPhysicalCoeff 3 B i k * UnitAddTorus.mFourier k q
        ring
      map_smul' := by
        intro r A
        have he (k : PeriodicFrequency) : torusPhysicalCoeff 3 (r • A) i k =
            r • torusPhysicalCoeff 3 A i k := by
          change (_ : ℂ) * ((r : ℂ) * A.1 i k) = (r : ℂ) * (_ * A.1 i k)
          ring
        change (∑' k, torusPhysicalCoeff 3 (r • A) i k • UnitAddTorus.mFourier k) = _
        simp only [he, smul_assoc, RingHom.id_apply]
        exact (torusPhysicalTorus_summable A i).tsum_const_smul r }
    ‖torusRecoveryWeight‖ (fun A ↦ by
      have hn : Summable (fun k ↦ ‖torusPhysicalCoeff 3 A i k • UnitAddTorus.mFourier k‖) := by
        simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
          torusPhysicalCoeff_summable A i
      refine (norm_tsum_le_tsum_norm hn).trans ?_
      simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using
        torusPhysicalCoeff_norm_sum_le A i)

/-- Evaluation of the bounded inverse is the pointwise physical series. -/
theorem torusPhysicalComponentCLM_apply (A : PeriodicSobolev 3) (i : Fin 3) (x : Space) :
    torusPhysicalComponentCLM i A (fun j ↦ (x j : UnitAddCircle)) =
      torusPhysicalComponent A i x := by
  change (∑' k, torusPhysicalCoeff 3 A i k • UnitAddTorus.mFourier k)
    (fun j ↦ (x j : UnitAddCircle)) = _
  rw [← ContinuousMap.tsum_apply (torusPhysicalTorus_summable A i)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul,
    torusPhysicalComponent, NSFormalization.Paper1.periodicCharacter_eq_mFourier]

/-- Joint continuity in the coefficient datum and the physical point. -/
theorem torusPhysicalField_joint_continuous :
    Continuous (fun z : PeriodicSobolev 3 × Space ↦ torusPhysicalField z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hq : Continuous (fun z : PeriodicSobolev 3 × Space ↦
      fun j ↦ (z.2 j : UnitAddCircle)) := by
    apply continuous_pi
    intro j
    exact continuous_quotient_mk'.comp ((PiLp.continuous_apply 2 _ j).comp continuous_snd)
  have he := ((torusPhysicalComponentCLM i).continuous.comp continuous_fst).eval hq
  have he' := Complex.continuous_re.comp he
  simpa only [Function.comp_def, torusPhysicalComponentCLM_apply] using he'

/-- A continuous coefficient path has a jointly continuous physical inverse. -/
theorem torusPhysicalVelocity_continuousOn {u : ℝ → PeriodicSobolev 3} {I : Set ℝ}
    (hu : ContinuousOn u I) :
    ContinuousOn (torusPhysicalVelocity u) (I ×ˢ (univ : Set Space)) := by
  have hf : ContinuousOn (fun z : SpaceTime ↦ u z.1) (I ×ˢ (univ : Set Space)) :=
    hu.comp (f := fun z : SpaceTime ↦ z.1) continuous_fst.continuousOn
      (fun z hz ↦ hz.1)
  have hc : ContinuousOn (fun z : SpaceTime ↦ (u z.1, z.2)) (I ×ˢ (univ : Set Space)) :=
    hf.prodMk (continuous_snd.continuousOn : ContinuousOn (fun z : SpaceTime ↦ z.2) _)
  exact torusPhysicalField_joint_continuous.comp_continuousOn
    (f := fun z : SpaceTime ↦ (u z.1, z.2)) hc

/-- The forced mild solution's velocity is jointly continuous on its closed horizon. -/
theorem torusForcedMildOn_physical_continuous {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u) :
    ContinuousOn (torusPhysicalVelocity u) (Icc (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  torusPhysicalVelocity_continuousOn hu.continuous_path

/-- Transport a datum through the exact order-changing weight. -/
theorem recovery_datum_reweight {s r : ℝ} {a : SpatialField}
    {A : PeriodicSobolev s} {B : PeriodicSobolev r}
    (hA : IsPeriodicDatum s a A) (hB : IsPeriodicReweight s r A B) :
    IsPeriodicDatum r a B := by
  refine ⟨hA.1, hA.2.1, fun i k ↦ ?_⟩
  rw [hB i k, hA.2.2 i k, smul_smul]
  have hw : 0 < periodicFrequencyWeight k := by unfold periodicFrequencyWeight; positivity
  rw [← Real.rpow_add hw, show (r-s)/2+s/2 = r/2 by ring]

/-- Higher-order data for the inverse need actual reweighting, not a phantom cast. -/
theorem torusPhysicalField_datum_reweight {s : ℝ} {A : PeriodicSobolev 3}
    {B : PeriodicSobolev s} (hB : IsPeriodicReweight 3 s A B) :
    IsPeriodicDatum s (torusPhysicalField A) B :=
  recovery_datum_reweight (torusPhysicalField_datum A) hB

/-- A common-horizon reweighted family supplies precisely the datum-path clause. -/
theorem torusPhysicalVelocity_reweight {s : ℝ} {I : Set ℝ}
    {u : ℝ → PeriodicSobolev 3} {U : ℝ → PeriodicSobolev s}
    (hU : ∀ t ∈ I, IsPeriodicReweight 3 s (u t) (U t)) :
    IsPeriodicSobolevPathOn s I (torusPhysicalVelocity u) U :=
  fun t ht ↦ torusPhysicalField_datum_reweight (hU t ht)

/-- Time smoothness of every physical component follows from H³ path smoothness. -/
theorem torusPhysicalVelocity_component_contDiffOn {I : Set ℝ}
    {u : ℝ → PeriodicSobolev 3} (hu : ContDiffOn ℝ ∞ u I)
    (x : Space) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t ↦ torusPhysicalVelocity u (t, x) i) I := by
  let L : PeriodicSobolev 3 →L[ℝ] ℝ := Complex.reCLM.comp
    ((ContinuousMap.evalCLM ℝ (fun j ↦ (x j : UnitAddCircle))).comp
      (torusPhysicalComponentCLM i))
  have he : (fun t ↦ torusPhysicalVelocity u (t, x) i) = fun t ↦ L (u t) := by
    funext t
    exact congrArg Complex.re (torusPhysicalComponentCLM_apply (u t) i x).symm
  rw [he]
  exact L.contDiff.comp_contDiffOn hu

/-- Nonzero constants are recovered pointwise, at every physical point. -/
theorem torusPhysicalField_constant (c : Space) :
    torusPhysicalField (torusConstantDatum 3 c) = fun _ ↦ c :=
  torusPhysicalField_eq continuous_const (torusConstantDatum_isDatum 3 c)

/-- A genuinely forced coefficient solution tests recovery on its own horizon. -/
theorem torusPhysicalRecovery_nonzero :
    ∃ (C : TorusTwoSpaceContract 1) (T : ℝ) (u : ℝ → PeriodicSobolev 3),
      0 < T ∧ TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
        (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) T u ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) (torusPhysicalVelocity u) u ∧
      torusPhysicalVelocity u (0, 0) ≠ 0 ∧
      torusPhysicalField (torusConstantDatum 3 (coordinateVector 0)) 0 ≠ 0 := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' 1 (by norm_num)
  let A := torusConstantDatum 3 (coordinateVector 0)
  obtain ⟨hT, _, u, hu, _, _⟩ := torusForcedPicard_quantitative (by norm_num) C
    A (fun _ ↦ A) ‖A‖ (norm_nonneg _) continuousOn_const (fun _ _ ↦ le_rfl)
  refine ⟨C, _, u, hT, hu, torusPhysicalVelocity_datum u _, ?_, ?_⟩
  · change torusPhysicalField (u 0) 0 ≠ 0
    rw [hu.initial, torusPhysicalField_constant]
    intro h
    have hh := congrArg (fun v : Space ↦ v 0) h
    norm_num [coordinateVector] at hh
  · rw [torusPhysicalField_constant]
    intro h
    have hh := congrArg (fun v : Space ↦ v 0) h
    norm_num [coordinateVector] at hh

example : ∃ (C : TorusTwoSpaceContract 1) (T : ℝ) (u : ℝ → PeriodicSobolev 3),
    0 < T ∧ TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
      (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) T u ∧
    IsPeriodicSobolevPathOn 3 (Ico 0 T) (torusPhysicalVelocity u) u ∧
    torusPhysicalVelocity u (0, 0) ≠ 0 ∧
    torusPhysicalField (torusConstantDatum 3 (coordinateVector 0)) 0 ≠ 0 :=
  torusPhysicalRecovery_nonzero

/-- Every exact contract preserves the constant spatial mode under heat evolution. -/
theorem torusContract_heat_constant {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (t : ℝ≥0) (c : Space) :
    C.analytic.linearEvolution t (torusConstantDatum 3 c) = torusConstantDatum 3 c := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  rw [C.linear_symbol]
  by_cases hk : k = 0
  · subst k
    simp [torusHeatSymbol, NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol,
      NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue,
      ← torus_weight_eq, periodicFrequencyWeight]
  · simp [torusConstantDatum, lp.single_apply, hk]

/-- Every exact contract has zero convection on any pair of constant modes. -/
theorem torusContract_bilinear_constant {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (c d : Space) :
    C.analytic.bilinear (torusConstantDatum 3 c) (torusConstantDatum 3 d) = 0 := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  rw [C.bilinear_symbol, torusProjectedConvectionSymbol_constants]
  rfl

/-- A nonzero constant force produces an affine coefficient trajectory on every horizon. -/
theorem torusForcedMildOn_affine_constant {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (c : Space) (hT : 0 ≤ T) :
    TorusForcedMildOn C (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) T
      (fun t ↦ (1+t) • torusConstantDatum 3 c) := by
  let A := torusConstantDatum 3 c
  have hQ (s : ℝ) : C.analytic.bilinear ((1+s) • A) ((1+s) • A) = 0 := by
    simp only [map_smul, smul_apply, torusContract_bilinear_constant,
      smul_zero, A]
  have hD (t s : ℝ) : C.analytic.duhamelIntegrand t (fun r ↦ (1+r) • A) s = 0 := by
    change MNS2.endpointSafePositiveOperator C.analytic.positiveSmoothing (t-s)
      (C.analytic.bilinear ((1+s) • A) ((1+s) • A)) = 0
    rw [hQ]
    exact map_zero _
  have hDf (t : ℝ) : C.analytic.duhamelIntegrand t (fun r ↦ (1+r) • A) =
      fun _ ↦ 0 := funext (hD t)
  refine ⟨hT, (continuous_const.add continuous_id |>.smul continuous_const).continuousOn,
    by simp, ?_, ?_, ?_⟩
  · intro t _
    simpa only [torusContract_heat_constant] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ A) volume 0 t)
  · intro t _
    change IntervalIntegrable (C.analytic.duhamelIntegrand t (fun r ↦ (1+r) • A)) volume 0 t
    rw [hDf]
    exact intervalIntegrable_const
  · intro t ht
    change 0 ≤ t ∧ t ≤ T at ht
    change (1+t) • A = torusForcedPicard C A (fun _ ↦ A)
      (fun r ↦ (1+r) • A) ⟨t, ht.1⟩
    unfold torusForcedPicard
    erw [torusContract_heat_constant]
    change (1+t) • A = A + (∫ s in (0 : ℝ)..t,
      C.analytic.linearEvolution (Real.toNNReal (t-s)) A) -
        ∫ s in (0 : ℝ)..t, C.analytic.duhamelIntegrand t (fun r ↦ (1+r) • A) s
    rw [hDf]
    have hheat (s : ℝ) : C.analytic.linearEvolution (Real.toNNReal (t-s)) A = A :=
      torusContract_heat_constant C _ c
    simp_rw [hheat]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_zero, sub_zero, sub_zero,
      add_smul, one_smul]

/-- Full recovery for this nonzero forced family, on the original arbitrary horizon. -/
theorem torusPhysicalRecovery_affine_constant (ν T : ℝ) (c : Space) (hT : 0 < T) :
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ ↦ c) T,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun _ ↦ c) T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity
        (fun t ↦ (1+t) • torusConstantDatum 3 c) := by
  have hb : ContDiff ℝ ∞ (fun t : ℝ ↦ 1+t) := contDiff_const.add contDiff_id
  have hb0 : (1 : ℝ)+0 = 1 := by norm_num
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ ↦ 1+r) 1 t := by
    exact (hasDerivAt_id t).const_add 1
  have h : ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun z : SpaceTime ↦ (1 : ℝ) • c) T,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun z : SpaceTime ↦ (1 : ℝ) • c) T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity
        (fun t ↦ (1+t) • torusConstantDatum 3 c) := by
    exact ⟨torusHomogeneousSolution ν T hT c (fun t ↦ 1+t) (fun _ ↦ 1) hb hb0 hd,
      torusHomogeneousSolution_regularity ν T hT c (fun t ↦ 1+t) (fun _ ↦ 1) hb hb0 hd,
      fun t _ ↦ torusConstantDatum_smul 3 (1+t) c⟩
  have hc : (1 : ℝ) • c = c := one_smul ℝ c
  rw [hc] at h
  exact h

end NSFormalization.Section3.T11
