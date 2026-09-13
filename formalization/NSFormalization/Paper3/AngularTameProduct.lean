import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Paper3.SobolevPhysicalProduct

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.FourierTameProduct
open scoped SchwartzMap ENNReal

/-- Actual cycles-to-angular weighted Fourier data equivalence. -/
def cyclesToAngular (s : ℝ) : SobolevHilbert s ≃L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (angularWeightEquiv s).trans angularFrequencyDilation.toContinuousLinearEquiv

theorem cyclesToAngular_norm_le (s : ℝ) (h : SobolevHilbert s) :
    ‖cyclesToAngular s h‖ ≤ frequencyUnit ^ |s| * ‖h‖ := by
  change ‖angularFrequencyDilation (angularWeightEquiv s h)‖ ≤ _
  rw [angularFrequencyDilation.norm_map]
  exact angularWeightEquiv_norm_le s h

theorem cyclesToAngular_symm_norm_le (s : ℝ) (h : Lp ℂ 2 (volume : Measure Space)) :
    ‖(cyclesToAngular s).symm h‖ ≤ frequencyUnit ^ |s| * ‖h‖ := by
  change ‖(angularWeightEquiv s).symm (angularFrequencyDilation.symm h)‖ ≤ _
  exact (angularWeightEquiv_symm_norm_le s _).trans_eq (by rw [angularFrequencyDilation.symm.norm_map])

@[simp] theorem angularRealization_cyclesToAngular (s : ℝ) (h : SobolevHilbert s) :
    angularRealization s (cyclesToAngular s h) = sobolevRealization s h := by
  change angularRealization s (angularFrequencyDilation (angularWeightEquiv s h)) = _
  rw [angularRealization_preserves_coordinate, angularCoordinateRealization_equiv]

theorem angularRealization_eq_cycles (s : ℝ) (h : Lp ℂ 2 (volume : Measure Space)) :
    angularRealization s h = sobolevRealization s ((cyclesToAngular s).symm h) := by
  have H := angularRealization_cyclesToAngular s ((cyclesToAngular s).symm h)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using H

@[simp] theorem cyclesToAngular_weightedFourierLp (s : ℝ) (φ : SchwartzMap Space ℂ) :
    cyclesToAngular s (weightedFourierLp s φ) = angularDatum s φ := rfl

/-- Genuine angular order lowering, preserving the physical field. -/
def angularOrderLowering (s r : ℝ) (hrs : r ≤ s) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  (cyclesToAngular r).toContinuousLinearMap.comp
    ((sobolevOrderLowering s r hrs).comp (cyclesToAngular s).symm.toContinuousLinearMap)

theorem cyclesToAngular_symm_orderLowering (s r : ℝ) (hrs : r ≤ s)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    (cyclesToAngular r).symm (angularOrderLowering s r hrs h) =
      sobolevOrderLowering s r hrs ((cyclesToAngular s).symm h) := by
  change (cyclesToAngular r).symm (cyclesToAngular r _) = _
  exact (cyclesToAngular r).symm_apply_apply _

theorem angularRealization_orderLowering (s r : ℝ) (hrs : r ≤ s)
    (h : Lp ℂ 2 (volume : Measure Space)) :
    angularRealization r (angularOrderLowering s r hrs h) = angularRealization s h := by
  change angularRealization r (cyclesToAngular r
    (sobolevOrderLowering s r hrs ((cyclesToAngular s).symm h))) = _
  rw [angularRealization_cyclesToAngular, sobolevRealization_orderLowering,
    angularRealization_eq_cycles]

/-- The actual completed angular product, obtained by continuous bilinear
composition of the existing complete cycles product. -/
def angularProduct (m : ℕ) (hm : 2 ≤ m) :
    Lp ℂ 2 (volume : Measure Space) →L[ℝ]
      Lp ℂ 2 (volume : Measure Space) →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  ((ContinuousLinearMap.compL ℝ (SobolevHilbert m) (SobolevHilbert m) (SobolevHilbert m))
    ((cyclesToAngular m).toContinuousLinearMap.restrictScalars ℝ)).comp
      ((sobolevProduct m hm).bilinearComp
        ((cyclesToAngular m).symm.toContinuousLinearMap.restrictScalars ℝ)
        ((cyclesToAngular m).symm.toContinuousLinearMap.restrictScalars ℝ))

@[simp] theorem angularProduct_apply (m : ℕ) (hm : 2 ≤ m)
    (h k : Lp ℂ 2 (volume : Measure Space)) :
    angularProduct m hm h k = cyclesToAngular m
      (sobolevProduct m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k)) := rfl

/-- Exact angular H2/Hm tame bound, with a support-independent constant. -/
theorem angularProduct_tame_bound (m : ℕ) (hm : 2 ≤ m)
    (h k : Lp ℂ 2 (volume : Measure Space)) :
    ‖angularProduct m hm h k‖ ≤ frequencyUnit ^ (2 * (m : ℝ) + 2) * sobolevTameConstant m *
      (‖angularOrderLowering m 2 (by exact_mod_cast hm) k‖ * ‖h‖ +
        ‖angularOrderLowering m 2 (by exact_mod_cast hm) h‖ * ‖k‖) := by
  let M := frequencyUnit ^ (m : ℝ)
  let C := frequencyUnit ^ (2 : ℝ)
  have hM : 0 ≤ M := Real.rpow_nonneg frequencyUnit_pos.le _
  have hC : 0 ≤ C := Real.rpow_nonneg frequencyUnit_pos.le _
  have hK := sobolevTameConstant_nonneg m
  have hhi (x : Lp ℂ 2 (volume : Measure Space)) :
      ‖(cyclesToAngular m).symm x‖ ≤ M * ‖x‖ := by
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)] using cyclesToAngular_symm_norm_le m x
  have hlo (x : Lp ℂ 2 (volume : Measure Space)) :
      ‖sobolevOrderLowering m 2 (by exact_mod_cast hm) ((cyclesToAngular m).symm x)‖ ≤
        C * ‖angularOrderLowering m 2 (by exact_mod_cast hm) x‖ := by
    have H := cyclesToAngular_symm_norm_le 2 (angularOrderLowering m 2 (by exact_mod_cast hm) x)
    rw [cyclesToAngular_symm_orderLowering] at H
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] using H
  have hcoef : M * (C * M) = frequencyUnit ^ (2 * (m : ℝ) + 2) := by
    unfold M C
    rw [← Real.rpow_add frequencyUnit_pos, ← Real.rpow_add frequencyUnit_pos]
    congr 1
    ring
  rw [angularProduct_apply]
  calc
    _ ≤ M * ‖sobolevProduct m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k)‖ := by
      simpa only [abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m)] using
        cyclesToAngular_norm_le m (sobolevProduct m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k))
    _ ≤ M * (sobolevTameConstant m *
        (‖sobolevOrderLowering m 2 (by exact_mod_cast hm) ((cyclesToAngular m).symm k)‖ *
          ‖(cyclesToAngular m).symm h‖ +
        ‖sobolevOrderLowering m 2 (by exact_mod_cast hm) ((cyclesToAngular m).symm h)‖ *
          ‖(cyclesToAngular m).symm k‖)) :=
      mul_le_mul_of_nonneg_left (sobolevProduct_tame_bound m hm _ _) hM
    _ ≤ M * (sobolevTameConstant m *
        ((C * ‖angularOrderLowering m 2 (by exact_mod_cast hm) k‖) * (M * ‖h‖) +
        (C * ‖angularOrderLowering m 2 (by exact_mod_cast hm) h‖) * (M * ‖k‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul (hlo k) (hhi h) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))
        (mul_le_mul (hlo h) (hhi k) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))) hK) hM
    _ = (M * (C * M)) * sobolevTameConstant m *
        (‖angularOrderLowering m 2 (by exact_mod_cast hm) k‖ * ‖h‖ +
        ‖angularOrderLowering m 2 (by exact_mod_cast hm) h‖ * ‖k‖) := by ring
    _ = _ := by rw [hcoef]

/-- The actual angular H2 datum of a Schwartz field is its lower-order datum. -/
theorem angularOrderLowering_datum (s r : ℝ) (hrs : r ≤ s) (φ : SchwartzMap Space ℂ) :
    angularOrderLowering s r hrs (angularDatum s φ) = angularDatum r φ := by
  change cyclesToAngular r (sobolevOrderLowering s r hrs
    ((cyclesToAngular s).symm (cyclesToAngular s (weightedFourierLp s φ)))) =
      cyclesToAngular r (weightedFourierLp r φ)
  rw [ContinuousLinearEquiv.symm_apply_apply, sobolevOrderLowering_weightedFourierLp]

/-- Compatibility with literal Schwartz multiplication in actual angular data. -/
theorem angularProduct_datum (m : ℕ) (hm : 2 ≤ m) (φ ψ : SchwartzMap Space ℂ) :
    angularProduct m hm (angularDatum m φ) (angularDatum m ψ) =
      angularDatum m (schwartzProduct φ ψ) := by
  change angularProduct m hm (cyclesToAngular m (weightedFourierLp m φ))
    (cyclesToAngular m (weightedFourierLp m ψ)) =
      cyclesToAngular m (weightedFourierLp m (schwartzProduct φ ψ))
  rw [angularProduct_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, sobolevProduct_weightedFourierLp]

/-- The same actual physical bounded representative in angular data. -/
def angularBoundedRepresentative (s : ℝ) (hs : 2 ≤ s) :
    Lp ℂ 2 (volume : Measure Space) →L[ℝ] BoundedContinuousFunction Space ℂ :=
  (sobolevBoundedRepresentative s hs).comp
    ((cyclesToAngular s).symm.toContinuousLinearMap.restrictScalars ℝ)

theorem angularRealization_boundedRepresentative (s : ℝ) (hs : 2 ≤ s)
    (h : Lp ℂ 2 (volume : Measure Space)) (θ : SchwartzMap Space ℂ) :
    angularRealization s h θ = ∫ x : Space, θ x * angularBoundedRepresentative s hs h x := by
  rw [angularRealization_eq_cycles, sobolevRealization_boundedRepresentative]
  rfl

/-- Multiplication of the actual bounded physical representatives. -/
theorem angularBoundedRepresentative_product (m : ℕ) (hm : 2 ≤ m)
    (h k : Lp ℂ 2 (volume : Measure Space)) :
    angularBoundedRepresentative m (by exact_mod_cast hm) (angularProduct m hm h k) =
      angularBoundedRepresentative m (by exact_mod_cast hm) h *
        angularBoundedRepresentative m (by exact_mod_cast hm) k := by
  rw [angularProduct_apply]
  change sobolevBoundedRepresentative m (by exact_mod_cast hm)
    ((cyclesToAngular m).symm (cyclesToAngular m
      (sobolevProduct m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact sobolevBoundedRepresentative_product m hm _ _

/-- The angular product test pairing is genuinely integrable. -/
theorem angularPhysicalProduct_integrable (m : ℕ) (hm : 2 ≤ m)
    (h k : Lp ℂ 2 (volume : Measure Space)) (θ : SchwartzMap Space ℂ) :
    Integrable (fun x : Space => θ x *
      (angularBoundedRepresentative m (by exact_mod_cast hm) h x *
        angularBoundedRepresentative m (by exact_mod_cast hm) k x)) volume :=
  sobolevPhysicalProduct_integrable m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k) θ

/-- The complete angular product realizes precisely the ordinary physical product. -/
theorem angularRealization_product (m : ℕ) (hm : 2 ≤ m)
    (h k : Lp ℂ 2 (volume : Measure Space)) (θ : SchwartzMap Space ℂ) :
    angularRealization m (angularProduct m hm h k) θ =
      ∫ x : Space, θ x *
        (angularBoundedRepresentative m (by exact_mod_cast hm) h x *
          angularBoundedRepresentative m (by exact_mod_cast hm) k x) := by
  rw [angularProduct_apply, angularRealization_cyclesToAngular]
  exact sobolevRealization_product m hm ((cyclesToAngular m).symm h) ((cyclesToAngular m).symm k) θ

end NSFormalization.Paper3
