import NSFormalization.Section4.A01.CommutatorBound
import Euler.SmoothInequalityTransfer
import Euler.ExternalTransportCommutator

/-! Continuity and smooth-to-finite transfer for the coordinate tame estimate.
The smooth cylinder estimate remains an explicit analytic hypothesis. -/
noncomputable section
namespace NSFormalization.Section4.A01
open EulerSobolevL2Product EulerFamilyNormTime EulerCylinderSobolev EulerMetricTransport
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution EulerTimeLp
  EulerRegularizedTopBlocks EulerSobolevMaximalRegularity EulerSobolevWordConstraints
  EulerTimeSobolevTransport EulerAsymmetricTransport EulerSobolevTransport
  EulerRegularizedEnergyFamily EulerTransportL2Time EulerRegularizedMetricPaths
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerMildTopWord
  EulerSobolevWordValueIdentity EulerSobolevEnergyPaths
open NSFormalization.Source.ForcedCylinderLocal

open EulerRealCylinder EulerVectorCylinder EulerTransportDerivatives
open EulerMildTopWord EulerH6Nonlinear EulerBaseTransportCommutator
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Recursive full Leibniz expansion. Each branch assigns the last derivative to
one of the two factors, until only scalar-vector products remain. -/
def cylinderLeibniz : {n : ℕ} → (Fin n → Fin 4) →
    (LiftDomain 1 → ℝ) → (LiftDomain 1 → Vector3) → LiftDomain 1 → Vector3
  | 0, _, f, g => fun x => f x • g x
  | n+1, w, f, g =>
      cylinderLeibniz (Fin.init w) (fieldDerivative 1 (standardDirection (w (Fin.last n))) f) g +
      cylinderLeibniz (Fin.init w) f (fieldDerivative 1 (standardDirection (w (Fin.last n))) g)

/-- The full recursive expansion is the actual derivative of the product. -/
theorem cylinderLeibniz_eq {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain 1 → ℝ) (g : LiftDomain 1 → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 g x)) :
    cylinderLeibniz w f g = iteratedFieldDerivative 1 w (fun x => f x • g x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [cylinderLeibniz, ih _ _ _ (fieldDerivative_smooth 1 _ f hf) hg,
      ih _ _ _ hf (fieldDerivative_smooth 1 _ g hg), word_init_last,
      fieldDerivative_smul 1 _ f g hf hg, word_add]
    · exact fun x => (fieldDerivative_smooth 1 _ f hf x).smul (hg x)
    · exact fun x => (hf x).smul (fieldDerivative_smooth 1 _ g hg x)

/-- Expand only the surviving commutator branches: every leaf has at least
one derivative on the scalar coefficient. For transport, g already has one derivative. -/
def cylinderCommutatorLeibniz : {n : ℕ} → (Fin n → Fin 4) →
    (LiftDomain 1 → ℝ) → (LiftDomain 1 → Vector3) → LiftDomain 1 → Vector3
  | 0, _, _, _ => 0
  | n+1, w, f, g =>
      cylinderLeibniz (Fin.init w) (fieldDerivative 1 (standardDirection (w (Fin.last n))) f) g +
      cylinderCommutatorLeibniz (Fin.init w) f
        (fieldDerivative 1 (standardDirection (w (Fin.last n))) g)

/-- Exact smooth-cylinder Leibniz cancellation, with the vendor's product-minus-transport sign. -/
theorem cylinderCommutatorLeibniz_eq {n : ℕ} (w : Fin n → Fin 4)
    (f : LiftDomain 1 → ℝ) (g : LiftDomain 1 → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 g x)) :
    cylinderCommutatorLeibniz w f g = scalarCommutator 1 w f g := by
  induction n generalizing g with
  | zero => simp [cylinderCommutatorLeibniz, scalarCommutator, iteratedFieldDerivative_zero]
  | succ n ih =>
    rw [cylinderCommutatorLeibniz, cylinderLeibniz_eq _ _ _
      (fieldDerivative_smooth 1 _ f hf) hg,
      ih _ _ (fieldDerivative_smooth 1 _ g hg), scalarCommutator_recurrence 1 w f g hf hg]

/-- The transport-minus-product sign used by lane 202 is the negative of the
smooth expansion. Word differentiation commutes with the transport direction. -/
theorem cylinderCoordinateLeibniz_sign {n : ℕ} (w : Fin n → Fin 4) (i : Fin 4)
    (f : LiftDomain 1 → ℝ) (g : LiftDomain 1 → Vector3)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift 1 g x)) :
    (fun x => f x • fieldDerivative 1 (standardDirection i)
      (iteratedFieldDerivative 1 w g) x) -
      iteratedFieldDerivative 1 w (fun x => f x • fieldDerivative 1 (standardDirection i) g x) =
    -cylinderCommutatorLeibniz w f (fieldDerivative 1 (standardDirection i) g) := by
  rw [cylinderCommutatorLeibniz_eq _ _ _ hf (fieldDerivative_smooth 1 _ g hg),
    scalarCommutator, EulerExternalTransportCommutator.word_derivative_comm 1 w _ g hg]
  exact (neg_sub _ _).symm

/-- The gradient uses exactly the finite word array, and is continuous at its stated order. -/
theorem cylinderWordGradient_continuous (q : ℕ) :
    Continuous (cylinderWordGradient : SobolevSpace 1 (2+q) → ℝ) := by
  unfold cylinderWordGradient
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro w _
  exact (((wordOperator 1 w).continuous.comp (derivativeOperator 1 (q+1) i).continuous).comp
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).continuous).norm.pow 2

-- Avoid unfolding the analytic construction of the bounded products during unification.
attribute [local irreducible] productHqBilinear scalarProductBilinear
  cylinderCoordinateCommutator

-- Dependent word operators and bilinear maps require additional elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Both sides of the commutator are continuous bilinear operations at finite order. -/
theorem cylinderCoordinateCommutator_continuous {q : ℕ} (hq : 6 ≤ q) (i : Fin 4) :
    Continuous (fun p : SobolevSpace 1 (q+1) × SobolevSpace 1 (2+q) =>
      cylinderCoordinateCommutator hq p.1 p.2 i) := by
  unfold cylinderCoordinateCommutator
  have hd : Continuous (derivativeOperator 1 (q+1) i) :=
    (derivativeOperator 1 (q+1) i).continuous
  have hr : Continuous (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)) :=
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).continuous
  have hp : Continuous (fun p : SobolevSpace 1 (q+1) × SobolevSpace 1 (q+1) =>
      productHqBilinear 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0 i)
        (velocityComponents_norm 1 0 (by norm_num) (by simp) i) p.1 p.2) :=
    (productHqBilinear 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0 i)
      (velocityComponents_norm 1 0 (by norm_num) (by simp) i)).continuous₂
  have hs : Continuous (fun p : SobolevSpace 1 (q+1) × LiftL2 1 =>
      scalarProductBilinear 1 (by omega : 3 ≤ q+1) (velocityComponents 1 0 i) p.1 p.2) :=
    (scalarProductBilinear 1 (by omega : 3 ≤ q+1) (velocityComponents 1 0 i)).continuous₂
  have hv : Continuous (valueOperator 1 0) := (valueOperator 1 0).continuous
  have hd0 : Continuous (derivativeOperator 1 0 i) := (derivativeOperator 1 0 i).continuous
  apply continuous_pi
  intro w
  have hb : Continuous (boundedWordBlock 1 1 w.1.val (q := 2+q)
      (by have := w.1.isLt; omega) w.2) :=
    (boundedWordBlock 1 1 w.1.val (q := 2+q)
      (by have := w.1.isLt; omega) w.2).continuous
  have hw : Continuous (wordOperator 1 w) := (wordOperator 1 w).continuous
  exact (hs.comp (continuous_fst.prodMk ((hv.comp (hd0.comp hb)).comp continuous_snd))).sub
    (hw.comp (hp.comp (continuous_fst.prodMk ((hd.comp hr).comp continuous_snd))))

/-- ONE remaining analytic input: the estimate only on genuine smooth H-infinity
cylinder representatives. No ordinary-lift or angular-invariance restriction is imposed. -/
def SmoothCylinderCoordinateTame (q : ℕ) (hq : 6 ≤ q) (C : ℝ) : Prop :=
  ∀ (V : SobolevSpace 1 (2+q)) (f : LiftDomain 1 → Vector3),
    (value 1 V : LiftDomain 1 → Vector3) =ᵐ[liftMeasure 1] f →
    (∀ x, ContDiff ℝ ∞ (localFieldLift 1 f x)) →
    (∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative 1 w f) 2 (liftMeasure 1)) →
    ∀ i : Fin 4,
      familyNorm (cylinderCoordinateCommutator hq
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V) V i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq)
        (restrictOperator 1 (by omega : q+1 ≤ 2+q) V)‖ * cylinderWordGradient V

-- Elaborating both continuous functionals involves the dependent finite word types.
set_option maxHeartbeats 400000 in
/-- Genuine heat/mollifier density discharges the finite-order limit passage.
The same approximation is restricted to obtain the coefficient, preserving compatibility. -/
theorem cylinderCoordinateTame {q : ℕ} (hq : 6 ≤ q) {C : ℝ}
    (h : SmoothCylinderCoordinateTame q hq C) : CylinderCoordinateTame q hq C := by
  intro v V hV i
  subst v
  let F := fun p : SobolevSpace 1 (2+q) × SobolevSpace 1 (2+q) =>
    familyNorm (cylinderCoordinateCommutator hq
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) p.1) p.1 i)
  let G := fun p : SobolevSpace 1 (2+q) × SobolevSpace 1 (2+q) =>
    C * ‖restrictOperator 1 (Nat.succ_le_succ hq)
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) p.1)‖ * cylinderWordGradient p.1
  have hr : Continuous (restrictOperator 1 (by omega : q+1 ≤ 2+q)) :=
    (restrictOperator 1 (by omega : q+1 ≤ 2+q)).continuous
  have hl : Continuous (restrictOperator 1 (Nat.succ_le_succ hq)) :=
    (restrictOperator 1 (Nat.succ_le_succ hq)).continuous
  have hn : Continuous (familyNorm : (SobolevWord (q+1) → LiftL2 1) → ℝ) :=
    familyNorm_lipschitz.continuous
  have hR : Continuous (fun p : SobolevSpace 1 (2+q) × SobolevSpace 1 (2+q) =>
      (restrictOperator 1 (by omega : q+1 ≤ 2+q) p.1, p.1)) :=
    (hr.comp continuous_fst).prodMk continuous_fst
  have hF : Continuous F := hn.comp ((cylinderCoordinateCommutator_continuous hq i).comp hR)
  have hG : Continuous G := (continuous_const.mul
    ((hl.comp (hr.comp continuous_fst)).norm)).mul
      ((cylinderWordGradient_continuous q).comp continuous_fst)
  exact EulerSmoothInequalityTransfer.binary_le_of_smooth 1 F G hF hG
    (fun U _ f _ hf _ hfs _ hfL _ => h U f hf hfs hfL i) V V

/-- Conditional existence; the smooth uniform constant has NOT been constructed here. -/
theorem cylinderCoordinateTame_exists {q : ℕ} (hq : 6 ≤ q)
    (h : ∃ C : ℝ, SmoothCylinderCoordinateTame q hq C) :
    ∃ C : ℝ, CylinderCoordinateTame q hq C := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, cylinderCoordinateTame hq hC⟩

/-- The smooth restriction is equivalent to the finite estimate: density loses no constant. -/
theorem smoothCylinderCoordinateTame_iff {q : ℕ} (hq : 6 ≤ q) (C : ℝ) :
    SmoothCylinderCoordinateTame q hq C ↔ CylinderCoordinateTame q hq C := by
  refine ⟨cylinderCoordinateTame hq, ?_⟩
  intro h V _ _ _ _ i
  exact h _ V rfl i

/-- A numerical enlargement only; this definition does not certify any analytic estimate. -/
def coordinateTameA (q : ℕ) (C : ℝ) : ℝ := max (A q) (C / 4)

theorem coordinateTameA_nonneg (q : ℕ) (C : ℝ) : 0 ≤ coordinateTameA q C :=
  (A_nonneg q).trans (le_max_left _ _)

/-- The recut absorbs the factor four from the coordinate sum in lane 200's factor sixteen. -/
theorem coordinateTameA_absorbs (q : ℕ) (C : ℝ) : C ≤ 4 * coordinateTameA q C := by
  have h : C / 4 ≤ coordinateTameA q C := le_max_right _ _
  linarith

/-- Conditional cylinder tame bound with the honest enlarged constant. -/
theorem cylinderCommutatorBound_recut {q : ℕ} (hq : 6 ≤ q) {C : ℝ}
    (h : SmoothCylinderCoordinateTame q hq C)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q))
    (hV : restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v) :
    familyNorm (cylinderCommutator hq v V) ≤
      coordinateTameA q C * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        cylinderWordGradient V := by
  apply (cylinderCommutator_le hq (cylinderCoordinateTame hq h) v V hV).trans
  have hC := coordinateTameA_absorbs q C
  have hn := norm_nonneg (restrictOperator 1 (Nat.succ_le_succ hq) v)
  have hg : 0 ≤ cylinderWordGradient V := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn) hg]

/-- Keeping the old numerical API is also possible, if its smooth estimate is supplied. -/
theorem cylinderCommutatorBound_of_smooth {q : ℕ} (hq : 6 ≤ q)
    (h : SmoothCylinderCoordinateTame q hq (4 * A q)) : CylinderCommutatorBound q hq :=
  cylinderCommutatorBound hq (cylinderCoordinateTame hq h) le_rfl

/-- Conditional composition with lane 200's unchanged forcing predicate and enlarged A. -/
theorem forcingFamilyBound_of_cylinder_recut {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {C : ℝ}
    (h : SmoothCylinderCoordinateTame q hq C) :
    ForcingFamilyBound hq hν a F hF (E q) (coordinateTameA q C) := by
  intro T hT hTS u _hu U hU
  have hrestriction := EulerSobolevMaximalRegularity.maximal_limit_restriction 1 T hT u U hU
  filter_upwards [cylinderEnergyForcing_ae hq hT hTS F hF u U, hrestriction,
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q)).coeFn_compLpL U]
    with r hz hr hv
  have hc := cylinderCommutatorBound_recut hq h (extendPath T hT u r) (U r) hr
  have hg : Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
      ‖(derivativeOperator 1 (q+1) i
        (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) (U r))).val w‖^2) =
      energyGradientNorm U r := by
    unfold energyGradientNorm
    change reindexMaximalTime 1 q T U r = _ at hv
    rw [hv]
  change familyNorm _ ≤ coordinateTameA q C * (16 * _) *
    (Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
      ‖(derivativeOperator 1 (q+1) i
        (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) (U r))).val w‖^2)) at hc
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
          coordinateTameA q C * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
            (extendPath T hT u r)‖) * energyGradientNorm U r) :=
      mul_le_mul_of_nonneg_left hb hx
    _ = _ := by ring


/-- Fixed-constant composition with lane 202's original primed forcing theorem. -/
theorem forcingFamilyBound_of_smooth {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (h : SmoothCylinderCoordinateTame q hq (4 * A q)) :
    ForcingFamilyBound hq hν a F hF (E q) (A q) :=
  forcingFamilyBound_of_cylinder' hq hν a F hF (cylinderCoordinateTame hq h)

end NSFormalization.Section4.A01
