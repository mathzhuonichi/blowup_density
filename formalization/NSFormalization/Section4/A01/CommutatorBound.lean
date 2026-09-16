import NSFormalization.Section4.A01.ForcingFamilyBound

/-! Finite-carrier coordinate expansion and conditional tame assembly.
`CylinderCoordinateTame` is an unproved analytic input, including the cylinder
interpolation and finite-order limit passage. No Kato–Ponce constant is proved here. -/
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

open EulerSobolevL2Product EulerFamilyNormTime

/-- The precise full gradient word norm; all four cylinder directions are retained. -/
def cylinderWordGradient {q : ℕ} (V : SobolevSpace 1 (2+q)) : ℝ :=
  Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
    ‖(derivativeOperator 1 (q+1) i
      (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)

/-- One coordinate of the actual finite-order commutator, with lane 200's sign. -/
def cylinderCoordinateCommutator {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) (i : Fin 4) :
    SobolevWord (q+1) → LiftL2 1 := fun w =>
  scalarProductBilinear 1 (by omega : 3 ≤ q+1) (velocityComponents 1 0 i) v
    (valueOperator 1 0 (derivativeOperator 1 0 i
      (boundedWordBlock 1 1 w.1.val (by have := w.1.isLt; omega) w.2 V))) -
  (productHqBilinear 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0 i)
    (velocityComponents_norm 1 0 (by norm_num) (by simp) i) v
    (derivativeOperator 1 (q+1) i
      (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V))).val w

-- Dependent word blocks and subtype sums need additional elaboration fuel.
set_option maxHeartbeats 400000 in
/-- Exact coordinate expansion on finite Sobolev elements, without smoothness premises. -/
theorem cylinderCommutator_eq_sum {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) :
    cylinderCommutator hq v V = ∑ i : Fin 4, cylinderCoordinateCommutator hq v V i := by
  funext w
  have hs (f : Fin 4 → SobolevSpace 1 (q+1)) :
      (∑ i, f i).val w = ∑ i, (f i).val w := by
    exact congrArg (fun z : SobolevWord (q+1) → LiftL2 1 => z w)
      (map_sum (sobolevSubspace 1 (q+1)).toSubmodule.subtype f Finset.univ)
  simp only [cylinderCommutator, cylinderCoordinateCommutator, transportL2Bilinear,
    asymmetricTransport, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    Finset.sum_apply, hs, Finset.sum_sub_distrib]

/-- The empty word cancels on arbitrary finite elements, before taking any norm. -/
theorem cylinderCoordinateCommutator_empty {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) (i : Fin 4) :
    cylinderCoordinateCommutator hq v V i (emptyWord (q+1)) = 0 := by
  unfold cylinderCoordinateCommutator
  rw [scalarProductBilinear_apply, productHqBilinear_apply]
  change _ - value 1 (productHq 1 _ _ _ _ _) = 0
  rw [productHq_value]
  exact sub_self _

/-- The undifferentiated word contributes no forcing residual. -/
theorem cylinderCommutator_empty {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) :
    cylinderCommutator hq v V (emptyWord (q+1)) = 0 := by
  rw [cylinderCommutator_eq_sum]
  simp only [Finset.sum_apply, cylinderCoordinateCommutator_empty, Finset.sum_const_zero]

/-- The ONE missing analytic fact, parameterized by an uncertified real constant.
It must hold uniformly on compatible finite cylinder elements, including angular dependence. -/
def CylinderCoordinateTame (q : ℕ) (hq : 6 ≤ q) (C : ℝ) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    ∀ i : Fin 4, familyNorm (cylinderCoordinateCommutator hq v V i) ≤
      C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V

/-- Summing coordinates costs exactly four, independently of the number of words. -/
theorem cylinderCommutator_le {q : ℕ} (hq : 6 ≤ q) {C : ℝ}
    (htame : CylinderCoordinateTame q hq C)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q))
    (hV : restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v) :
    familyNorm (cylinderCommutator hq v V) ≤
      (4*C) * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V := by
  rw [cylinderCommutator_eq_sum, familyNorm_eq_piLp, map_sum]
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    htame v V hV i)
  simp only [familyNorm_eq_piLp] at h
  exact h.trans_eq (by simp; ring)

/-- Conditional existence only: supplying a coordinate tame constant supplies a family constant. -/
theorem cylinderCommutatorBound_exists {q : ℕ} (hq : 6 ≤ q)
    (htame : ∃ C : ℝ, CylinderCoordinateTame q hq C) :
    ∃ C : ℝ, ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
      restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
      familyNorm (cylinderCommutator hq v V) ≤
        C * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖ * cylinderWordGradient V := by
  obtain ⟨C, hC⟩ := htame
  exact ⟨4*C, cylinderCommutator_le hq hC⟩

/-- Lane 200's numerical constant is usable only after the displayed comparison is supplied. -/
theorem cylinderCommutatorBound {q : ℕ} (hq : 6 ≤ q) {C : ℝ}
    (htame : CylinderCoordinateTame q hq C) (hC : C ≤ 4 * A q) :
    CylinderCommutatorBound q hq := by
  intro v V hV
  apply (cylinderCommutator_le hq htame v V hV).trans
  change _ ≤ A q * (16 * _) * cylinderWordGradient V
  have hn := norm_nonneg (restrictOperator 1 (Nat.succ_le_succ hq) v)
  have hg : 0 ≤ cylinderWordGradient V := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hC hn,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn) hg]

/-- Conditional composition; the analytic input has not been discharged. -/
theorem forcingFamilyBound_of_cylinder' {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (htame : CylinderCoordinateTame q hq (4 * A q)) :
    ForcingFamilyBound hq hν a F hF (E q) (A q) :=
  forcingFamilyBound_of_cylinder hq hν a F hF (cylinderCommutatorBound hq htame le_rfl)

end NSFormalization.Section4.A01
