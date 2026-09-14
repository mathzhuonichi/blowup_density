-- Axiom audit for lane 145 (D01 · D-quant): the quantitative finite-order datum constructor.
-- Every new declaration of `Section4/D01/FiniteOrderNorm.lean` must print exactly
-- [propext, Classical.choice, Quot.sound].  Compiles under `lake env lean` from verification/.
import NSFormalization.Section4.D01.FiniteOrderNorm

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open scoped SchwartzMap

-- §0 the Euclidean-valued Plancherel/Pythagoras L² identity
#print axioms eLpNorm_two_sq
#print axioms eLpNorm_component_sq_sum
#print axioms norm_toLp_component_sq_sum
-- §1 deliverable 1: the order-0 bound (c₀ = 1)
#print axioms norm_orderZeroDatum_le
-- §2 deliverable 2: the raising bound (c = 4)
#print axioms coord_smul_deriv_ae
#print axioms eLpNorm_coord_smul_eq
#print axioms norm_raiseHilbert_le
#print axioms norm_raise_le
-- §3 deliverable 3: the quantitative constructor (c_m = 16^m)
#print axioms HasWeakDerivsL2Bound
#print axioms weakDerivsBound_mono
#print axioms exists_isSobolevDatum_norm_le
#print axioms norm_isSobolevDatum_le_of_memLp_derivs
#print axioms norm_isSobolevDatum_le_two
-- §4 non-vacuity
#print axioms weakDerivsBound_mono_le
#print axioms exists_hasWeakDerivsL2Bound_smooth
#print axioms hasWeakDerivsL2_of_bound

-- Non-vacuity, concrete: a smooth compactly supported field.  The order-0 bound of deliverable 1
-- applies to any square-integrable field, e.g. every `SmoothL2Field`; and the whole order-2 chain
-- has an inhabited hypothesis class, so `norm_isSobolevDatum_le_two` is not vacuous.
example (Z : EulerLpTranslation.SmoothL2Field Space) :
    ‖orderZeroDatum Z.memLp‖ ≤ ‖Z.memLp.toLp‖ :=
  norm_orderZeroDatum_le Z.memLp

example (Z : EulerLpTranslation.SmoothL2Field Space) :
    ∃ M : ℝ, HasWeakDerivsL2Bound Z.field M 2 :=
  exists_hasWeakDerivsL2Bound_smooth 2 Z

-- the order-2 cap is genuinely inhabited and quantitative: some bound M and some datum give ‖A‖² ≤ 256 M
example (Z : EulerLpTranslation.SmoothL2Field Space) :
    ∃ (M : ℝ) (A : NSFormalization.Paper3.RealVectorSobolev ((2 : ℕ) : ℝ)),
      IsSobolevDatum ((2 : ℕ) : ℝ) Z.field A ∧ ‖A‖ ^ 2 ≤ 256 * M := by
  obtain ⟨M, hM⟩ := exists_hasWeakDerivsL2Bound_smooth 2 Z
  obtain ⟨A, hA, _⟩ := exists_isSobolevDatum_norm_le 2 Z.field M hM
  exact ⟨M, A, hA, norm_isSobolevDatum_le_two Z.field M hM A hA⟩
