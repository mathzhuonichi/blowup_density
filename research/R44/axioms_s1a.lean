import NSFormalization.Section4.R44.JWeight
import NSFormalization.Section4.D01.OrderZeroSymbol

/-!
# Axiom and satisfiability audit for R44 row S1a

Every printed declaration must report exactly
`[propext, Classical.choice, Quot.sound]`.  The examples instantiate the one
named input structure first at zero data and then at a genuinely nonzero
compact-smooth (hence componentwise Schwartz) velocity field.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Section4.D01
open NSFormalization.Section4.R44
open scoped ContDiff ENNReal LineDeriv RealInnerProductSpace SchwartzMap

namespace Lane218S1AAudit

/-! ## Zero datum -/

def zeroJWeightDatum : JWeightDatum (0 : Space → Space) (0 : Space → Space) where
  velocityHalf := 0
  velocityThreeHalf := 0
  gradientHalf := fun _ => 0
  forceNegHalf := 0
  velocityHalf_isDatum := isSobolevDatum_zero (1 / 2)
  velocityThreeHalf_isDatum := isSobolevDatum_zero (3 / 2)
  gradientHalf_isDatum := by
    intro j
    rw [show partialDeriv j (0 : Space → Space) = 0 by
      funext x
      simp [partialDeriv, NSFormalization.Section4.A03.lift, spatialDerivative]]
    exact isSobolevDatum_zero (1 / 2)
  forceNegHalf_isDatum := isSobolevDatum_zero (-1 / 2)
  gradient_pairing := by
    simp [partialDeriv, NSFormalization.Section4.A03.lift, spatialDerivative]

example :
    (sobolevENorm (3 / 2) (0 : Space → Space)).toReal ^ 2 =
      Y (0 : Space → Space) ^ 2 + Z (0 : Space → Space) ^ 2 :=
  weight_identity zeroJWeightDatum

example :
    |forceJPairing zeroJWeightDatum| ≤
      B (0 : Space → Space) *
        Real.sqrt (Y (0 : Space → Space) ^ 2 +
          Z (0 : Space → Space) ^ 2) :=
  force_pairing_le zeroJWeightDatum

/-! ## A nonzero compact-smooth datum -/

local notation "zB" =>
  (fun x : Space => (Cut.bump x) • (coordinateVector 0 : Space))

theorem bumpField_smooth : ContDiff ℝ ∞ zB :=
  Cut.bump_smooth.smul contDiff_const

theorem bumpField_compact : HasCompactSupport zB := by
  exact Cut.bump_cs.comp_left
    (g := fun c : ℝ => c • (coordinateVector 0 : Space)) (by simp)

theorem bumpField_ne_zero : zB ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Space)
  have hb : Cut.bump (0 : Space) = 1 := Cut.bump_one (by simp)
  have hc := congrArg (fun v : Space => v 0) h0
  simp [hb, coordinateVector] at hc

def bumpSmoothL2 : EulerLpTranslation.SmoothL2Field Space where
  field := zB
  smooth := bumpField_smooth
  integrable := fun n =>
    (bumpField_smooth.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
        (bumpField_compact.iteratedFDeriv n)

def bumpVelocityHalf : RealVectorSobolev (1 / 2) :=
  smoothAngularDatum 2 (1 / 2) (by norm_num) bumpSmoothL2

def bumpVelocityThreeHalf : RealVectorSobolev (3 / 2) :=
  smoothAngularDatum 2 (3 / 2) (by norm_num) bumpSmoothL2

theorem bumpVelocityThreeHalf_isDatum :
    IsSobolevDatum (3 / 2) zB bumpVelocityThreeHalf := by
  unfold bumpVelocityThreeHalf
  exact smoothAngularDatum_isSobolevDatum 2 (3 / 2) (by norm_num) bumpSmoothL2

def bumpGradientSmoothL2 (j : Fin 3) : EulerLpTranslation.SmoothL2Field Space :=
  bumpSmoothL2.directionalField (coordinateVector j)

def bumpGradientHalf (j : Fin 3) : RealVectorSobolev (1 / 2) :=
  smoothAngularDatum 2 (1 / 2) (by norm_num) (bumpGradientSmoothL2 j)

theorem bump_gradient_pairing (j i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((partialDeriv j zB x i : ℝ) : ℂ) =
      ∫ x, (-∂_{coordinateVector j} ψ) x * ((zB x i : ℝ) : ℂ) := by
  rw [NSFormalization.Section4.A03.partialDeriv_eq_dirDeriv]
  simpa [bumpSmoothL2, NSFormalization.Section4.A05.dirDeriv] using
    (smoothField_weakDeriv_pairing bumpSmoothL2 j i ψ)

theorem bumpGradientHalf_isDatum (j : Fin 3) :
    IsSobolevDatum (1 / 2) (partialDeriv j zB) (bumpGradientHalf j) := by
  rw [NSFormalization.Section4.A03.partialDeriv_eq_dirDeriv]
  exact smoothAngularDatum_isSobolevDatum 2 (1 / 2) (by norm_num)
    (bumpGradientSmoothL2 j)

def bumpJWeightDatum : JWeightDatum zB (0 : Space → Space) where
  velocityHalf := bumpVelocityHalf
  velocityThreeHalf := bumpVelocityThreeHalf
  gradientHalf := bumpGradientHalf
  forceNegHalf := 0
  velocityHalf_isDatum :=
    smoothAngularDatum_isSobolevDatum 2 (1 / 2) (by norm_num) bumpSmoothL2
  velocityThreeHalf_isDatum :=
    bumpVelocityThreeHalf_isDatum
  gradientHalf_isDatum := bumpGradientHalf_isDatum
  forceNegHalf_isDatum := isSobolevDatum_zero (-1 / 2)
  gradient_pairing := bump_gradient_pairing

/-- The sole named input of S1a is satisfiable by a nonzero Schwartz-type
velocity, and all three conclusions apply to it. -/
theorem nonzero_bump_satisfies_S1a :
    zB ≠ 0 ∧
      (sobolevENorm (3 / 2) zB).toReal ^ 2 =
        Y zB ^ 2 + Z zB ^ 2 ∧
      |forceJPairing bumpJWeightDatum| ≤
        B (0 : Space → Space) *
          (Y zB + Z zB) :=
  ⟨bumpField_ne_zero, weight_identity bumpJWeightDatum,
    force_pairing_le' bumpJWeightDatum⟩

example :
    zB ≠ 0 ∧
      (sobolevENorm (3 / 2) zB).toReal ^ 2 =
        Y zB ^ 2 + Z zB ^ 2 ∧
      |forceJPairing bumpJWeightDatum| ≤
        B (0 : Space → Space) *
          (Y zB + Z zB) :=
  nonzero_bump_satisfies_S1a

end Lane218S1AAudit

/-! ## Exported-declaration audit -/

#print axioms Jmul
#print axioms Jmul_weighted_symbol
#print axioms Jmul_symbol
#print axioms Jmul_norm
#print axioms Jmul_enorm
#print axioms JWeightDatum
#print axioms Y
#print axioms Z
#print axioms B
#print axioms forceJPairing
#print axioms sobolevENorm_eq_of_isSobolevDatum
#print axioms Y_eq_norm
#print axioms Z_sq_eq_sum_norm
#print axioms B_eq_norm
#print axioms weight_identity
#print axioms force_pairing_le
#print axioms force_pairing_le'

#print axioms Lane218S1AAudit.zeroJWeightDatum
#print axioms Lane218S1AAudit.bumpField_smooth
#print axioms Lane218S1AAudit.bumpField_compact
#print axioms Lane218S1AAudit.bumpField_ne_zero
#print axioms Lane218S1AAudit.bumpSmoothL2
#print axioms Lane218S1AAudit.bumpVelocityHalf
#print axioms Lane218S1AAudit.bumpVelocityThreeHalf
#print axioms Lane218S1AAudit.bumpVelocityThreeHalf_isDatum
#print axioms Lane218S1AAudit.bumpGradientSmoothL2
#print axioms Lane218S1AAudit.bumpGradientHalf
#print axioms Lane218S1AAudit.bump_gradient_pairing
#print axioms Lane218S1AAudit.bumpGradientHalf_isDatum
#print axioms Lane218S1AAudit.bumpJWeightDatum
#print axioms Lane218S1AAudit.nonzero_bump_satisfies_S1a
