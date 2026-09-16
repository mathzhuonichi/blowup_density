import NSFormalization.Section4.R44.TrilinearJ
import NSFormalization.Section4.A04.ZeroSolution
import NSFormalization.Section4.D01.OrderZeroSymbol

/-!
# Axiom and satisfiability audit for R44 row S1c

Every printed declaration must report exactly
`[propext, Classical.choice, Quot.sound]`.  The examples instantiate the full
S1c input at zero and reuse lane 218's genuinely nonzero compact-smooth datum.
For that nonzero datum they also instantiate the canonical physical `Ju`
representative and its half-order realization.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Section4.D01
open NSFormalization.Section4.R44
open scoped ContDiff ENNReal LineDeriv RealInnerProductSpace SchwartzMap

namespace Lane220S1CAudit

/-! ## Full zero instance -/

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

def zeroAdvectionJDatum : AdvectionJDatum zeroJWeightDatum where
  velocity_memHInfty :=
    memHInfty_iff_smoothSquareIntegrableJets.mpr
      NSFormalization.Section4.A04.jets_zero
  advectionNegHalf := 0
  advectionNegHalf_isDatum := by
    rw [show advectionFieldJ (0 : Space → Space) = 0 by
      funext x
      simp [advectionFieldJ, NSFormalization.Section4.C01.lift,
        advection, spatialDerivative]]
    exact isSobolevDatum_zero (-1 / 2)

example :
    |advectionJPairing zeroJWeightDatum zeroAdvectionJDatum| ≤
      trilinearConstJ * Y (0 : Space → Space) *
        (Y (0 : Space → Space) ^ 2 + Z (0 : Space → Space) ^ 2) :=
  advection_pairing_le zeroJWeightDatum zeroAdvectionJDatum

/-! ## Lane 218's nonzero compact-smooth datum -/

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
    smoothAngularDatum_isSobolevDatum 2 (3 / 2) (by norm_num) bumpSmoothL2
  gradientHalf_isDatum := bumpGradientHalf_isDatum
  forceNegHalf_isDatum := isSobolevDatum_zero (-1 / 2)
  gradient_pairing := bump_gradient_pairing

theorem bumpVelocity_jets : SmoothSquareIntegrableJets zB :=
  ⟨bumpSmoothL2.smooth, bumpSmoothL2.integrable⟩

theorem bumpVelocity_memHInfty :
    NSFormalization.Section4.A02.MemHInfty zB :=
  memHInfty_iff_smoothSquareIntegrableJets.mpr bumpVelocity_jets

theorem bumpAdvection_jets : SmoothSquareIntegrableJets (advectionFieldJ zB) := by
  change SmoothSquareIntegrableJets
    (NSFormalization.Section4.A03.advectionOf zB zB)
  exact advectionOf_smoothL2 bumpVelocity_jets

def bumpAdvectionSmoothL2 : EulerLpTranslation.SmoothL2Field Space where
  field := advectionFieldJ zB
  smooth := bumpAdvection_jets.1
  integrable := bumpAdvection_jets.2

def bumpAdvectionNegHalf : RealVectorSobolev (-1 / 2) :=
  smoothAngularDatum 2 (-1 / 2) (by norm_num) bumpAdvectionSmoothL2

theorem bumpAdvectionNegHalf_isDatum :
    IsSobolevDatum (-1 / 2) (advectionFieldJ zB) bumpAdvectionNegHalf :=
  smoothAngularDatum_isSobolevDatum 2 (-1 / 2) (by norm_num)
    bumpAdvectionSmoothL2

/-- The entire separate S1c package is satisfiable by lane 218's genuinely
nonzero compact-smooth velocity.  The package assumes no Parseval field; the
final estimate derives its pairing identity from the general inhomogeneous
dual-order theorem. -/
def bumpAdvectionJDatum : AdvectionJDatum bumpJWeightDatum where
  velocity_memHInfty := bumpVelocity_memHInfty
  advectionNegHalf := bumpAdvectionNegHalf
  advectionNegHalf_isDatum := bumpAdvectionNegHalf_isDatum

/-- The S1c physical reassembly is inhabited by lane 218's genuinely nonzero
datum: its canonical `L²` field realizes `Jmul` at order one half. -/
example :
    zB ≠ 0 ∧
      MemLp (halfDatumPhysicalField (Jmul bumpVelocityThreeHalf)) 2 volume ∧
      IsSobolevDatum (1 / 2)
        (halfDatumPhysicalField (Jmul bumpVelocityThreeHalf))
        (Jmul bumpVelocityThreeHalf) :=
  ⟨bumpField_ne_zero, halfDatumPhysicalField_memLp _,
    halfDatumPhysicalField_isDatum _⟩

example : Nonempty (JWeightDatum zB (0 : Space → Space)) :=
  ⟨bumpJWeightDatum⟩

example :
    zB ≠ 0 ∧
      |advectionJPairing bumpJWeightDatum bumpAdvectionJDatum| ≤
        trilinearConstJ * Y zB * (Y zB ^ 2 + Z zB ^ 2) :=
  ⟨bumpField_ne_zero, advection_pairing_le bumpJWeightDatum bumpAdvectionJDatum⟩

end Lane220S1CAudit

/-! ## Exported-declaration audit -/

#print axioms halfHomogeneousComponent
#print axioms halfHomogeneousComponent_coe
#print axioms halfHomogeneousDatum
#print axioms halfHomogeneousDatum_norm_le
#print axioms halfHomogeneousDatum_isDatum
#print axioms inhomogeneousCriticalL3
#print axioms halfDatumCyclesComponent
#print axioms halfDatumPhysicalComponent
#print axioms halfDatumPhysicalComponent_real
#print axioms halfDatumPhysicalLp
#print axioms halfDatumPhysicalField
#print axioms halfDatumPhysicalField_memLp
#print axioms halfDatumPhysicalField_isDatum
#print axioms inhomogeneous_half_order_parseval
#print axioms advectionFieldJ
#print axioms AdvectionJDatum
#print axioms advectionJPairing
#print axioms advectionJHolder
#print axioms trilinearConstJ
#print axioms trilinearConstJ_pos
#print axioms advection_pairing_le_sqrt
#print axioms advection_pairing_le

#print axioms Lane220S1CAudit.zeroJWeightDatum
#print axioms Lane220S1CAudit.zeroAdvectionJDatum
#print axioms Lane220S1CAudit.bumpField_smooth
#print axioms Lane220S1CAudit.bumpField_compact
#print axioms Lane220S1CAudit.bumpField_ne_zero
#print axioms Lane220S1CAudit.bumpSmoothL2
#print axioms Lane220S1CAudit.bumpVelocityHalf
#print axioms Lane220S1CAudit.bumpVelocityThreeHalf
#print axioms Lane220S1CAudit.bumpGradientSmoothL2
#print axioms Lane220S1CAudit.bumpGradientHalf
#print axioms Lane220S1CAudit.bump_gradient_pairing
#print axioms Lane220S1CAudit.bumpGradientHalf_isDatum
#print axioms Lane220S1CAudit.bumpJWeightDatum
#print axioms Lane220S1CAudit.bumpVelocity_jets
#print axioms Lane220S1CAudit.bumpVelocity_memHInfty
#print axioms Lane220S1CAudit.bumpAdvection_jets
#print axioms Lane220S1CAudit.bumpAdvectionSmoothL2
#print axioms Lane220S1CAudit.bumpAdvectionNegHalf
#print axioms Lane220S1CAudit.bumpAdvectionNegHalf_isDatum
#print axioms Lane220S1CAudit.bumpAdvectionJDatum
