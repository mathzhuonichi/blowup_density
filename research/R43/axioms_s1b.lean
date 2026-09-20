import NSFormalization.Section4.R43.Trilinear
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom and non-vacuity audit for lane 182-R43-s1b-trilinear.
Every theorem below must print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR)
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace NSFormalization.Section4.R43

#print axioms derivativeCriticalConst_pos
#print axioms rieszCoordinateSymbol_norm_le
#print axioms memHInfty_dirDeriv
#print axioms derivativeCriticalL3
#print axioms lintegral_enorm_mul_three_le
#print axioms criticalAdvectionHolder
#print axioms trilinearConst_eq
#print axioms trilinearConst_pos
#print axioms criticalTrilinearEstimate_of_hcrit
#print axioms rcritical1_of_hcrit

/-- Concrete zero-data realization of every field required by `hcrit`. -/
def zeroCriticalDatumPathS1b : CriticalDatumPath
    (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero where
  velocityHalf := fun _ => 0
  velocityThreeHalf := fun _ => 0
  laplacianHalf := fun _ => 0
  advectionHalf := fun _ => 0
  pressureHalf := fun _ => 0
  forceHalf := fun _ => 0
  velocityHalf_isDatum := by
    intro t ht
    rw [show (fun x => (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity (t, x)) =
      (0 : SpatialField) by rfl]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  velocityThreeHalf_isDatum := by
    intro t ht
    rw [show (fun x => (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity (t, x)) =
      (0 : SpatialField) by rfl]
    exact isHomogeneousSliceDatum_zero (3 / 2)
  laplacianHalf_isDatum := by
    intro t ht
    rw [show (fun x => spatialLaplacian
        (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity t x) =
      (0 : SpatialField) by
        funext x
        simp [spatialLaplacian, spatialDerivative]]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  advectionHalf_isDatum := by
    intro t ht
    rw [show (fun x => advection
        (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity t x) =
      (0 : SpatialField) by
        funext x
        simp [advection, spatialDerivative]]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  pressureHalf_isDatum := by
    intro t ht
    rw [show (fun x => pressureGradient
        (A04.zeroSol 1 2 (by norm_num) (by norm_num)).pressure t x) =
      (0 : SpatialField) by
        funext x
        simp [pressureGradient]]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  forceHalf_isDatum := by
    intro t ht
    rw [show (fun x => (0 : SpaceTimeField) (t, x)) = (0 : SpatialField) by rfl]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  velocityHalf_smooth := contDiffOn_const
  momentum := by
    intro t ht
    simp
  order_shift := by
    intro t ht i
    simp only [PiLp.zero_apply]
    change ((↑(0 : FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => (((‖ξ‖ : ℝ) : ℂ) * (↑(0 : FourierData) : Space → ℂ) ξ))
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := (volume : Measure Space))] with ξ hξ
    rw [hξ]
    simp
  laplacian_symbol := by
    intro t ht i
    simp only [PiLp.zero_apply]
    change ((↑(0 : FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => -((((‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (↑(0 : FourierData) : Space → ℂ) ξ)))
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := (volume : Measure Space))] with ξ hξ
    rw [hξ]
    simp
  velocity_transverse := by
    intro t ht
    simp
  pressure_longitudinal := by
    intro t ht
    exact ⟨0, by simp⟩

/-- The shifted `L³` carrier for the identically-zero velocity. -/
def zeroShiftedCriticalData :
    ShiftedCriticalData (0 : SpatialField) (0 : RealVectorSobolev (3 / 2)) where
  lambda := 0
  lambda_memHInfty := A04.zero_mem_initialClassR.1
  lambdaHalf_isDatum := isHomogeneousSliceDatum_zero (1 / 2)
  derivativeHalf := fun _ => 0
  derivativeHalf_isDatum := by
    intro j
    rw [show NSFormalization.Section4.A05.dirDeriv j (0 : SpatialField) =
      (0 : SpatialField) by
        funext x
        simp [NSFormalization.Section4.A05.dirDeriv]]
    exact isHomogeneousSliceDatum_zero (1 / 2)
  derivativeHalf_symbol := by
    intro j i
    simp only [PiLp.zero_apply]
    change ((↑(0 : FourierData) : Space → ℂ) =ᵐ[volume]
      fun ξ => rieszCoordinateSymbol j ξ *
        (↑(0 : FourierData) : Space → ℂ) ξ)
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := (volume : Measure Space))] with ξ hξ
    rw [hξ]
    simp

/-- The exact Parseval/carrier bridge is inhabited on the genuine zero
solution; in particular the named hypothesis is consistent. -/
def zeroCriticalAdvectionLpBridge :
    CriticalAdvectionLpBridge zeroCriticalDatumPathS1b where
  shifted := by
    intro t ht
    exact zeroShiftedCriticalData
  pairing_identity := by
    intro t ht
    simp [zeroCriticalDatumPathS1b, zeroShiftedCriticalData,
      NSFormalization.Section4.C01.lift, advection, spatialDerivative]

example :
    let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
    ∃ hcrit : CriticalDatumPath w A04.memForceR_zero,
      ∃ hbridge : CriticalAdvectionLpBridge hcrit,
        CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit ∧
          HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
            (criticalEnergyDerivative hcrit 1) 1 ∧
          criticalEnergyDerivative hcrit 1 / 2 +
              (1 - trilinearConst * criticalNormAt w.velocity 1) *
                criticalDissipationAt w.velocity 1 ^ 2
            ≤ criticalForceAt (0 : SpaceTimeField) 1 *
                criticalNormAt w.velocity 1 := by
  dsimp only
  have htri := criticalTrilinearEstimate_of_hcrit
    zeroCriticalDatumPathS1b zeroCriticalAdvectionLpBridge
  have hcritical := rcritical1_of_hcrit A04.memForceR_zero
    zeroCriticalDatumPathS1b zeroCriticalAdvectionLpBridge
  exact ⟨zeroCriticalDatumPathS1b, zeroCriticalAdvectionLpBridge, htri,
    hcritical.1 1 (by norm_num), hcritical.2 1 (by norm_num)⟩

end NSFormalization.Section4.R43
