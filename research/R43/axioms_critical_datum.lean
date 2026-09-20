import NSFormalization.Section4.R43.CriticalDatumPath
import NSFormalization.Section4.A04.ZeroSolution

/-! Lane 216: axiom audit for every declaration in `CriticalDatumPath.lean`,
followed by a genuine zero-solution witness for the sole fallback input. -/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff

noncomputable section
namespace NSFormalization.Section4.R43

#print axioms CriticalHomogeneous.besselFractionalDatum_mem_realSubspace
#print axioms CriticalHomogeneous.ofSobolevScalar
#print axioms CriticalHomogeneous.ofSobolevScalar_ae
#print axioms CriticalHomogeneous.ofSobolevScalar_weight_ae
#print axioms CriticalHomogeneous.ofSobolevScalar_isHomogeneousDatum
#print axioms CriticalHomogeneous.ofSobolevVector
#print axioms CriticalHomogeneous.ofSobolevVector_apply
#print axioms CriticalHomogeneous.ofSobolevVector_isHomogeneousSliceDatum
#print axioms CriticalHomogeneous.ofSmoothL2
#print axioms CriticalHomogeneous.ofSmoothL2_isHomogeneousSliceDatum
#print axioms chosenHomogeneousDatum
#print axioms chosenHomogeneousDatum_isDatum
#print axioms exists_isHomogeneousSliceDatum_of_smoothL2
#print axioms criticalVelocityHalf
#print axioms criticalVelocityThreeHalf
#print axioms criticalLaplacianHalf
#print axioms criticalAdvectionHalf
#print axioms criticalPressureHalf
#print axioms criticalForceHalf
#print axioms criticalVelocityHalf_isDatum
#print axioms criticalVelocityThreeHalf_isDatum
#print axioms criticalLaplacianHalf_isDatum
#print axioms criticalAdvectionHalf_isDatum
#print axioms criticalPressureHalf_isDatum
#print axioms criticalForceHalf_isDatum
#print axioms orderZeroDatum_angular_ae
#print axioms criticalVelocity_order_shift
#print axioms componentLp_laplacianField
#print axioms fourier_laplacianField_component_ae
#print axioms angular_laplacianField_component_ae
#print axioms criticalLaplacian_symbol
#print axioms criticalVelocity_transverse
#print axioms criticalPressure_longitudinal
#print axioms CriticalDatumInputs
#print axioms criticalDatumPath
#print axioms exists_criticalDatumPath
#print axioms rcritical1_of_classical

/-- The exact two-field fallback is inhabited by the genuine zero classical
solution with zero force. -/
theorem zeroCriticalDatumInputs : CriticalDatumInputs
    (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero := by
  let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
  change CriticalDatumInputs w A04.memForceR_zero
  have hchosen (s : ℝ) : chosenHomogeneousDatum s (0 : SpatialField) = 0 := by
    apply NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_unique
      (chosenHomogeneousDatum_isDatum
        ⟨0, isHomogeneousSliceDatum_zero s⟩)
      (isHomogeneousSliceDatum_zero s)
  have hvelocity : criticalVelocityHalf w = fun _ => 0 := by
    funext t
    rw [criticalVelocityHalf]
    change chosenHomogeneousDatum (1 / 2) (0 : SpatialField) = 0
    exact hchosen (1 / 2)
  refine ⟨?_, ?_⟩
  · rw [hvelocity]
    exact contDiffOn_const
  · intro t ht
    have hlap : criticalLaplacianHalf w t = 0 := by
      rw [criticalLaplacianHalf]
      rw [show (fun x => spatialLaplacian w.velocity t x) =
          (0 : SpatialField) by
        funext x
        simp [w, spatialLaplacian, spatialDerivative]]
      exact hchosen (1 / 2)
    have hadv : criticalAdvectionHalf w t = 0 := by
      rw [criticalAdvectionHalf]
      rw [show (fun x => advection w.velocity t x) = (0 : SpatialField) by
        funext x
        simp [w, advection, spatialDerivative]]
      exact hchosen (1 / 2)
    have hpressure : criticalPressureHalf w t = 0 := by
      rw [criticalPressureHalf]
      rw [show (fun x => pressureGradient w.pressure t x) = (0 : SpatialField) by
        funext x
        simp [w, pressureGradient]]
      exact hchosen (1 / 2)
    have hforce : criticalForceHalf (f := (0 : SpaceTimeField)) t = 0 := by
      rw [criticalForceHalf]
      change chosenHomogeneousDatum (1 / 2) (0 : SpatialField) = 0
      exact hchosen (1 / 2)
    rw [hvelocity, hlap, hadv, hpressure, hforce]
    simp

#print axioms zeroCriticalDatumInputs

example :
    let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
    Nonempty (CriticalDatumPath w A04.memForceR_zero) := by
  dsimp only
  exact exists_criticalDatumPath
    (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
    zeroCriticalDatumInputs

end NSFormalization.Section4.R43
