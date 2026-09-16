import NSFormalization.Section4.R43.Parseval
import NSFormalization.Section4.A04.ZeroSolution

/-! Lane 214: every named declaration is audited, followed by a genuine
zero-solution instance at the interior time `1 ∈ (0, 2)`. -/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace NSFormalization.Section4.R43

#print axioms homogeneous_slice_angular_ae
#print axioms angular_real_parseval
#print axioms component_real_pairing
#print axioms half_order_parseval
#print axioms pairing_identity_of_hcrit
#print axioms criticalAdvectionLpBridge_of_hcrit
#print axioms criticalTrilinearEstimate_of_hcrit'
#print axioms rcritical1_of_hcrit'

/-- Concrete zero-data realization of every field required by `hcrit`. -/
def zeroCriticalDatumPathParseval : CriticalDatumPath
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

#print axioms zeroCriticalDatumPathParseval

-- This consumes the constructed bridge, including its prescribed shifted
-- field; no independent zero bridge or trilinear assumption is supplied.
example :
    let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
    ∃ hcrit : CriticalDatumPath w A04.memForceR_zero,
      Nonempty (CriticalAdvectionLpBridge hcrit) ∧
        CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit ∧
          HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
            (criticalEnergyDerivative hcrit 1) 1 ∧
          criticalEnergyDerivative hcrit 1 / 2 +
              (1 - trilinearConst * criticalNormAt w.velocity 1) *
                criticalDissipationAt w.velocity 1 ^ 2
            ≤ criticalForceAt (0 : SpaceTimeField) 1 *
                criticalNormAt w.velocity 1 := by
  dsimp only
  have hcritical := rcritical1_of_hcrit' A04.memForceR_zero zeroCriticalDatumPathParseval
  exact ⟨zeroCriticalDatumPathParseval,
    ⟨criticalAdvectionLpBridge_of_hcrit zeroCriticalDatumPathParseval⟩,
    criticalTrilinearEstimate_of_hcrit' zeroCriticalDatumPathParseval,
    hcritical.1 1 (by norm_num), hcritical.2 1 (by norm_num)⟩

example :
    ⟪zeroCriticalDatumPathParseval.advectionHalf 1,
      zeroCriticalDatumPathParseval.velocityHalf 1⟫ =
      ∫ x : Space, inner ℝ
        (advection (NSFormalization.Section4.C01.lift
          (fun y => (A04.zeroSol 1 2 (by norm_num) (by norm_num)).velocity (1, y))) 0 x)
        ((criticalAdvectionLpBridge_shifted zeroCriticalDatumPathParseval 1
          (by norm_num)).lambda x) :=
  pairing_identity_of_hcrit zeroCriticalDatumPathParseval 1 (by norm_num)

end NSFormalization.Section4.R43
