import NSFormalization.Section4.R43.CriticalPairing
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 175-R43-s1-pairing.  Every theorem below must
print exactly `[propext, Classical.choice, Quot.sound]`.

The final example constructs the complete `hcrit` carrier and `htri` estimate
for the genuine solution `A04.zeroSol : ClassicalSolutionR 1 0 0 2`, using
`A04.memForceR_zero`, and instantiates `rcritical1_of_trilinear` on the
explicit interior time `1 ∈ (0, 2)`.
-/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR)
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace NSFormalization.Section4.R43

#print axioms isHomogeneousSliceDatum_zero
#print axioms dotHomogeneousENorm_eq_of_isHomogeneousSlice
#print axioms criticalNormAt_eq_norm
#print axioms criticalDissipationAt_eq_norm
#print axioms criticalForceAt_eq_norm
#print axioms critical_laplacian_pairing
#print axioms critical_pressure_pairing
#print axioms critical_force_pairing
#print axioms criticalEnergyPath_eq
#print axioms criticalEnergyPath_hasDerivAt
#print axioms criticalNormAt_continuousOn
#print axioms criticalEnergyDerivative_hasDerivAt
#print axioms criticalLaplacianPairing_path
#print axioms criticalPressurePairing_path
#print axioms criticalForcePairing_path
#print axioms rcritical1_of_trilinear

/-- Concrete zero-data realization of every field required by `hcrit`. -/
def zeroCriticalDatumPath : CriticalDatumPath
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

example :
    let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
    ∃ hcrit : CriticalDatumPath w A04.memForceR_zero,
      CriticalTrilinearEstimate (C₀ := 1) hcrit ∧
        HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
          (criticalEnergyDerivative hcrit 1) 1 ∧
        criticalEnergyDerivative hcrit 1 / 2 +
            (1 - 1 * criticalNormAt w.velocity 1) *
              criticalDissipationAt w.velocity 1 ^ 2
          ≤ criticalForceAt (0 : SpaceTimeField) 1 *
              criticalNormAt w.velocity 1 := by
  dsimp only
  have htri : CriticalTrilinearEstimate (C₀ := 1) zeroCriticalDatumPath := by
      intro t ht
      simp [zeroCriticalDatumPath]
  have hcritical :=
    rcritical1_of_trilinear A04.memForceR_zero zeroCriticalDatumPath htri
  exact ⟨zeroCriticalDatumPath, htri,
    hcritical.1 1 (by norm_num), hcritical.2 1 (by norm_num)⟩

end NSFormalization.Section4.R43
