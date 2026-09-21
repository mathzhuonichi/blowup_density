import NSFormalization.Section3.T11.EnergyIdentity
import NSFormalization.Section3.T20.H1Energy
import NSFormalization.Section4.A04.EnstrophyInequality

/-!
# P21 Route B, B2: periodic inhomogeneous enstrophy

The revised article, `paper/revised/sections/02-preliminaries.tex:149–156`,
states: “For each initial velocity in the stated class and each force smooth into
every $H^m$ on compact time intervals” there is a unique maximal smooth velocity,
and “then it extends smoothly beyond $S$” under the squared H² integral criterion.
Lines 165–168 explicitly retain nonzero periodic mean through mean reduction.
This module concerns the separate H¹-uniform restart obligation.

The periodic Fourier weight is 1+|2πk|²: the physical gradient weight is one,
unlike the whole-space convention of B1. No smallness estimate is used.
-/

noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal

/-- Differentiated full H¹ energy, retaining the zero Fourier mode.
The pairings here are H¹ pairings, before spatial integration by parts. -/
theorem inhomogeneousEnergyIdentityT
    {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : f ∈ forceClassT)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G F N : PeriodicSobolev 1}
    (hG : IsPeriodicDatum 1 (fun x ↦ w.velocity (t, x)) G)
    (hF : IsPeriodicDatum 1 (fun x ↦ f (t, x)) F)
    (hN : IsPeriodicDatum 1 (fun x ↦ convectionFieldT w.velocity (t, x)) N) :
    HasDerivAt
      (fun s ↦ (periodicSobolevENorm 1 (fun x ↦ w.velocity (s, x))).toReal ^ 2)
      (-2 * ν * torusGradientNormAt 1 w.velocity t ^ 2 +
        2 * torusRealPairing G F - 2 * torusRealPairing G N) t := by
  convert
    (energyIdentity_of_classical w hf.1 1 ht (Gm := G) (Fm := F) (Nm := N)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hG)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hF)
      (by simpa only [IsPeriodicDatum, Nat.cast_one] using hN)) using 1 <;>
    norm_num [torusSobolevNormAt, torusRealPairing]

/-- Haar Hölder with velocity in L⁶, gradient in L³, Laplacian in L². -/
theorem lintegral_convection_holder_632T (z : SpatialField) (hz : SmoothPeriodicT z) :
    ∫⁻ y, ‖torusLift
      (fun x ↦ (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) y‖ₑ
        ∂periodicTorusMeasure ≤
      periodicLpENorm 6 z * periodicLpENorm 3 (gradientTensor z) *
        periodicLpENorm 2 (laplacian z) := by
  have h := T20.lintegral_enorm_mul_three_le_torus_three_six_two
    (T20.aestronglyMeasurable_torusLiftH1 (T20.continuous_gradientTensorH1 hz.1))
    (T20.aestronglyMeasurable_torusLiftH1 hz.1.continuous)
    (T20.aestronglyMeasurable_torusLiftH1 (contDiff_laplacian hz.1).continuous)
  have hp : ∀ y : PeriodicTorus,
      ‖torusLift (fun x ↦ (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)) y‖ₑ ≤
        ‖torusLift (gradientTensor z) y‖ₑ * ‖torusLift z y‖ₑ *
          ‖torusLift (laplacian z) y‖ₑ := by
    intro y
    simpa only [torusLift, NSFormalization.Paper1.torusLift, mul_comm] using T20.enorm_inner_advection_leH1 z (laplacian z)
      (NavierStokes.PeriodicIntegration.toSpace
        ((UnitAddTorus.measurableEquivPiIoc (0 : NavierStokes.PeriodicIntegration.Coords) y).val))
  exact (lintegral_mono hp).trans (by simpa only [periodicLpENorm, mul_comm] using h)

end NSFormalization.Section3.T11

