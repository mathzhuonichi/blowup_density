import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureGauge
import NSFormalization.Section4.C01.EnstrophyIdentityRaw

/-! # Manuscript regularity on the constructor horizon -/

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02
  (ClassicalSolutionR SpatialField SpaceTimeField PressureGaugeEquivOn IsSolenoidal)
open RadialPotential (HasSymmetricJacobian pressurePotential)
open scoped ContDiff

/-- The momentum equation in the manuscript's tensor-divergence notation. -/
theorem projected_of_classicalSolution {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f S) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      temporalDerivative w.velocity t x + ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergence w.velocity t x) -
          pressureGradient w.pressure t x := by
  intro t ht x
  exact (navierStokesResidual_eq_iff_projected ν w.velocity w.pressure t x (f (t, x))
    ((D01.contDiff_slice w.velocity_smooth ⟨ht.1.le, ht.2⟩).differentiable (by simp) x)
    (w.divergence t ⟨ht.1.le, ht.2⟩ x)).mp (w.momentum t ht x)


end NSFormalization.Section4.A01
