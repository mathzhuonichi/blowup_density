import NSFormalization.Paper1.PeriodicDensityDichotomy

/-!
# Explicit unforced local flows for constant periodic data

The arbitrary-data local existence premise in `PeriodicDensityDichotomy` is kept
explicit.  This module supplies a genuine, premise-free slice of that premise:
for every constant divergence-free datum the constant velocity and zero pressure
solve the unforced periodic equation on every positive horizon.  It also feeds
that concrete witness into the density dichotomy.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicConstantLocal

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicDensityDichotomy
open scoped ContDiff ENNReal

/-- A spatially constant velocity with zero pressure is an unforced flow on
any positive time horizon.  No local-existence theorem is used here: every
term in the residual is identically zero. -/
def constantUnforcedFlow (ν : ℝ) (c : Space) {S : ℝ} (hS : 0 < S) :
    Flow ν (fun _ => c) (0 : VelocityField) S where
  velocity := fun _ => c
  pressure := fun _ => 0
  horizon_pos := hS
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  velocity_periodic := fun _ _ _ _ => rfl
  pressure_periodic := fun _ _ _ _ => rfl
  initial := fun _ => rfl
  divergence := by
    intro t ht x
    simp [spatialDivergence, spatialDerivative]
  equation := by
    intro t ht x
    simp [Source.residual, temporalDerivative, advection, spatialLaplacian,
      spatialDerivative, pressureGradient]

/-- Constant data have an unforced flow on every prescribed positive horizon. -/
theorem constant_unforced_flow_on (ν : ℝ) (c : Space) {S : ℝ} (hS : 0 < S) :
    Nonempty (Flow ν (fun _ => c) (0 : VelocityField) S) :=
  ⟨constantUnforcedFlow ν c hS⟩

/-- The explicit constant-data witness instantiates the local-flow branch of
the density argument. -/
theorem exists_nearby_singular_force_of_constant_data
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {c : Space} {g : VelocityField} (hg : IsTestForce g)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ S : ℝ, Nonempty (Flow ν (fun _ => c) G S)) ∧
      0 < lifespan ν (fun _ => c) G ∧
      lifespan ν (fun _ => c) G ≤ ENNReal.ofReal T := by
  exact exists_nearby_singular_force_of_unforced_localFlow hν hT hs
    (constantUnforcedFlow ν c zero_lt_one) hg hρ

/-- Every constant initial datum satisfies the `UnforcedLocalExistence`
interface on its singleton slice.  This records exactly what is proved here;
the extension to arbitrary periodic data remains a separate bridge. -/
def ConstantUnforcedLocalExistence (ν : ℝ) : Prop :=
  ∀ c : Space, ∀ S : ℝ, 0 < S →
    Nonempty (Flow ν (fun _ => c) (0 : VelocityField) S)

theorem constantUnforcedLocalExistence (ν : ℝ) :
    ConstantUnforcedLocalExistence ν := by
  intro c S hS
  exact constant_unforced_flow_on ν c hS

end NSFormalization.Paper1.PeriodicConstantLocal
