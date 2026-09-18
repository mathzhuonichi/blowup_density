import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A04.ForceShift

/-!
# T11 canonical periodic local-theory vocabulary

This definitions-only module realizes the vocabulary introduced before and
between the five API structures in `research/T11/Spec.lean`.  The T10 data and
solution vocabulary is imported from its canonical module.  Tensor divergence
and positive-time translation are reducible aliases of their token-identical
local Section 4 sources; the other declarations use torus-specific vocabulary
and retain the specification bodies.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators

/-! ## Local solution and continuation vocabulary -/

/-- An order-`s` Fourier datum path for a physical field on a specified time set. -/
def IsPeriodicSobolevPathOn (s : ℝ) (I : Set ℝ) (u : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t ∈ I, IsPeriodicDatum s (fun x ↦ u (t, x)) (G t)

/-- The tensor divergence, reused from its local Section 4 canonical source. -/
abbrev convectionDivergenceT (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  NSFormalization.Section4.A01.convectionDivergence u t x

/-- The scalar spatial Laplacian of a periodic pressure field. -/
def scalarSpatialLaplacianT (p : SpaceTimeScalar) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y : Space ↦
        fderiv ℝ (fun z : Space ↦ p (t, z)) y (coordinateVector i))
      x (coordinateVector i)

/-- One velocity-pressure pair solves on every strictly shorter positive horizon. -/
def SolvesBelowT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionT ν a f b, w.velocity = u ∧ w.pressure = p

/-- A common pair realizes every positive horizon below the maximal lifespan. -/
def IsMaximalPeriodicSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanT ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanT ν a f →
      ∃ w : ClassicalSolutionT ν a f S, w.velocity = u ∧ w.pressure = p

/-- The squared periodic `H²` continuation lintegral. -/
def squaredHTwoIntegralT (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    periodicSobolevENorm 2 (fun x ↦ u (t, x)) ^ 2

/-- Positive-time translation, reused from its local Section 4 canonical source. -/
abbrev timeShiftT (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  NSFormalization.Section4.A04.timeShift t₀ f

/-- Concrete strict extension of common fields solving below `S`. -/
def ExtendsBeyondT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT ν a f (S + δ),
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.velocity (t, x) = u (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.pressure (t, x) = p (t, x))

/-! ## Local regularity vocabulary consumed by all four public APIs -/

/-- The three nonredundant regularity clauses on one periodic classical solution. -/
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionT ν a f T) : Prop where
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) w.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  pressure_poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence
          (fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2) t x
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
      (f (t, x) - convectionDivergenceT w.velocity t x) -
        pressureGradient w.pressure t x

/-! ## Data-defined Galilean mean reduction -/

/-- The normalized spatial mean of a velocity slice. -/
def velocityMeanT (u : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ u (t, x))

/-- The normalized spatial mean of a force slice. -/
def forceMeanT (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ f (t, x))

/-- The data-defined mean trajectory `m(t)`. -/
def galileanMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, forceMeanT f r

/-- The data-defined displacement `X(t)`. -/
def galileanShiftT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  ∫ r in (0 : ℝ)..t, galileanMeanT a f r

/-- The Galilean-transformed velocity. -/
def galileanVelocityT (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ u (z.1, z.2 + galileanShiftT a f z.1) - galileanMeanT a f z.1

/-- The Galilean-transformed mean-zero force. -/
def galileanForceT (a : SpatialField) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1, z.2 + galileanShiftT a f z.1) - forceMeanT f z.1

/-- Pressure transported by the data-defined Galilean translation. -/
def galileanPressureT (a : SpatialField) (f : SpaceTimeField)
    (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p (z.1, z.2 + galileanShiftT a f z.1)

/-! ## Positive-viscosity rescaling -/

/-- The unit-viscosity initial datum. -/
def unitViscosityInitialT (ν : ℝ) (a : SpatialField) : SpatialField :=
  fun x ↦ ν⁻¹ • a x

/-- The unit-viscosity velocity. -/
def unitViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν⁻¹ • u (z.1 / ν, z.2)

/-- The unit-viscosity pressure. -/
def unitViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ (ν ^ 2)⁻¹ * p (z.1 / ν, z.2)

/-- The unit-viscosity force. -/
def unitViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ (ν ^ 2)⁻¹ • f (z.1 / ν, z.2)

/-- Restore the original viscosity in a velocity field. -/
def restoreViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν • u (ν * z.1, z.2)

/-- Restore the original viscosity in a pressure field. -/
def restoreViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ν ^ 2 * p (ν * z.1, z.2)

/-- Restore the original viscosity in a force field. -/
def restoreViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν ^ 2 • f (ν * z.1, z.2)

end NSFormalization.Section3.T11
