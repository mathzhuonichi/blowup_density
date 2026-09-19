import NSFormalization.Section3.T24.Conservative
import NSFormalization.Section3.T24.PotentialPairing
import NSFormalization.Section3.T11.ExtendsBeyond

/-!
# T24c: conservative-forcing assembly

This module assembles the two proved clauses of `prop:conservative` in the
canonical T10/T11 vocabulary.  It also supplies a genuine solution witness for
the contract tests: zero velocity and zero pressure solve the equation from
rest for the zero potential on every positive horizon and at every viscosity.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-- Proposition `prop:conservative` (`paper/sections/03-torus.tex:723-740`) on
the torus, assembled from units Uc1 and Uc2. -/
structure ConservativeForcingAPI : Prop where
  potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0

/-- `03-torus.tex:723-740`: the statement form of `prop:conservative`. -/
def conservativeForcingStatement : Prop := ConservativeForcingAPI

/-- The canonical two-field conservative-forcing package. -/
theorem conservativeForcing : ConservativeForcingAPI where
  potential_pairing := potential_pairing
  zero_from_rest := zero_from_rest

/-- Zero velocity and zero pressure give a genuine classical solution from
rest for the zero potential, for arbitrary viscosity and positive horizon.

The Sobolev witness is reused from T11's established constant-velocity
solution; the momentum equation is checked directly because that reusable
solution is indexed at unit viscosity. -/
def restSolution (ν : ℝ) (T : ℝ) (hT : 0 < T) :
    ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT 0) T where
  velocity := 0
  pressure := 0
  horizon_pos := hT
  velocity_smooth := contDiff_const.contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  initial := fun _ ↦ rfl
  divergence := by
    intro t _ht x
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ht x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
      conservativeForceT, temporalDerivative, advection, spatialDerivative,
      spatialLaplacian, pressureGradient]
  sobolev :=
    (NSFormalization.Section3.T11.constantVelocitySolutionT (0 : Space) hT).sobolev
  pressure_gradient := by
    intro t _ht
    have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    exact memLp_const (0 : Space)
  velocity_periodic := fun _ _ _ _ ↦ rfl
  pressure_periodic := fun _ _ _ _ ↦ rfl
  pressure_gauge := by
    intro t _ht
    simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]

end NSFormalization.Section3.T24
