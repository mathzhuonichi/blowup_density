import Contracts.V1.ConservativeForcing
import Contracts.V1.BoundaryInsertion

/-! Proposition 3.17, both branches. The bounded-domain branch covers every
nonempty bounded open set. The potential need only be smooth on a neighborhood
of `[0,T) × closure Ω`, using the registered closed-slab convention. No global
smoothness, boundary regularity or temporal support condition is assumed. -/
noncomputable section
namespace BlowupDensity.Contracts.V2.ConservativeForcing
open Set MeasureTheory
open NavierStokes.ProblemStatement
open V1.Data V1.BoundaryInsertion
open scoped ContDiff RealInnerProductSpace

/-- The negative spatial gradient on the domain. -/
def conservativeForceOmega (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- The two bounded-domain clauses of Proposition 3.17. -/
structure ConservativeForcingOmegaAPI : Prop where
  potential_pairing :
    ∀ (ν T : ℝ), 0 < T → ∀ (Ω : Set Space), IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty →
      ∀ φ : SpaceTimeScalar, SmoothOnClosedSlab (Ico 0 T) Ω φ →
        ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
          ∀ t ∈ Ico 0 T,
            (∫ x in Ω, inner ℝ (conservativeForceOmega φ (t, x)) (S.velocity (t, x))) = 0
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (Ω : Set Space), IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty →
        ∀ φ : SpaceTimeScalar, SmoothOnClosedSlab (Ico 0 T) Ω φ →
          ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
            ∀ t ∈ Ico 0 T, ∀ x ∈ Ω, S.velocity (t, x) = 0

/-- The retained torus API paired with the bounded no-slip API. -/
def conservativeForcingStatementV2 : Prop :=
  V1.ConservativeForcingAPI ∧ ConservativeForcingOmegaAPI

end BlowupDensity.Contracts.V2.ConservativeForcing
