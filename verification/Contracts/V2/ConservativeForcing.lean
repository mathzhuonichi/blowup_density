import Contracts.V1.ConservativeForcing
import Contracts.V1.BoundaryInsertion

/-! Proposition 3.17, both branches. The domain potential is globally smooth;
no periodicity or compact temporal support is assumed. Domain types are the
registered V1 boundary vocabulary. -/
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
    ∀ (ν T : ℝ), 0 < T → ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
      ∀ φ : SpaceTimeScalar, ContDiff ℝ ∞ φ →
        ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
          ∀ t ∈ Ico 0 T,
            (∫ x in Ω, inner ℝ (conservativeForceOmega φ (t, x)) (S.velocity (t, x))) = 0
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
        ∀ φ : SpaceTimeScalar, ContDiff ℝ ∞ φ →
          ∀ S : ClassicalSolutionOmega ν Ω 0 (conservativeForceOmega φ) T,
            ∀ t ∈ Ico 0 T, ∀ x ∈ Ω, S.velocity (t, x) = 0

/-- The retained torus API paired with the bounded no-slip API. -/
def conservativeForcingStatementV2 : Prop :=
  V1.ConservativeForcingAPI ∧ ConservativeForcingOmegaAPI

end BlowupDensity.Contracts.V2.ConservativeForcing
