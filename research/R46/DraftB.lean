import Contracts.V1.Data
import Contracts.V1.InsertionFamily

/-!
Independent statement draft B for Proposition 4.6.
Sources: `04-whole-space.tex:218-272`, `02-preliminaries.tex:55-72`, and
registered contract vocabulary. No implementation or competing draft is used.
This file declares a specification type, not an inhabitant or a proof.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.REnergyDraftB

open Set Filter Topology
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- Proposition 4.6, `04-whole-space.tex:218-228`.
The density targets are completed datum paths, not smooth reference forces.
The last field existentially chooses ONE insertion family after the reference
and ball, and imposes both displayed limits on that family. -/
structure REnergyAPI where
  /-- `04-whole-space.tex:219`, first density assertion.
  Quantifiers: datum, positive viscosity and horizon, q in {1,2}, s < s_q;
  then every completed target and every positive radius (inside the predicate).
  The realization is explicitly the inhomogeneous `IsSobolevPath s`. -/
  sobolevDensity :
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
      s < 2 / q.toReal - 3 / 2 →
        CompletedDenseVia q s (IsSobolevPath s)
          (breakdownSetIn forceClassCompact ν a T)

  /-- `04-whole-space.tex:219`, second density assertion; realization fixed
  by `02-preliminaries.tex:58-72`: Fourier transform = |ξ| times the L² datum.
  Same smooth compact breakdown set; the target ranges over the full completed
  L² time space. No condition on an arbitrary rough target's lifespan. -/
  homogeneousDensity :
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      CompletedDenseVia 2 (-1) (IsHomogeneousPath (-1))
        (breakdownSetIn forceClassCompact ν a T)

  /-- `04-whole-space.tex:221-228`, both limits simultaneously, for every
  reference of Theorem 4.2 (`:31-43`) and every nonempty open ball.
  The carried `InsertionFamilyAPI` retains `energyRate`, `forceConvergence`,
  localization, history and blowup on this same family. Its missing classical
  solution and lifespan conclusions are stated explicitly here, not assumed
  via an unregistered API. A smaller internal margin is allowed.

  Strong closure means `energyENorm T (u_ε - v) → 0` on (0,T), not pointwise
  convergence or continuation at T. The sum of the THREE force norms tends
  to zero on (0,∞). At H⁰ we use the registered Sobolev norm for L²_x, exactly
  the q=1,s=0 reuse described in `:271`. The homogeneous norm is only applied
  to the compact difference; no homogeneous membership of g is imposed. -/
  strongTrajectoryClosure :
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ δ : ℝ, 0 < δ → RegularThrough ν a g (T + δ) →
    ∀ R : ClassicalSolutionR ν a g (T + δ),
    ∀ x₀ : Space, ∀ r : ℝ, 0 < r →
      ∃ P : PacketAPI ν, ∃ A : InsertionFamilyAPI ν P,
        A.a = a ∧ A.scaling.correction.T = T ∧
        A.scaling.correction.g = g ∧
        A.scaling.correction.v = R.velocity ∧
        A.scaling.correction.π = R.pressure ∧
        A.scaling.correction.x₀ = x₀ ∧ A.scaling.correction.r = r ∧
        (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
          MemForceR (A.force ε) ∧
          maximalLifespanR ν a (A.force ε) = ENNReal.ofReal T ∧
          ∃ U : ClassicalSolutionR ν a (A.force ε) T,
            U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
        Tendsto (fun ε : ℝ => energyENorm T
          (fun z => A.velocity ε z - R.velocity z)) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun ε : ℝ =>
          forceSobolevENorm 1 0 (fun z => A.force ε z - g z) +
          forceSobolevENorm 2 (-1) (fun z => A.force ε z - g z) +
          forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
          (𝓝[>] 0) (𝓝 0)

end BlowupDensity.Contracts.V1.REnergyDraftB
