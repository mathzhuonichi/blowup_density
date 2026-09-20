import Contracts.V1.Data
import Contracts.V1.Thresholds

/-!
# Draft A: Theorem 4.1 (`thm:Rmain`)

Independent statement draft from `paper/sections/04-whole-space.tex:7-14`.
This file deliberately imports only the registered data and threshold vocabulary.
It contains no proof and no dependency on an implementation of Theorem 4.1 or
Theorem 4.2.
-/

noncomputable section

namespace BlowupDensity.Research.R41.DraftA

open Set
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- **Needs registration.**  A bundled version of the manuscript's phrase
"a reference regular through `T`" (`02-preliminaries.tex:34-36`), with the
explicit positive extension margin and reference solution used by
`04-whole-space.tex:32`.

The registered proposition is retained explicitly, while the positive margin
and solution unpack its existential content so the approximation below can
refer to the particular reference velocity whose difference is measured. -/
structure RegularReferenceR (ν : ℝ) (a : SpatialField) (g : SpaceTimeField) (T : ℝ) where
  /-- `02-preliminaries.tex:34-36`, the reference is regular through `T`. -/
  regular_through : RegularThrough ν a g T
  /-- `04-whole-space.tex:32`, the extension margin `δ`. -/
  margin : ℝ
  /-- `04-whole-space.tex:32`, the hypothesis `δ > 0`. -/
  margin_pos : 0 < margin
  /-- `04-whole-space.tex:32`, `(v, π, g)` is a solution through `T + δ`. -/
  solution : ClassicalSolutionR ν a g (T + margin)

/-- **Needs registration.**  The single approximating family referred to in
the rider of Theorem 4.1 (`04-whole-space.tex:13`).  Its component assertions
are the corresponding conclusions of Theorem 4.2 at
`04-whole-space.tex:32-42`; keeping them in one structure records that all
conclusions concern the same forces and solutions.

The two convergence fields spell out the right-hand `ε → 0` limit using
positive radii, so no additional topology API is needed. -/
structure RegularReferenceApproximation
    (ν T : ℝ) (q : ℕ) (s : ℝ) (a : SpatialField) (g : SpaceTimeField)
    (reference : RegularReferenceR ν a g T) where
  /-- `04-whole-space.tex:32`, "for all sufficiently small `ε > 0`". -/
  epsilon0 : ℝ
  /-- `04-whole-space.tex:32`, the range of available positive insertion
  parameters is nonempty. -/
  epsilon0_pos : 0 < epsilon0
  /-- `04-whole-space.tex:32`, the approximating forces `g_ε`. -/
  force : {ε : ℝ // ε ∈ Ioc (0 : ℝ) epsilon0} → SpaceTimeField
  /-- `04-whole-space.tex:32`, the corresponding solutions `u_ε`, all with the
  original initial velocity `a`. -/
  solution : ∀ ε, ClassicalSolutionR ν a (force ε) T
  /-- `04-whole-space.tex:32`, every `g_ε` lies in `𝓕_R`. -/
  force_mem : ∀ ε, force ε ∈ forceClassR
  /-- `04-whole-space.tex:42`, `g_ε - g → 0` in
  `L^q(0,∞; H^s(ℝ³))`.  The quantifier order is radius, cutoff, then every
  positive insertion parameter below that cutoff. -/
  force_tends_to_reference :
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ η : ℝ, 0 < η ∧
        ∀ ε : {ε : ℝ // ε ∈ Ioc (0 : ℝ) epsilon0}, (ε : ℝ) < η →
        forceSobolevENorm (q : ℝ≥0∞) s (force ε - g) < r
  /-- `04-whole-space.tex:13`, "the same initial velocity".  This is explicit
  even though it also follows from the two `ClassicalSolutionR.initial`
  fields. -/
  same_initial_velocity :
    ∀ ε, ∀ x, (solution ε).velocity (0, x) = reference.solution.velocity (0, x)
  /-- `04-whole-space.tex:34` and `:13`, the inserted solution has singularity
  exactly at `T`, not merely breakdown by `T`. -/
  lifespan_exact :
    ∀ ε, maximalLifespanR ν a (force ε) = ENNReal.ofReal T
  /-- `04-whole-space.tex:36` and `:13`, the inserted and reference velocities
  have the same earlier history on `0 ≤ t ≤ T - 2 ε²`. -/
  same_earlier_history :
    ∀ ε : {ε : ℝ // ε ∈ Ioc (0 : ℝ) epsilon0},
      ∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * (ε : ℝ) ^ 2 →
      ∀ x, (solution ε).velocity (t, x) = reference.solution.velocity (t, x)
  /-- `04-whole-space.tex:13`, the velocity difference tends to zero in `E_T`.
  This is the qualitative consequence of the estimate at
  `04-whole-space.tex:39-40`, for the same family as every preceding field. -/
  velocity_tends_in_energy :
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ η : ℝ, 0 < η ∧
        ∀ ε : {ε : ℝ // ε ∈ Ioc (0 : ℝ) epsilon0}, (ε : ℝ) < η →
        energyENorm T ((solution ε).velocity - reference.solution.velocity) < r

/-- **Theorem 4.1** (`thm:Rmain`),
`paper/sections/04-whole-space.tex:7-14`: the two whole-space Sobolev
thresholds, followed by the threshold-value and regular-reference riders.

The zero-initial-velocity clause is one `↔` field because the manuscript states
one biconditional; splitting it would obscure that the density and obstruction
directions have exactly the same hypotheses. -/
structure RMainAPI where
  /-- Clause (i), `04-whole-space.tex:8-10`.  In manuscript order: fix
  `ν,T > 0`; choose `q ∈ {1,2}` and the topology order `s`; then for every fixed
  `a ∈ 𝓧_R`, subcriticality implies relative density in `𝓕_R`. -/
  fixed_initial_velocity_density :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder (q : ℝ) →
          ∀ a : SpatialField, a ∈ initialClassR →
            BreakdownDenseR ν a T (q : ℝ≥0∞) s
  /-- Clause (ii), `04-whole-space.tex:8-11`.  With zero initial velocity and
  all preceding fixed parameters unchanged, relative density holds if and only
  if `s < s_q`. -/
  zero_initial_velocity_density_iff :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ,
          RelativelyDense (q : ℝ≥0∞) s forceClassR (breakdownSetRZero ν T) ↔
            s < criticalOrder (q : ℝ)
  /-- `04-whole-space.tex:13`, "the thresholds are `1/2` for `L¹_tH^s_x` and
  `-1/2` for `L²_tH^s_x`".  This records the two values of the same
  `s_q = 2/q - 3/2` used in clauses (i) and (ii). -/
  threshold_values :
    criticalOrder 1 = (1 : ℝ) / 2 ∧ criticalOrder 2 = -(1 : ℝ) / 2
  /-- `04-whole-space.tex:13`, the regular-reference rider.  The common theorem
  parameters occur first; under the same subcritical hypothesis, every
  `a ∈ 𝓧_R`, `g ∈ 𝓕_R`, and reference regular through `T` has one approximating
  family carrying all the insertion, exact-lifespan, earlier-history, and
  energy conclusions. -/
  regular_reference_approximation :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ q : ℕ, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder (q : ℝ) →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassR →
              ∀ reference : RegularReferenceR ν a g T,
                RegularReferenceApproximation ν T q s a g reference

end BlowupDensity.Research.R41.DraftA
