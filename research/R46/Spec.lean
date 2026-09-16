import Contracts.V1.InsertionFamily

/-!
# R46 reconciled specification: Proposition 4.6 (`prop:Renergy`)

This is the statement-only reconciliation of the two blind drafts against
`paper/sections/04-whole-space.tex:218-229`.  It has exactly the three fields
selected in `research/R46/RECONCILIATION.md`: completed inhomogeneous density,
completed homogeneous density, and strong trajectory closure for one inserted
family.  All mathematical notions are registered contract vocabulary; there is
no local proposition wrapper and no implementation import.

The first two fields use the registered abbreviations `CompletedDense` and
`CompletedDenseHomogeneous`.  The two `example ... := rfl` declarations below
pin the reconciliation's claim that these are definitionally the corresponding
`CompletedDenseVia` predicates.

The strong-closure field uses raw manuscript data rather than taking a packet or
scaling record as an input.  Its order is exactly

    a, a ∈ X_R, ν, 0 < ν, T, 0 < T, g, g ∈ F_R, δ, 0 < δ, R,
      ∃ P, ∃ A, ...

The explicit `R : ClassicalSolutionR ν a g (T + δ)` is the reference regular
through the stated horizon; the redundant `RegularThrough` premise is omitted.
The insertion ball is internal to `A.scaling` and is not quantified or pinned,
because Proposition 4.6 does not mention it.  The exact lifespan and classical
solution clauses are retained so that “inserted solutions” cannot be witnessed
by arbitrary trajectories.
-/

noncomputable section

namespace BlowupDensity.R46.Draft

open Set Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## Definitional checks for the registered density abbreviations -/

/-- `CompletedDense` is exactly the inhomogeneous realization of
`CompletedDenseVia`; this is definitional, as required by the R46
reconciliation. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S =
      CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- `CompletedDenseHomogeneous` is exactly the homogeneous realization of
`CompletedDenseVia`; this is definitional, as required by the R46
reconciliation. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-! ## Proposition 4.6 -/

/-- **Proposition 4.6** (`prop:Renergy`),
`paper/sections/04-whole-space.tex:218-229`: finite-lifespan smooth compact
forces are dense in the specified full completed Bochner spaces, and every
Theorem 4.2 reference admits one inserted family on which the energy trajectory
and all three displayed force distances converge to zero simultaneously.

This structure is a specification only.  Each field is a fully spelled-out
statement over registered data; no field is an abstract `Prop` placeholder. -/
structure REnergyAPI where
  /-- First density assertion, `paper/sections/04-whole-space.tex:218-219`.

  Exact quantifier order:
  `∀ a, a ∈ X_R → ∀ ν, 0 < ν → ∀ T, 0 < T → ∀ q, q ∈ {1,2} →
  ∀ s, s < s_q → density`.  Here `q : ℝ≥0∞`, membership in `{1,2}` is written
  `(q = 1 ∨ q = 2)`, and `s_q` is the registered
  `criticalOrder q.toReal`.  The dense set is precisely the smooth compact
  force set whose registered maximal lifespan is at most `T`.

  Non-vacuity: `CompletedDense` expands to quantification over every
  `MemBochnerDatum` target and every strictly positive `ℝ≥0∞` radius, followed
  by an actual force in `breakdownSetIn forceClassCompact ν a T`; the distance
  is the fail-safe `ℝ≥0∞` Bochner norm, never a `.toReal` value. -/
  completedSobolevDensity :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
            ∀ s : ℝ, s < criticalOrder q.toReal →
              CompletedDense q s
                (breakdownSetIn forceClassCompact ν a T)

  /-- Homogeneous density assertion, `paper/sections/04-whole-space.tex:219`.

  Exact quantifier order:
  `∀ a, a ∈ X_R → ∀ ν, 0 < ν → ∀ T, 0 < T → density`.  The exponent and order
  are fixed at `q = 2`, `s = -1`; only the realization changes to the registered
  `IsHomogeneousPath (-1)`.  The approximating set is the same
  `breakdownSetIn forceClassCompact ν a T` as in the first field.

  Non-vacuity: `CompletedDenseHomogeneous` again ranges over every finite,
  strongly measurable completed datum and every positive radius, and demands an
  actual smooth compact finite-lifespan force.  The realization predicate is
  homogeneous, so this is not definitionally the inhomogeneous `H⁻¹` clause. -/
  completedHomogeneousDensity :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          CompletedDenseHomogeneous 2 (-1)
            (breakdownSetIn forceClassCompact ν a T)

  /-- Simultaneous strong closure, `paper/sections/04-whole-space.tex:221-228`,
  for every raw-data reference of Theorem 4.2 (`04-whole-space.tex:31-43`).

  Exact quantifier order:
  `∀ a, a ∈ X_R → ∀ ν, 0 < ν → ∀ T, 0 < T → ∀ g, g ∈ F_R →
  ∀ δ, 0 < δ → ∀ R : ClassicalSolutionR ν a g (T+δ), ∃ P, ∃ A`.
  The one family `A` is then pinned to `a`, `T`, `g`, `R.velocity`, and
  `R.pressure`.  For every `ε ∈ (0,A.ε₀]`, its force lies in `F_R`, its maximal
  lifespan is exactly `T`, and its velocity/pressure are carried by a
  full-horizon `ClassicalSolutionR`.  The same `A` witnesses both the
  `E_T` limit at `04-whole-space.tex:223` and the single summed three-norm limit
  at `:224-226`.  In accord with `:228`, the homogeneous norm is applied only
  to `A.force ε - g`, never to the background `g` itself.

  Non-vacuity: `InsertionFamilyAPI.eps_pos` makes `(0,A.ε₀]` nonempty; the
  per-`ε` conjunction requires registered forces, an exact finite lifespan, and
  genuine classical solutions rather than unconstrained fields.  Both limits
  are in `ℝ≥0∞`-valued norms along the nontrivial right-hand filter `𝓝[>] 0`,
  and both belong to the same existential family, so simultaneity cannot be
  discharged by choosing unrelated approximants. -/
  strongTrajectoryClosure :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ g : SpaceTimeField, MemForceR g →
            ∀ δ : ℝ, 0 < δ →
              ∀ R : ClassicalSolutionR ν a g (T + δ),
                ∃ (P : PacketAPI ν) (A : InsertionFamilyAPI ν P),
                  A.a = a ∧
                  A.scaling.correction.T = T ∧
                  A.scaling.correction.g = g ∧
                  A.scaling.correction.v = R.velocity ∧
                  A.scaling.correction.π = R.pressure ∧
                  (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
                    MemForceR (A.force ε) ∧
                    maximalLifespanR ν a (A.force ε) = ENNReal.ofReal T ∧
                    ∃ U : ClassicalSolutionR ν a (A.force ε) T,
                      U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
                  Tendsto (fun ε : ℝ => energyENorm T
                    (fun z => A.velocity ε z - R.velocity z))
                    (𝓝[>] 0) (𝓝 0) ∧
                  Tendsto (fun ε : ℝ =>
                    forceSobolevENorm 1 0 (fun z => A.force ε z - g z) +
                    forceSobolevENorm 2 (-1) (fun z => A.force ε z - g z) +
                    forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
                    (𝓝[>] 0) (𝓝 0)

end BlowupDensity.R46.Draft
