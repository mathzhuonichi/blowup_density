import Contracts.V1.Data

/-! Stable specification for the **uniqueness** half of A02's local theory.

Task `collaboration/tasks/A02.md`, graph node `A02`
(`formalization/blueprint/DEPENDENCY_GRAPH.md`, `A02 ← A01`; consumers
`A02 → A04`, `A02 → C01`, `A02 → R42`).  `prop:local` (= `lem:Rlocal`,
`paper/sections/02-preliminaries.tex:105`) asserts local existence, uniqueness
and continuation; A01 owns existence and A04 the continuation criterion, and A02
owns the middle third.  The manuscript derives the uniqueness clause from the
displayed energy estimate at `paper/sections/appendix-a-local-theory.tex:115-125`:
if `z = u₁ − u₂` for two classical solutions with the same data then
`½(‖z‖₂²)' + ν‖∇z‖₂² ≤ ‖∇u₂‖_∞‖z‖₂²` (`:119-120`), the coefficient `‖∇u₂‖_∞` is
finite on compact common intervals since `u₂ ∈ C_tH³` (`:122-123`), and Grönwall
gives uniqueness (`:123`).  The scalar pressure is "determined up to a function
of time" (`paper/sections/02-preliminaries.tex:31`); applied to the difference of
two solutions this is the pressure clause.

This version-one record fixes exactly those two clauses, in the vocabulary of
`Contracts/V1/Data.lean`.  They are the two fields of the accepted draft
`research/A02/Spec.lean:263-281` `UniquenessAPI`, discharged by the merged proof
modules `formalization/NSFormalization/Section4/A02/{Energy,Bounds,Uniqueness}.lean`
(lanes 033/049/052): `velocity_unique` and `pressure_gauge` of
`Section4/A02/Uniqueness.lean`, stated on the A02-local restatement of the
solution class.

## Consumers

* **A04** (continuation criterion, `DEPENDENCY_GRAPH.md:205-209`): the restarted
  local solution is identified with the original on the overlap by
  `velocity_unique`.
* **R42** (`thm:Rinsert`): "Proposition 2.1 identifies the solution with the
  unique maximal solution" (`04-whole-space.tex:53`) rests on both clauses.
* **C01** (energy identities): the identities are computed along *the* solution,
  which uniqueness makes well defined.

## Out of scope: the rest of `MaximalSolutionAPI`

`research/A02/Spec.lean` bundles uniqueness with the maximal-lifespan interface
`MaximalSolutionAPI`.  Only the `UniquenessAPI` half is registered here.  Not
included, and each owed by a later lane: the A01 interface fields (`horizon`,
`localSolution`, `horizonLowerBound`); the order-theoretic clauses
(`maximalLifespanR` characterizations `lifespan_le_iff`,
`lifespan_le_iff_no_extension`, `lifespan_ge_of_forall_shorter`,
`regularThrough_iff`, `referenceLifespan`, `horizon_le_lifespan`); patching and
restriction (`patch`, `restrict`); the canonical pressure gauge
(`pressure_normalization`); the existence and uniqueness of the maximal solution
(`IsMaximalSolution`, `exists_maximal`, `maximal_unique`); the quantitative
restart (`restart`, `restart_datum`, `restart_force`); and Theorem 4.2's
identification (`lifespan_le_of_unbounded`, `insertion_lifespan_eq`).  Nothing
below asserts `eq:mild`, the continuation criterion `eq:criterion`, or any
smallness, common-horizon, compact-support or `p ∈ L²` side condition; the
Grönwall coefficient's finiteness (`eq:Rproduct`'s `‖z‖_∞ ≤ C‖z‖_{H²}`, the edge
`A03 → A02` of `research/A02/COMPARISON.md` §5) is a step of the discharging
proof, not a field.

## The narrowing to `F_R`, recorded deliberately

`prop:local` quantifies over "each force smooth into every `H^m` on compact time
intervals" (`02-preliminaries.tex:107-109`); `MemForceR` (`Data.lean:544`)
additionally demands the `L¹_t`/`L²_t` finiteness of `eq:Rclasses` at every
order, so both fields are stated on the strictly smaller class
`F_c ⊆ F_rd ⊆ F_R` Section 4 quantifies over (`04-whole-space.tex:183-192`).  A
consumer needing the wider hypothesis must widen these fields.  The initial class
`initialClassR` is the manuscript's `X_R` verbatim (`02-preliminaries.tex:12`).
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.Uniqueness

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data

/-- **The uniqueness half of `prop:local` on `R³`**
(`paper/sections/02-preliminaries.tex:105`, "a unique maximal smooth velocity,
with pressure determined as above"), derived at
`paper/sections/appendix-a-local-theory.tex:115-125`.

Two classical solutions of the *same* whole-space datum `(ν,a,f)` on horizons
`T₁` and `T₂` have the same velocity on the common interval `[0, min(T₁,T₂))`,
and their pressures differ there by a function of time only.  Types copied
verbatim from `research/A02/Spec.lean:267-281`. -/
structure UniquenessAPI where
  /-- `appendix-a-local-theory.tex:119-124`: equal data give equal velocities on
  the common interval.  `Ico 0 (min T₁ T₂)` is the intersection of the two
  half-open intervals of definition, including the initial time. -/
  velocity_unique : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
          u₁.velocity (t, x) = u₂.velocity (t, x)
  /-- `02-preliminaries.tex:31,105` "with pressure determined as above":
  the two pressures agree up to the gauge freedom `p ∼ p + κ(t)` on the same
  common interval.  `PressureGaugeEquivOn` (`Data.lean:589`) is exactly that
  relation. -/
  pressure_gauge : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure

end BlowupDensity.Contracts.V1.Uniqueness
