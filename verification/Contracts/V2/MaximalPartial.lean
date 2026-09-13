import Contracts.V1.MaximalPartial

/-! Version 2 of the **proved part of A02's maximal-solution interface**: the
version-one record `MaximalPartialAPI` (`Contracts/V1/MaximalPartial.lean`),
extended by the two maximal-solution fields of lane 064 (unit **U7**).

Task `collaboration/tasks/A02.md`, graph node `A02`
(`formalization/blueprint/DEPENDENCY_GRAPH.md`, `A02 ← A01`; consumers
`A02 → A04`, `A02 → C01`, `A02 → R42`).  `research/A02/Spec.lean` bundles the whole
obligation as `MaximalSolutionAPI`; version one registered ten of its fields plus
the carried `A02.uniqueness`.  Version two adds the two remaining
maximal-solution fields, discharged by the merged proof module
`formalization/NSFormalization/Section4/A02/Maximal.lean` (lane 064).

## Why a new version

`Contracts.V1.MaximalPartial` deliberately stops short of the maximal solution
itself: its module docstring lists `exists_maximal`, `maximal_unique` and the
predicate `IsMaximalSolution` they rest on among the excluded fields, "because
not yet proved on this branch".  Lane 064's `Section4/A02/Maximal.lean`
discharges exactly those two fields (`exists_maximal_of_localSolution` and
`maximal_unique`), so version two records them.

## What changed, exactly

`MaximalPartialV2API` extends `Contracts.V1.MaximalPartial.MaximalPartialAPI`
unchanged and adds **two** fields:

* `exists_maximal` (`research/A02/Spec.lean:421-423`; `02-preliminaries.tex:105`,
  "has a unique maximal smooth velocity"): existence of one velocity `u` and one
  pressure `p` that are, *literally*, the fields of a classical solution on
  `[0,S)` for every `S` below `T^ν_{max,R}` — i.e. `IsMaximalSolution ν a f u p`.
  Stated **with the A01 `localSolution` clause as an explicit hypothesis**, in
  the same shape as version one's `horizon_le_lifespan`: `Section4/A02/Maximal.lean`
  proves it as `exists_maximal_of_localSolution`, and A01 will discharge the
  hypothesis by `LocalTheoryAPI.solution`.  The A01 clause is genuinely used —
  it is what makes `0 < maximalLifespanR`.
* `maximal_unique` (`research/A02/Spec.lean:429-434`; `02-preliminaries.tex:105`,
  the word "unique"): any two maximal solutions of one datum agree in velocity at
  every presingular time and have gauge-equivalent pressures there.  Stated
  **verbatim** (no A01 hypothesis: the two `IsMaximalSolution` hypotheses already
  supply the solutions), discharged by `Section4/A02/Maximal.lean` `maximal_unique`.

No version-one field is removed, weakened, renamed or restated; `extends` makes
that structural.  `Bindings.maximalPartial_of_v2` exports the version-one record,
and `Tests.checkedMaximalPartial` keeps running against the untouched
`Bindings.maximalPartial`.

## The two objects `Data.lean` does not define, restated verbatim

`IsMaximalSolution` and `presingularTimes` are `⟪D01:IsMaximalSolution⟫`
(`research/section4/STATEMENTS.md:1198`) and the positive-time half of the
maximal-lifespan interval `[0,T^ν_{max,R})` (`02-preliminaries.tex:32`), which
`Contracts/V1/Data.lean` does not define and the two new fields are stated over.
They are restated **token-for-token** from `research/A02/Spec.lean:168-169,210-214`
in the vocabulary of `Contracts.V1.Data` (`maximalLifespanR`, `ClassicalSolutionR`).
`formalization/NSFormalization/Section4/A02/Maximal.lean` carries a byte-identical
copy on the A02-local solution class; because both rest on `maximalLifespanR`,
which quantifies over the solution class, they do **not** bridge to the A02 copies
by `rfl` (unlike version one's `limsupLeft`/`speedENorm`) — the propositional
transports live in `verification/Bindings/MaximalPartialV2.lean`.

## Out of scope: the rest of `MaximalSolutionAPI`, each owed by a later lane

Not included, because not yet proved on this branch:

* the restated **A01 interface fields** `horizon`, `localSolution`,
  `horizonLowerBound` (`Spec.lean:316-332`) — A01's obligation;
* the quantitative restart `restart`, `restart_datum`, `restart_force`
  (`Spec.lean:512-558`);
* Theorem 4.2's packaged identification `insertion_lifespan_eq`
  (`Spec.lean:609-626`).

Nothing here asserts `eq:mild`, the continuation criterion `eq:criterion` (A04),
or any smallness, common-horizon, compact-support or `p ∈ L²` side condition.

This module introduces two definitions and one structure and proves nothing. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.MaximalPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## The two objects `Data.lean` does not define, restated verbatim from `Spec.lean` -/

/-- `research/A02/Spec.lean:168-169`, `02-preliminaries.tex:32`: the times
strictly before the maximal classical lifespan, `[0, T^ν_{max,R}(a,f))` read
inside `ℝ`.  `maximalLifespanR` is `ℝ≥0∞`-valued, so the comparison is made after
`ENNReal.ofReal`; strictness is the right condition (`Spec.lean:161-167`).
Restated token-for-token in `Contracts.V1.Data` vocabulary; used by
`maximal_unique`. -/
def presingularTimes (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < maximalLifespanR ν a f}

/-- `research/A02/Spec.lean:210-214`, `⟪D01:IsMaximalSolution⟫`
(`02-preliminaries.tex:32,105`, `appendix-a-local-theory.tex:124-125`): `(u,p)`
**is** the maximal classical solution for the datum `(ν,a,f)`.  Two clauses: the
lifespan is positive, and `u`, `p` are *literally* the velocity and pressure of a
classical solution on `[0,S)` for **every** `S` below the maximal lifespan.
Restated token-for-token in `Contracts.V1.Data` vocabulary; the predicate the two
new fields quantify over. -/
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p

/-- **The proved part of A02's maximal-solution interface, version 2.**  Version
one's `MaximalPartialAPI` (ten fields plus the carried `A02.uniqueness`), together
with the existence and uniqueness of the maximal solution (unit **U7**,
`Section4/A02/Maximal.lean`, lane 064).

Every field of `Contracts.V1.MaximalPartial.MaximalPartialAPI` is inherited
verbatim through `toMaximalPartialAPI`; see `Contracts/V1/MaximalPartial.lean` for
their docstrings and manuscript citations.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure MaximalPartialV2API extends
    BlowupDensity.Contracts.V1.MaximalPartial.MaximalPartialAPI where
  /-- `02-preliminaries.tex:105` "has a unique maximal smooth velocity":
  **existence** of the maximal solution for every admissible datum, attaining
  `maximalLifespanR` in the sense of `IsMaximalSolution` — a classical solution on
  `[0,S)` for every `S` below the maximal lifespan, with one velocity and one
  pressure field serving all of them.  `research/A02/Spec.lean:421-423`.

  Stated **in the form `Section4/A02/Maximal.lean` proves it**
  (`exists_maximal_of_localSolution`): the A01 clause ⟪A01:LocalTheoryAPI.solution⟫
  (`research/A02/Spec.lean:317-321`) — the local classical solution on `[0,horizon)`
  for every manuscript datum — is an **explicit hypothesis** here rather than an
  ambient A01 field, exactly as version one's `horizon_le_lifespan` does.  It is
  genuinely used: `0 < maximalLifespanR` holds precisely because A01 supplies a
  local solution.  Instantiating `localSolution` at A01's `LocalTheoryAPI.solution`
  once A01 is registered gives the spec field verbatim. -/
  exists_maximal : ∀ (horizon : ℝ → SpatialField → SpaceTimeField → ℝ),
    (∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) →
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p
  /-- `02-preliminaries.tex:105`, the word "unique": any two maximal solutions of
  the same datum have the same velocity at every presingular time and
  gauge-equivalent pressures there.  The `R42` risk note
  `research/section4/STATEMENTS.md:393-395` ("the definite article presupposes
  uniqueness (A02)") is discharged by this field.  `research/A02/Spec.lean:429-434`,
  discharged **verbatim** (no A01 hypothesis) by `Section4/A02/Maximal.lean`
  `maximal_unique`: the two `IsMaximalSolution` hypotheses already supply the
  solutions on `[0,S)`. -/
  maximal_unique : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
        IsMaximalSolution ν a f u₁ p₁ → IsMaximalSolution ν a f u₂ p₂ →
          (∀ t ∈ presingularTimes ν a f, ∀ x : Space, u₁ (t, x) = u₂ (t, x)) ∧
          PressureGaugeEquivOn (presingularTimes ν a f) p₁ p₂

end BlowupDensity.Contracts.V2.MaximalPartial
