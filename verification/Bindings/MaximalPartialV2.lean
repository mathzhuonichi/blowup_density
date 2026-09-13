import Contracts.V2.MaximalPartial
import Bindings.MaximalPartial
import NSFormalization.Section4.A02.Maximal

/-! The implementation layer for the version-two maximal-partial contract, and the
compatibility bridge back to version one.

`Contracts.V2.MaximalPartial.MaximalPartialV2API` extends
`Contracts.V1.MaximalPartial.MaximalPartialAPI` by the two maximal-solution fields
`exists_maximal` and `maximal_unique`, both proved in
`NSFormalization.Section4.A02.Maximal` (lane 064, unit **U7**), so this file has
three jobs.

* `maximalPartialV2` inhabits the version-two record.  It reuses the frozen
  version-one witness `Bindings.maximalPartial` with `{ … with … }` and fills the
  two new fields with the `Maximal.lean` theorems, transported across the two
  `ClassicalSolutionR` copies.
* `maximalPartial_of_v2` records that version one is recoverable from version two
  by the inherited projection `toMaximalPartialAPI`; the recovery is definitional,
  so it cannot drift, and `Tests.checkedMaximalPartial` keeps using the untouched
  `Bindings.maximalPartial`.
* §1's transports carry the two restated objects across the two solution classes.

## The one unavoidable proof, and why it is the only one

`Contracts.V1.Data.ClassicalSolutionR` and the `Section4/A02` restatement are two
separately declared `structure`s, so the objects that quantify over the solution
class do not bridge by `rfl`.  Version one already proved the `maximalLifespanR`
`iSup` congruence and the `RegularThrough` `Iff` (`Bindings/MaximalPartial.lean`
§2), reused here.  The one new object is the predicate `IsMaximalSolution`, whose
transport `maximalPartial_isMaximalSolution_iff` is a single `Iff`, exactly like
version one's `RegularThrough` transport: the positivity clause and the `S`-bound
match after the `maximalLifespanR` congruence, and the inner
`∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p` transports by
the field-by-field conversions `uniqueness_toA02` / `maximalPartial_ofA02`, whose
velocity/pressure projections reduce by `rfl`.  This is the **only** non-mechanical
proof in the file, and it is kept minimal.  `maximalPartial_presingularTimes_eq`
is a plain `congrArg` on the `maximalLifespanR` congruence (no `by`); the two field
bodies are then term-mode applications of the `Maximal.lean` theorems up to these
transports.

Every declaration carries a `maximalPartial_` prefix; `BlowupDensity.Bindings` is a
flat namespace shared by all adapters.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 1. Transport of the two restated objects across the two solution classes

`presingularTimes` and `IsMaximalSolution` rest on `maximalLifespanR` (and, for the
predicate, on the solution class), so — unlike version one's `limsupLeft`/`speedENorm`
— they do not bridge by `rfl`.  `maximalPartial_maximalLifespanR_eq`,
`maximalPartial_ofA02` and `uniqueness_toA02` are reused from `Bindings.MaximalPartial`
/ `Bindings.Uniqueness`. -/

/-- The `Section4/A02` restatement of `presingularTimes` is the contract's, once
the `maximalLifespanR` `iSup` congruence is applied.  A plain `congrArg` on
`maximalPartial_maximalLifespanR_eq`: both sides are `{t | 0 ≤ t ∧ ofReal t < ·}`
of the two `maximalLifespanR` copies. -/
theorem maximalPartial_presingularTimes_eq (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) :
    NSFormalization.Section4.A02.presingularTimes ν a f
      = Contracts.V2.MaximalPartial.presingularTimes ν a f :=
  congrArg (fun L : ℝ≥0∞ => {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < L})
    (maximalPartial_maximalLifespanR_eq ν a f)

/-- **The one `Iff`.**  `IsMaximalSolution` is `0 < maximalLifespanR ∧ ∀ S …,
∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p`.  Its positivity
clause and `S`-bound transport by the `maximalLifespanR` `iSup` congruence
(`maximalPartial_maximalLifespanR_eq`), and the inner existential transports by the
field-by-field conversions `uniqueness_toA02` / `maximalPartial_ofA02`, which
preserve velocity and pressure on the nose.  The analogue of version one's
`maximalPartial_regularThrough_iff`; the only non-mechanical proof here. -/
theorem maximalPartial_isMaximalSolution_iff (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (u : SpaceTimeField) (p : SpaceTimeScalar) :
    NSFormalization.Section4.A02.IsMaximalSolution ν a f u p ↔
      Contracts.V2.MaximalPartial.IsMaximalSolution ν a f u p := by
  rw [NSFormalization.Section4.A02.IsMaximalSolution,
    Contracts.V2.MaximalPartial.IsMaximalSolution, maximalPartial_maximalLifespanR_eq]
  refine and_congr Iff.rfl (forall_congr' fun S => imp_congr Iff.rfl (imp_congr Iff.rfl ?_))
  exact ⟨fun ⟨w, hv, hp⟩ => ⟨maximalPartial_ofA02 w, hv, hp⟩,
         fun ⟨w, hv, hp⟩ => ⟨uniqueness_toA02 w, hv, hp⟩⟩

/-! ## 2. The contract

The two new fields apply the corresponding `Section4/A02/Maximal.lean` theorem to
arguments moved across the two solution classes: `exists_maximal` transports its
A01 `localSolution` hypothesis by `uniqueness_toA02` (as version one's
`horizon_le_lifespan` does) and its `IsMaximalSolution` conclusion by the `Iff`;
`maximal_unique` transports its two `IsMaximalSolution` hypotheses by the `Iff` and
its `presingularTimes` conclusion by the set equality of §1.

`MaximalPartialV2API` has only propositional fields, so it lives in `Prop`; the
binding is therefore a `theorem`. -/
theorem maximalPartialV2 : Contracts.V2.MaximalPartial.MaximalPartialV2API :=
  { maximalPartial with
    exists_maximal := fun horizon localSolution ν a f hν ha hf =>
      let ⟨u, p, hmax⟩ :=
        NSFormalization.Section4.A02.exists_maximal_of_localSolution horizon
          (fun ν a f hν ha hf => uniqueness_toA02 (localSolution ν a f hν ha hf))
          ν a f hν ha hf
      ⟨u, p, (maximalPartial_isMaximalSolution_iff ν a f u p).mp hmax⟩
    maximal_unique := fun ν a f hν ha hf u₁ u₂ p₁ p₂ hM₁ hM₂ =>
      maximalPartial_presingularTimes_eq ν a f ▸
        NSFormalization.Section4.A02.maximal_unique ν a f hν ha hf u₁ u₂ p₁ p₂
          ((maximalPartial_isMaximalSolution_iff ν a f u₁ p₁).mpr hM₁)
          ((maximalPartial_isMaximalSolution_iff ν a f u₂ p₂).mpr hM₂) }

/-- Version one is recoverable from version two by the inherited projection: a
version-two record *is* a version-one record together with the two maximal-solution
clauses.  Definitional, so it cannot drift.

`Tests.checkedMaximalPartial` does not go through this function — the registered
version-one test keeps using the untouched `Bindings.maximalPartial`.  What this
declaration rules out is a version two that quietly drops or weakens a version-one
field, which would make the projection fail to typecheck. -/
theorem maximalPartial_of_v2 : Contracts.V1.MaximalPartial.MaximalPartialAPI :=
  maximalPartialV2.toMaximalPartialAPI

end BlowupDensity.Bindings
