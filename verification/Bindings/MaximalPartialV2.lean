import Contracts.V2.MaximalPartial
import Bindings.MaximalPartial
import NSFormalization.Section4.A02.Maximal

/-! Current maximal-solution interface, assembled from the live lifespan, existence and uniqueness results. -/

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

end BlowupDensity.Bindings
