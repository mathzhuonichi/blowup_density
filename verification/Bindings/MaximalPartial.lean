import Contracts.V1.MaximalPartial
import Bindings.Uniqueness
import NSFormalization.Section4.A02.Patch

/-! The only layer that knows the current implementation's names for the proved
part of A02's maximal-solution interface (beyond the registered uniqueness half).

`Contracts.V1.MaximalPartial` is self-contained — it imports only other contracts
(`Contracts.V1.Data`, `Contracts.V1.Uniqueness`).  The proved theorems live in
`formalization/NSFormalization/Section4/A02/{Restrict,Order,Patch}.lean`, stated on
the **A02-local** restatement of the solution class
(`Section4/A02/SolutionClass.lean`).  `NSFormalization.Section4.A02.Patch` imports
that whole chain, so it is the single formalization import here; `Bindings.Uniqueness`
supplies both the field-by-field conversion `uniqueness_toA02` and the registered
`uniqueness` binding this record carries.

## Why one short proof is unavoidable, and where

`Contracts.V1.Data.ClassicalSolutionR` and the `Section4/A02` restatement are two
separately declared `structure`s, hence distinct inductive types: a `rfl` bridge
is impossible for the structure itself, so the binding moves a solution across the
two copies **field by field** (`uniqueness_toA02`, and its inverse
`maximalPartial_ofA02` added here — needed because `restrict`, `patch` and
`pressure_normalization` *produce* a `ClassicalSolutionR`).  Every field type is
definitionally the contract's (`SolutionClass.lean` is token-for-token
`Data.lean:624-648`), so both conversions are plain structure literals and their
velocity/pressure projections reduce by `rfl` (recorded as the `example`s below).

The two objects `initialClassR`, `MemForceR`, `PressureGaugeEquivOn` A02 also
restates are token-identical `def`s and bridge by definitional unfolding, and the
restated `limsupLeft`/`speedENorm` bridge by `rfl` (§0).  The **only** objects that
resist are the two that *quantify over the solution class*: `maximalLifespanR` (a
double `iSup` through `Nonempty`) and `RegularThrough` (one `Iff`).  The 032
reviewer verified this is exactly "one `iSup` congruence + one `Iff`"
(`research/A02/REVIEW_U4U6.md` finding 1).  Both are proved once in §2 and reused;
the derived `Nonempty`/`IsEmpty` equivalences follow from the two conversions.
Every field assignment in §3 is then the corresponding A02 theorem applied up to
these conversions; the three `Iff`-valued fields transport their two sides with a
one-line `rw` (pure plumbing, no mathematics).

Every declaration carries a `maximalPartial_` prefix; `BlowupDensity.Bindings` is a
flat namespace shared by all adapters.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## 0. `rfl` bridges for the two restated `def`s -/

/-- The contract's `limsupLeft` is the `Section4/A02` restatement. -/
theorem maximalPartial_limsupLeft_eq :
    Contracts.V1.MaximalPartial.limsupLeft = NSFormalization.Section4.A02.limsupLeft := rfl

/-- The contract's `speedENorm` is the `Section4/A02` restatement. -/
theorem maximalPartial_speedENorm_eq :
    Contracts.V1.MaximalPartial.speedENorm = NSFormalization.Section4.A02.speedENorm := rfl

/-! ## 1. The inverse structure conversion `A02 → Data`

`Bindings.Uniqueness.uniqueness_toA02` is the forward conversion
`Data.ClassicalSolutionR → A02.ClassicalSolutionR`.  Its inverse is needed for the
fields whose *conclusion* produces a solution.  Both are plain structure literals,
each field's type being definitionally the other's. -/

/-- Field-by-field conversion of the `Section4/A02` restatement back into the
canonical `Data.ClassicalSolutionR`. -/
def maximalPartial_ofA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) :
    ClassicalSolutionR ν a f T where
  velocity := w.velocity
  pressure := w.pressure
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth
  pressure_smooth := w.pressure_smooth
  initial := w.initial
  divergence := w.divergence
  momentum := w.momentum
  sobolev := w.sobolev
  pressure_gradient := w.pressure_gradient

/-- `ofA02` preserves the velocity field on the nose. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) :
    (maximalPartial_ofA02 w).velocity = w.velocity := rfl

/-- `ofA02` preserves the pressure field on the nose. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T) :
    (maximalPartial_ofA02 w).pressure = w.pressure := rfl

/-- Round trip `ofA02 ∘ toA02` agrees with the original on the velocity. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) :
    (maximalPartial_ofA02 (uniqueness_toA02 u)).velocity = u.velocity := rfl

/-- Round trip `ofA02 ∘ toA02` agrees with the original on the pressure. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) :
    (maximalPartial_ofA02 (uniqueness_toA02 u)).pressure = u.pressure := rfl

/-! ## 2. Transport of the two objects that quantify over the solution class

These are the acknowledged unavoidable short proofs in the binding (the 032
reviewer's "one `iSup` congruence + one `Iff`", `research/A02/REVIEW_U4U6.md`
finding 1).  The `Nonempty`/`IsEmpty` equivalences are their immediate corollaries. -/

/-- The two copies of the solution class are simultaneously (un)inhabited. -/
theorem maximalPartial_nonempty_iff (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (S : ℝ) :
    Nonempty (NSFormalization.Section4.A02.ClassicalSolutionR ν a f S) ↔
      Nonempty (ClassicalSolutionR ν a f S) :=
  ⟨fun h => ⟨maximalPartial_ofA02 h.some⟩, fun h => ⟨uniqueness_toA02 h.some⟩⟩

/-- Corollary: emptiness transports too (needed by `lifespan_le_iff_no_extension`). -/
theorem maximalPartial_isEmpty_iff (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (S : ℝ) :
    IsEmpty (NSFormalization.Section4.A02.ClassicalSolutionR ν a f S) ↔
      IsEmpty (ClassicalSolutionR ν a f S) := by
  rw [← not_nonempty_iff, ← not_nonempty_iff, maximalPartial_nonempty_iff]

/-- **The `iSup` congruence.**  `maximalLifespanR` is a double `iSup` through
`Nonempty` of the solution class, so it transports across the two copies by the
`Nonempty` equivalence above. -/
theorem maximalPartial_maximalLifespanR_eq (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) :
    NSFormalization.Section4.A02.maximalLifespanR ν a f = maximalLifespanR ν a f := by
  simp only [NSFormalization.Section4.A02.maximalLifespanR, maximalLifespanR]
  apply le_antisymm
  · exact iSup_le fun S => iSup_le fun h =>
      le_iSup_of_le S (le_iSup_of_le ⟨maximalPartial_ofA02 h.some⟩ le_rfl)
  · exact iSup_le fun S => iSup_le fun h =>
      le_iSup_of_le S (le_iSup_of_le ⟨uniqueness_toA02 h.some⟩ le_rfl)

/-- **The one `Iff`.**  `RegularThrough` is `∃ δ > 0, Nonempty (solution on [0,T+δ))`,
so it transports by the `Nonempty` equivalence. -/
theorem maximalPartial_regularThrough_iff (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (T : ℝ) :
    NSFormalization.Section4.A02.RegularThrough ν a f T ↔ RegularThrough ν a f T := by
  refine ⟨fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩, fun ⟨δ, hδ, h⟩ => ⟨δ, hδ, ?_⟩⟩
  · exact ⟨maximalPartial_ofA02 h.some⟩
  · exact ⟨uniqueness_toA02 h.some⟩

/-! ## 3. The contract

Each field applies the corresponding `Section4/A02` theorem to arguments moved
across the two solution classes by `uniqueness_toA02` / `maximalPartial_ofA02`, and
adjusts `maximalLifespanR`, `RegularThrough`, `Nonempty`, `IsEmpty` by the §2
transports.  The datum/force/gauge predicates and the `limsupLeft`/`speedENorm`
hypotheses match definitionally, so they pass through unchanged.

`MaximalPartialAPI` has only propositional fields, so it lives in `Prop`; the
binding is therefore a `theorem`. -/
theorem maximalPartial : Contracts.V1.MaximalPartial.MaximalPartialAPI where
  uniqueness := uniqueness
  restrict := fun ν a f T u S hS hST =>
    let ⟨w, hv, hp⟩ :=
      NSFormalization.Section4.A02.exists_restrict ν a f T (uniqueness_toA02 u) S hS hST
    ⟨maximalPartial_ofA02 w, hv, hp⟩
  patch := fun ν a f hν ha hf T₁ T₂ u₁ u₂ =>
    let ⟨w, h1, h2, h3, h4⟩ :=
      NSFormalization.Section4.A02.patch ν a f hν ha hf T₁ T₂
        (uniqueness_toA02 u₁) (uniqueness_toA02 u₂)
    ⟨maximalPartial_ofA02 w, h1, h2, h3, h4⟩
  horizon_le_lifespan := fun horizon localSolution ν a f hν ha hf =>
    le_of_le_of_eq
      (NSFormalization.Section4.A02.horizon_le_lifespan_of_localSolution
        (horizon := horizon)
        (fun ν a f hν ha hf => uniqueness_toA02 (localSolution ν a f hν ha hf))
        ν a f hν ha hf)
      (maximalPartial_maximalLifespanR_eq ν a f)
  pressure_normalization := fun ν a f T w x₀ =>
    let ⟨w', hv, hp⟩ :=
      NSFormalization.Section4.A02.exists_pressure_normalization ν a f T
        (uniqueness_toA02 w) x₀
    ⟨maximalPartial_ofA02 w', hv, hp⟩
  lifespan_le_iff := fun ν a f T hT => by
    rw [← maximalPartial_maximalLifespanR_eq]
    exact (NSFormalization.Section4.A02.lifespan_le_iff ν a f T hT).trans
      (forall_congr' fun S => imp_congr (maximalPartial_nonempty_iff ν a f S) Iff.rfl)
  lifespan_le_iff_no_extension := fun ν a f T hT => by
    rw [← maximalPartial_maximalLifespanR_eq]
    exact (NSFormalization.Section4.A02.lifespan_le_iff_no_extension ν a f T hT).trans
      (forall_congr' fun S => imp_congr Iff.rfl (maximalPartial_isEmpty_iff ν a f S))
  lifespan_ge_of_forall_shorter := fun ν a f T hT hshort =>
    le_of_le_of_eq
      (NSFormalization.Section4.A02.lifespan_ge_of_forall_shorter ν a f T hT
        (fun b hb hbT => (maximalPartial_nonempty_iff ν a f b).mpr (hshort b hb hbT)))
      (maximalPartial_maximalLifespanR_eq ν a f)
  regularThrough_iff := fun ν a f T hT => by
    rw [← maximalPartial_regularThrough_iff, ← maximalPartial_maximalLifespanR_eq]
    exact NSFormalization.Section4.A02.regularThrough_iff ν a f T hT
  referenceLifespan := fun ν a g T hT h =>
    let ⟨δ, hδ, h1, ⟨S, hS, h2⟩, h3⟩ :=
      NSFormalization.Section4.A02.referenceLifespan ν a g T hT
        ((maximalPartial_regularThrough_iff ν a g T).mpr h)
    ⟨δ, hδ, (maximalPartial_nonempty_iff ν a g (T + δ)).mp h1,
      ⟨S, hS, (maximalPartial_nonempty_iff ν a g S).mp h2⟩,
      lt_of_lt_of_eq h3 (maximalPartial_maximalLifespanR_eq ν a g)⟩
  lifespan_le_of_unbounded := fun ν a f T hν ha hf hT u p hex hunbdd =>
    le_of_eq_of_le (maximalPartial_maximalLifespanR_eq ν a f).symm
      (NSFormalization.Section4.A02.lifespan_le_of_unbounded ν a f T hν ha hf hT u p
        (fun S hS hST =>
          let ⟨w, hv, hp⟩ := hex S hS hST
          ⟨uniqueness_toA02 w, hv, hp⟩)
        hunbdd)

end BlowupDensity.Bindings
