import Contracts.V1.Uniqueness
import NSFormalization.Section4.A02.Uniqueness

/-! The only layer that knows the current implementation's names for the
uniqueness clauses of `prop:local` on `R³`.

`Contracts.V1.Uniqueness` is self-contained — its sole import is another
contract, `Contracts.V1.Data`.  The proved theorems live in
`formalization/NSFormalization/Section4/A02/Uniqueness.lean`
(`velocity_unique`, `pressure_gauge`), stated on the **A02-local** restatement of
the solution class (`Section4/A02/SolutionClass.lean`).

`Contracts.V1.Data.ClassicalSolutionR` and that restatement are two separately
declared `structure`s, hence distinct inductive types: a `rfl` bridge is
impossible for the structure itself.  Every *field type* is definitionally the
contract's (`SolutionClass.lean` is token-for-token `Data.lean:624-648`), so the
binding moves a solution across the two copies **field by field** with `toA02`,
exactly as the conformance files `research/A02/axioms_u2u3.lean`,
`research/A04/axioms_f1n1.lean` and `research/C01/axioms_u1u3.lean` already do.
`toA02` is a plain structure literal and `(toA02 w).velocity` reduces to
`w.velocity` by `rfl` (recorded as the two `example`s below).

The three predicate/set restatements A02 also carries (`initialClassR`,
`MemForceR`, `PressureGaugeEquivOn`) are token-identical `def`s, so their `rfl`
bridges are stated in §0 to guard against drift; the field assignments then
typecheck by definitional unfolding.

Every declaration carries a `uniqueness_` prefix; `BlowupDensity.Bindings` is a
flat namespace shared by all adapters.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data

section Correspondence

variable (I : Set ℝ) (a : SpatialField) (f : SpaceTimeField) (p q : SpaceTimeScalar)

/-- The contract's initial class `X_R` is the A02-local restatement. -/
theorem uniqueness_initialClassR_eq :
    (initialClassR : Set SpatialField) = NSFormalization.Section4.A02.initialClassR := rfl

/-- The contract's force class `F_R` is the A02-local restatement. -/
theorem uniqueness_memForceR_eq :
    MemForceR f = NSFormalization.Section4.A02.MemForceR f := rfl

/-- The contract's pressure-gauge relation is the A02-local restatement. -/
theorem uniqueness_pressureGaugeEquivOn_eq :
    PressureGaugeEquivOn I p q
      = NSFormalization.Section4.A02.PressureGaugeEquivOn I p q := rfl

end Correspondence

/-- Field-by-field conversion of the canonical `Data.ClassicalSolutionR` into the
`Section4/A02` restatement.  Each field's type is definitionally the contract's
(`Section4/A02/SolutionClass.lean:114` is byte-identical to `Data.lean:624-648`),
so this is a plain structure literal. -/
def uniqueness_toA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    NSFormalization.Section4.A02.ClassicalSolutionR ν a f T where
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

/-- The conversion preserves the velocity field on the nose. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) : (uniqueness_toA02 w).velocity = w.velocity := rfl

/-- The conversion preserves the pressure field on the nose. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) : (uniqueness_toA02 w).pressure = w.pressure := rfl

/-- Bind the proved uniqueness clauses of `prop:local` to the stable
version-one contract.  Each field applies the corresponding A02 theorem to the
two solutions transported by `uniqueness_toA02`; the conclusion is definitionally
the contract's, since `(uniqueness_toA02 w).{velocity,pressure}` reduce to
`w.{velocity,pressure}` and the datum/force/gauge predicates agree by §0.

`UniquenessAPI` has only propositional fields, so it lives in `Prop`; the
binding is therefore a `theorem` rather than a `def`. -/
theorem uniqueness : Contracts.V1.Uniqueness.UniquenessAPI where
  velocity_unique := fun ν a f hν ha hf T₁ T₂ u₁ u₂ =>
    NSFormalization.Section4.A02.velocity_unique ν a f hν ha hf T₁ T₂
      (uniqueness_toA02 u₁) (uniqueness_toA02 u₂)
  pressure_gauge := fun ν a f hν ha hf T₁ T₂ u₁ u₂ =>
    NSFormalization.Section4.A02.pressure_gauge ν a f hν ha hf T₁ T₂
      (uniqueness_toA02 u₁) (uniqueness_toA02 u₂)

end BlowupDensity.Bindings
