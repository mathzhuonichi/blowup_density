import Contracts.V1.Data
import Contracts.V1.GradientL6
import NSFormalization.Section4.C01.VelocityJets
import NSFormalization.Section4.C01.Evolution

/-!
# C01 units U1 (and U3 core): conformance and axiom audit

Checked out of the build with `cd verification && lake env lean ../research/C01/axioms_u1u3.lean`.

This file has three jobs:

1. §0 restates the draft spec's slicing `def` (`research/C01/Spec.lean:167`)
   token-for-token, so the conformance `example` is stated in the *spec's* own
   vocabulary rather than in the implementation's.
2. §1 discharges an `example` whose type is the draft field
   `BlowupDensity.C01.Draft.EnergyAbsorptionAPI.velocityJets`
   (`research/C01/Spec.lean:295-300`), verbatim, by the U1 theorem
   `NSFormalization.Section4.C01.velocity_slice_memHInfty_and_smoothL2`.  It
   goes through the field-by-field conversion of the `Data.ClassicalSolutionR`
   structure into `Section4/A02/SolutionClass.lean`'s restatement — the only
   move a binding may not do by `rfl` (two separately declared structures are
   distinct inductive types; every *field type* is defeq, so the conversion
   typechecks and `MemHInfty`/`SmoothSquareIntegrableJets` match by `exact`).
3. §2 prints the transitive axioms of every public C01/U1 theorem.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1 (SmoothSquareIntegrableJets)
open BlowupDensity.Contracts.V1.Data

/-! ## 0. The spec's slicing def, restated verbatim from `research/C01/Spec.lean:167` -/

/-- The spatial slice `z(t) = z(t,·)` of a spacetime field
(`research/C01/Spec.lean:167`, token-for-token). -/
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)

/-! ## 1. Conformance for `velocityJets` -/

/-- Field-by-field conversion of the canonical `Data.ClassicalSolutionR` into the
`Section4/A02` restatement.  Each field's type is definitionally the contract's
(`Section4/A02/SolutionClass.lean:100` is byte-identical to `Data.lean:624-648`),
so every assignment typechecks. -/
def toA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
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

/-- **Conformance for `EnergyAbsorptionAPI.velocityJets`
(`research/C01/Spec.lean:295-300`).**  The type below is that field verbatim, in
the spec's vocabulary (`Data.MemHInfty`, `Contracts.V1.SmoothSquareIntegrableJets`,
and the `slice` of §0), discharged by the U1 theorem. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          MemHInfty (slice w.velocity t) ∧
            SmoothSquareIntegrableJets (slice w.velocity t) :=
  fun _ _ _ _ _ _ _ w _ ht =>
    NSFormalization.Section4.C01.velocity_slice_memHInfty_and_smoothL2 (toA02 w) ht

/-! ## 2. Axiom audit -/

-- U1
#print axioms NSFormalization.Section4.C01.velocity_slice_memHInfty_and_smoothL2
#print axioms NSFormalization.Section4.C01.velocity_slice_memHInfty
#print axioms NSFormalization.Section4.C01.velocity_slice_smoothL2
-- U3
#print axioms NSFormalization.Section4.C01.velocityField
#print axioms NSFormalization.Section4.C01.velocityField_field
#print axioms NSFormalization.Section4.C01.velocityField_solenoidal
#print axioms NSFormalization.Section4.C01.jetOfDatum_continuous
#print axioms NSFormalization.Section4.C01.velocityField_jetLp_continuous
