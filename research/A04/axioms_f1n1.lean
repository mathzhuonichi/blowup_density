/-
Conformance file for A04 units F1 and N1 (lane 039).

Checked with:
  cd verification && lake env lean ../research/A04/axioms_f1n1.lean

Every `theorem` below is stated in the **spec's own vocabulary**: the norms are
`Contracts.V1.Data.{sobolevENorm, forceSobolevENormL1}`, the classes are
`Data.{MemForceR, ClassicalSolutionR}`, and `sobolevNormAt`, `MemL1Hm`,
`BoundedIntoHOne` are reproduced token-for-token from `research/A04/Spec.lean`
(lines 183, 268, 286) in the `BlowupDensity.A04.Draft` namespace, exactly as
`Spec.lean` writes them.  Each statement is discharged by the corresponding
theorem of `NSFormalization.Section4.A04.{Forcing, Continuity}`; the discharge
goes through `exact`/definitional unfolding because every restated `def` in
those modules is field-for-field defeq to the `Data` original.

`Data.ClassicalSolutionR` and the local `NSFormalization.Section4.A02` restatement
are distinct inductive types (a `rfl` bridge is impossible for a structure), so
the N1 statements bridge them with the field-by-field conversion `toA02`, exactly
as a `verification/Bindings` module would; every field type is defeq, so `toA02`
is a plain structure literal and `(toA02 w).velocity` reduces to `w.velocity`.

`#print axioms` at the foot confirms the F1/N1 theorems use only
`propext, Classical.choice, Quot.sound`.
-/
import Contracts.V1.Data
import NSFormalization.Section4.A04.Continuity

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

namespace BlowupDensity.A04.Draft

/-! ## The A04 draft `def`s, token-for-token from `research/A04/Spec.lean` -/

/-- `research/A04/Spec.lean:183`. -/
def sobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `research/A04/Spec.lean:268`. -/
def MemL1Hm (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤

/-- `research/A04/Spec.lean:286`. -/
def BoundedIntoHOne (I : Set ℝ) (K : ℝ≥0∞) (f : SpaceTimeField) : Prop :=
  ∀ t ∈ I, sobolevENorm 1 (fun x : Space => f (t, x)) ≤ K

/-! ## The structure bridge `Data.ClassicalSolutionR → A02.ClassicalSolutionR` -/

/-- Field-by-field conversion into the `NSFormalization` restatement.  Each field
type is definitionally the contract's (see `Section4/A02/SolutionClass.lean`), so
this is a plain structure literal. -/
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

/-! ## F1 conformance -/

/-- F1a: `MemForceR f → MemL1Hm f` (spec vocabulary). -/
theorem f1a_memL1Hm_of_memForceR :
    ∀ f : SpaceTimeField, MemForceR f → MemL1Hm f :=
  fun _f hf => NSFormalization.Section4.A04.memL1Hm_of_memForceR hf

/-- F1b: `MemForceR f → ∃ K ≠ ⊤, BoundedIntoHOne (Icc 0 b) K f` (spec vocabulary). -/
theorem f1b_exists_boundedIntoHOne_of_memForceR :
    ∀ f : SpaceTimeField, MemForceR f →
      ∀ b : ℝ, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ BoundedIntoHOne (Icc 0 b) K f :=
  fun _f hf b => NSFormalization.Section4.A04.exists_boundedIntoHOne_of_memForceR hf b

/-! ## N1 conformance -/

/-- N1 finiteness: the velocity `H^m` norm is finite on `[0,T)` (spec vocabulary). -/
theorem n1_sobolevENorm_velocity_ne_top :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ}, t ∈ Ico (0 : ℝ) T →
      sobolevENorm (m : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ :=
  fun _ν _a _f _T w m _t ht =>
    NSFormalization.Section4.A04.sobolevENorm_velocity_ne_top (toA02 w) m ht

/-- N1 finiteness: the force `H^m` norm is finite at nonnegative times (spec vocabulary). -/
theorem n1_sobolevENorm_force_ne_top :
    ∀ (f : SpaceTimeField), MemForceR f → ∀ (m : ℕ) {t : ℝ}, 0 ≤ t →
      sobolevENorm (m : ℝ) (fun x : Space => f (t, x)) ≠ ⊤ :=
  fun _f hf m _t ht => NSFormalization.Section4.A04.sobolevENorm_force_ne_top hf m ht

/-- N1 continuity of the velocity norm on `[0,T)` (spec vocabulary). -/
theorem n1_continuousOn_sobolevNormAt_velocity :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (w : ClassicalSolutionR ν a f T) (m : ℕ),
      ContinuousOn (fun t => sobolevNormAt (m : ℝ) w.velocity t) (Ico (0 : ℝ) T) :=
  fun _ν _a _f _T w m =>
    NSFormalization.Section4.A04.continuousOn_sobolevNormAt_velocity (toA02 w) m

/-- N1 continuity of the force norm on `[0,T)` (spec vocabulary). -/
theorem n1_continuousOn_sobolevNormAt_force :
    ∀ (f : SpaceTimeField), MemForceR f → ∀ (m : ℕ) (T : ℝ),
      ContinuousOn (fun t => sobolevNormAt (m : ℝ) f t) (Ico (0 : ℝ) T) :=
  fun _f hf m T => NSFormalization.Section4.A04.continuousOn_sobolevNormAt_force hf m T

/-- N1 payoff: the `highContinuationIntegral` integrand is `IntervalIntegrable`
on `[t₀,t] ⊆ [0,T)`, in the exact shape of `research/A04/Spec.lean:499-510`
(spec vocabulary), so the field's `IntervalIntegrable` conjunct is free. -/
theorem n1_intervalIntegrable_highContinuationIntegrand :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      MemForceR f → ∀ (w : ClassicalSolutionR ν a f T) (Cgron : ℕ → ℝ → ℝ) (m : ℕ) (t₀ t : ℝ),
        0 ≤ t₀ → t₀ ≤ t → t < T →
        IntervalIntegrable
          (fun s : ℝ =>
            Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (m : ℝ) w.velocity s +
              sobolevNormAt (m : ℝ) f s) volume t₀ t :=
  fun _ν _a _f _T hf w Cgron m _t₀ _t h0 htt htT =>
    NSFormalization.Section4.A04.intervalIntegrable_highContinuationIntegrand
      hf (toA02 w) Cgron m h0 htt htT

end BlowupDensity.A04.Draft

/-! ## Axiom audit -/

-- The F1/N1 library theorems.
#print axioms NSFormalization.Section4.A04.memL1Hm_of_memForceR
#print axioms NSFormalization.Section4.A04.exists_boundedIntoHOne_of_memForceR
#print axioms NSFormalization.Section4.A04.sobolevENorm_velocity_ne_top
#print axioms NSFormalization.Section4.A04.sobolevENorm_force_ne_top
#print axioms NSFormalization.Section4.A04.continuousOn_sobolevNormAt_velocity
#print axioms NSFormalization.Section4.A04.continuousOn_sobolevNormAt_force
#print axioms NSFormalization.Section4.A04.intervalIntegrable_highContinuationIntegrand

-- The spec-vocabulary conformance theorems (chase the bridge too).
#print axioms BlowupDensity.A04.Draft.f1a_memL1Hm_of_memForceR
#print axioms BlowupDensity.A04.Draft.f1b_exists_boundedIntoHOne_of_memForceR
#print axioms BlowupDensity.A04.Draft.n1_intervalIntegrable_highContinuationIntegrand
