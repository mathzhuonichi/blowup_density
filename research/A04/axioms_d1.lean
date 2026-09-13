/-
Conformance file for A04 unit D1 (lane 053).

Checked with:
  cd verification && lake env lean ../research/A04/axioms_d1.lean

Purpose, exactly as `axioms_f1n1.lean` for F1/N1:

* Restate the two spec objects D1 rests on — `sobolevNormAt` and
  `HasSmoothSobolevPath` — token-for-token from `research/A04/Spec.lean`
  (lines 183, 247) in the spec's own vocabulary: the norm is
  `Contracts.V1.Data.sobolevENorm`, the datum predicate is
  `Data.IsSobolevDatum`, the carrier is `Paper3.RealVectorSobolev`, the solution
  class is `Data.ClassicalSolutionR`.
* Show the D1 payoff discharges the exact left-hand side of the spec field
  `energyIdentityHigh` (`research/A04/Spec.lean:429`),
  `∃ d, HasDerivAt (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t` on
  `Ioo 0 T`, from the field's own hypothesis `HasSmoothSobolevPath T w.velocity`.
  The discharge goes through `exact`/definitional unfolding: `Data.sobolevENorm`
  and `Data.IsSobolevDatum` are the verbatim originals of the `D01` restatements
  `NSFormalization.Section4.A04.exists_hasDerivAt_sobolevNormAt_sq` is stated
  against, so the two `sobolevNormAt`s and the two `HasSmoothSobolevPath`s are
  field-for-field defeq.  D1 touches only `w.velocity : SpaceTimeField` and the
  separate `HasSmoothSobolevPath` hypothesis, never a solution-structure field,
  so no `Data.ClassicalSolutionR → A02.ClassicalSolutionR` bridge is needed here
  (unlike `axioms_f1n1.lean`).

`#print axioms` at the foot confirms every D1 theorem uses only
`propext, Classical.choice, Quot.sound`.
-/
import Contracts.V1.Data
import NSFormalization.Section4.A04.DerivNorm

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal RealInnerProductSpace

namespace BlowupDensity.A04.Draft

/-! ## The A04 draft `def`s, token-for-token from `research/A04/Spec.lean` -/

/-- `research/A04/Spec.lean:183`. -/
def sobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `research/A04/Spec.lean:247`. -/
def HasSmoothSobolevPath (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

/-! ## D1 conformance -/

/-- D1, spec vocabulary: from `HasSmoothSobolevPath T u` the squared datum norm
`r ↦ sobolevNormAt (m:ℝ) u r ^ 2` is differentiable at every interior time, and
its value at a slice is the honest datum norm `‖G r‖`.  Discharged by
`exists_hasDerivAt_sobolevNormAt_sq`. -/
theorem d1_exists_hasDerivAt_sobolevNormAt_sq :
    ∀ (u : SpaceTimeField) (T : ℝ), HasSmoothSobolevPath T u → ∀ m : ℕ,
      ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        (∀ r ∈ Ico (0 : ℝ) T, sobolevNormAt (m : ℝ) u r = ‖G r‖) ∧
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (fun r => sobolevNormAt (m : ℝ) u r ^ 2)
              (2 * ⟪G t, deriv G t⟫) t :=
  fun _u _T hpath m =>
    NSFormalization.Section4.A04.exists_hasDerivAt_sobolevNormAt_sq hpath m

/-- **The shape `energyIdentityHigh`'s left side expects** (`research/A04/Spec.lean:429`).
For a classical solution `w` with `HasSmoothSobolevPath T w.velocity`, at every
integer order `m ≥ 3` and every interior time `t`,
`∃ d, HasDerivAt (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t`.  This is
exactly the first conjunct of the `energyIdentityHigh` field (the `d`-value
`2⟪G t, deriv G t⟫` is exposed through `d1_exists_hasDerivAt_sobolevNormAt_sq`
for unit G1 to bound); the remaining conjunct is the eq:Rhigh estimate, out of
D1's scope. -/
theorem d1_energyIdentityHigh_lhs :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (w : ClassicalSolutionR ν a f T), HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ d : ℝ,
            HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t := by
  intro _ν _a _f T w hpath m _hm t ht
  obtain ⟨_G, _hid, hderiv⟩ :=
    NSFormalization.Section4.A04.exists_hasDerivAt_sobolevNormAt_sq
      (u := w.velocity) hpath m
  exact ⟨_, hderiv t ht⟩

end BlowupDensity.A04.Draft

/-! ## Axiom audit -/

-- The D1 library theorems and the supplied inner-product instance (lifted to Paper3).
#print axioms NSFormalization.Paper3.realSobolevInnerProductSpace
#print axioms NSFormalization.Section4.A04.hasDerivAt_datumNormSq
#print axioms NSFormalization.Section4.A04.hasDerivAt_datumPath
#print axioms NSFormalization.Section4.A04.hasDerivAt_datumNormSq_of_contDiffOn
#print axioms NSFormalization.Section4.A04.exists_hasDerivAt_sobolevNormAt_sq

-- The spec-vocabulary conformance theorems (chase the bridge too).
#print axioms BlowupDensity.A04.Draft.d1_exists_hasDerivAt_sobolevNormAt_sq
#print axioms BlowupDensity.A04.Draft.d1_energyIdentityHigh_lhs
