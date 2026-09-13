import Contracts.V1.Data
import NSFormalization.Section4.B02.LebesgueDatum

/-!
# Conformance check for B02 unit 6 (`lebesgueHomogeneousDatum`)

Spec-typed `example`s stated against the frozen `Contracts.V1.Data` predicates
(`verification/Contracts/V1/Data.lean`) and discharged by the theorems of
`NSFormalization.Section4.B02.LebesgueDatum`.  The `example`s typecheck because
the `B02`/`D01.Homogeneous` restatements are *definitionally equal* to the `Data`
predicates.  `#print axioms` confirms only the standard logical axioms are used.

Note: the spec's original `homogeneousDatumSub` (no integrability hypotheses) was
proved **false** by lane 068's review (`research/B02/REVIEW_U6.md` §4); the
corrected, integrability-carrying form is the one checked here.
-/

open MeasureTheory NavierStokes.ProblemStatement NSFormalization.Paper3
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal SchwartzMap

namespace BlowupDensity.B02.ConformanceU6

/-- Verbatim `research/B02/Spec.lean:237`, matching the sibling conformance files. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-- `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum`, verbatim spec type,
discharged by `NSFormalization.Section4.B02.lebesgueHomogeneousDatum`. -/
example : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
    MemLp k 1 volume → MemLp k 2 volume →
    (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
      ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
        ‖G‖ₑ = homogeneousFourierENorm s k :=
  fun _s hs k hk1 hk2 =>
    NSFormalization.Section4.B02.lebesgueHomogeneousDatum hs.1 hs.2 k hk1 hk2

/-- `research/B02/Spec.lean:470` `homogeneousDatumSub` — the **corrected**,
integrability-carrying form.  The original verbatim spec field carried **no**
integrability hypotheses and is *false* (lane 068 review `REVIEW_U6.md` §4,
counterexample in `ATTEMPTS_U6.md` §3): a field pairing non-integrably with every
Schwartz test carries the zero datum vacuously.  The two side conditions here are
`Integrable.mul_bdd` facts, discharged for the diagonal by `Cutoff.lean`'s
`integrable_schwartzVector` / `integrable_cutoffCompl_schwartzVector`. -/
example : ∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
    IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume) →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ)) volume) →
      IsHomogeneousSliceDatum s (z - w) (Z - W) :=
  fun _s _z _w _Z _W hZ hW hz hw =>
    NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable hZ hW hz hw

end BlowupDensity.B02.ConformanceU6

#print axioms NSFormalization.Section4.B02.lebesgueHomogeneousDatum
#print axioms NSFormalization.Section4.B02.isHomogeneousSliceDatum_lebesgue
#print axioms NSFormalization.Section4.B02.angularFourierDistribution_lp_apply
#print axioms NSFormalization.Section4.B02.homogeneousProfile_memLp
#print axioms NSFormalization.Section4.B02.enorm_lebesgueVectorDatum
#print axioms NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable
#print axioms NSFormalization.Section4.B02.spatialApproxHomogeneous_of_units
