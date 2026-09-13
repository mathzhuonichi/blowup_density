import NSFormalization.Paper1.PeriodicFlowRestriction
import NSFormalization.Paper1.PeriodicLocalLifespan

/-!
# Restriction of normalized periodic flows

A normalized classical flow remains normalized after restriction to any shorter
positive horizon.  This is a bookkeeping bridge for the local/maximal theory;
it does not reconstruct a flow from a mild path or add any regularity.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLifespan

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicLocalLifespan
open scoped ContDiff ENNReal

/-- Restriction preserves the pressure normalization on its shorter horizon. -/
theorem Flow.restrict_isNormalized
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hW : IsNormalized W)
    {R : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    IsNormalized (W.restrict hR hRS) := by
  intro t ht
  exact hW t ⟨ht.1, ht.2.trans_le hRS⟩

/-- A normalized flow on `S` yields a normalized flow on every shorter
positive horizon. -/
theorem exists_normalized_restrict
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hW : IsNormalized W)
    {R : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    ∃ V : Flow ν a f R, IsNormalized V :=
  ⟨W.restrict hR hRS, W.restrict_isNormalized hW hR hRS⟩

end NSFormalization.Paper1.PeriodicLifespan

namespace NSFormalization.Paper1.PeriodicLifespan

open NavierStokes NavierStokes.ProblemStatement

/-- A strict shorter horizon of an actual flow lies strictly below the
supremum lifespan.  This is the quantitative endpoint bookkeeping needed
when passing from a finite witness to a maximal trajectory. -/
theorem lifespan_strictly_above_of_flow
    {ν S R : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (hR : 0 < R) (hRS : R < S) :
    ENNReal.ofReal R < lifespan ν a f := by
  have hle : ENNReal.ofReal S ≤ lifespan ν a f :=
    horizon_le_lifespan W
  have hlt : ENNReal.ofReal R < ENNReal.ofReal S :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_trans hR hRS)).mpr hRS
  exact lt_of_lt_of_le hlt hle

end NSFormalization.Paper1.PeriodicLifespan
