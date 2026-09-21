import Bindings.CompletedSobolevDensity

noncomputable section

namespace BlowupDensity.R46.Reviewer

open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal

/- Deliberately false strengthening of the main statement: the strict order
threshold is widened to include its endpoint.  The lane proof must not survive. -/
theorem completedSobolevDensity_closedEndpoint :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
            ∀ s : ℝ, s ≤ criticalOrder q.toReal →
              CompletedDense q s
                (breakdownSetIn forceClassCompact ν a T) := by
  intro a ha ν hν T hT q hq s hs b hb r hr
  have hq1 : 1 ≤ q := by
    rcases hq with rfl | rfl <;> norm_num
  have hqtop : q ≠ ⊤ := by
    rcases hq with rfl | rfl <;> norm_num
  have hrhalf : 0 < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨g, hg, Dg, hDg, hDgmeas, hDgdist⟩ :=
    Bindings.bochnerPartial.approxCompact q hq1 hqtop s b hb (r / 2) hrhalf
  obtain ⟨f, hf, hfgdist⟩ :=
    Bindings.density_compact ν hν T hT q hq s a ha hs g hg (r / 2) hrhalf

end BlowupDensity.R46.Reviewer
