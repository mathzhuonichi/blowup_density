import NSFormalization.Section4.A05.CriticalL3
import Contracts.V1.Data

noncomputable section
open MeasureTheory Set
open NSFormalization.Section4
open scoped ENNReal

example : A02.MemHInfty = BlowupDensity.Contracts.V1.Data.MemHInfty := rfl

-- The exact body used by the research spec and lane 164's contract.
def review165ContractNorm (s : ℝ)
    (z : BlowupDensity.Contracts.V1.Data.SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : NSFormalization.Paper3.RealVectorSobolev s //
    BlowupDensity.Contracts.V1.Data.IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ

example : A05.dotHomogeneousENorm = review165ContractNorm := rfl

example {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ico 0 T) :
    eLpNorm (fun x => w.velocity (t, x)) 3 volume ≤
      ENNReal.ofReal A05.criticalL3Const *
        A05.dotHomogeneousENorm (1 / 2) (fun x => w.velocity (t, x)) := by
  apply A05.velocityCriticalL3
  refine ⟨D01.contDiff_slice w.velocity_smooth ht, ?_⟩
  intro m
  obtain ⟨G, _, hG⟩ := w.sobolev m
  exact ⟨G t, hG t ht⟩
