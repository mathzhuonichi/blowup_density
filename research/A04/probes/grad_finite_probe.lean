import NSFormalization.Section4.A03.OuterTameProduct
import NSFormalization.Section4.C01.VelocityJets
import NSFormalization.Section4.D01.SmoothDatum

noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
namespace ProbeGrad

open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.A03 (gradientSobolevENorm columnsSobolevENorm partialDeriv columnsSobolevENorm_le_sum)
open NSFormalization.Section4.D01 (sobolevENorm sobolevENorm_ne_top_of_contDiff_memLp)

theorem gradientSobolevENorm_velocity_ne_top {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    gradientSobolevENorm (m : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ := by
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hsl := NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht'
  have hcol : ∀ j : Fin 3,
      sobolevENorm (m : ℝ) (partialDeriv j (fun x : Space => w.velocity (t, x))) ≠ ⊤ := by
    intro j
    have hpj := NSFormalization.Section4.A03.SmoothL2.partialDeriv hsl j
    exact sobolevENorm_ne_top_of_contDiff_memLp hpj.1 hpj.2 (m : ℝ)
  have hle := columnsSobolevENorm_le_sum (m : ℝ)
    (fun j => partialDeriv j (fun x : Space => w.velocity (t, x)))
  refine ne_top_of_le_ne_top ?_ hle
  exact ENNReal.sum_ne_top.mpr (fun j _ => hcol j)

#print axioms gradientSobolevENorm_velocity_ne_top
end ProbeGrad
