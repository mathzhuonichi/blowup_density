import NSFormalization.Section4.A03.OuterTameProduct
import NSFormalization.Section4.C01.VelocityJets
import NSFormalization.Section4.D01.SmoothDatum

/-!
# A04: finiteness of the velocity gradient `H^m` norm on a classical solution

The fourth member of the finiteness family `Section4/A04/Continuity.lean`
(`sobolevENorm_velocity_ne_top`, `sobolevENorm_force_ne_top`) begins.  Those cover
the three `sobolevNormAt` slots of eq:Rhigh
(`paper/sections/appendix-a-local-theory.tex:132-137`); this module covers the
fourth quantity, the **gradient** `ℝ≥0∞` norm `A03.gradientSobolevENorm` whose
`.toReal` is `A04.gradientSobolevNormAt` (`LaplacianDatum.lean:86`).

`sobolevNormAt`/`gradientSobolevNormAt` are `ENNReal.toReal`, so a `⊤` value would
silently read as `0`.  For eq:Rhigh this matters on the **left**: the dissipation
`ν‖∇u‖²_{H^m}` would degenerate to `0` and the inequality would collapse to
`(1/2) d ≤ ‖f‖_{H^m}‖u‖_{H^m}`.  This lemma rules that out for the class the field
is quantified over: the gradient norm of a classical-solution velocity slice is a
genuine finite norm at every integer order and every interior time.

Proved for lane 133's `Contracts/V1/EnergyHighPartial.lean` `.toReal` disclosure.
Route (reconstructed from the lane-128 reviewer's `/tmp/rev128/p6_finite.lean`,
`research/A04/REVIEW_ENERGY_HIGH.md` §2(d); credit: lane-128 reviewer):

* the velocity slice is smooth with all jets in `L²`
  (`C01.velocity_slice_smoothL2`), hence so is each first partial `∂ⱼu(t,·)`
  (`A03.SmoothL2.partialDeriv`);
* a smooth `L²`-jet field has finite `H^m` datum norm
  (`D01.sobolevENorm_ne_top_of_contDiff_memLp`), so each of the three gradient
  columns `sobolevENorm (m) (∂ⱼu(t,·))` is `≠ ⊤`;
* the Frobenius assembly `gradientSobolevENorm = columnsSobolevENorm` is `≤` the
  sum of the three column norms (`A03.columnsSobolevENorm_le_sum`), a finite sum
  of finite terms (`ENNReal.sum_ne_top`).

`ClassicalSolutionR` is A02's (`Section4/A02/SolutionClass.lean`, byte-identical to
`Contracts/V1/Data.lean:624-648`).
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.A03
  (gradientSobolevENorm columnsSobolevENorm partialDeriv columnsSobolevENorm_le_sum)
open NSFormalization.Section4.D01 (sobolevENorm sobolevENorm_ne_top_of_contDiff_memLp)

/-- **The velocity gradient `H^m` norm is finite** at every integer order and every
interior time of a classical whole-space solution:
`gradientSobolevENorm (m) (u(t,·)) = ‖∇u(t,·)‖_{H^m} ≠ ⊤`.  The missing fourth
member of `Continuity.lean`'s finiteness family, and the guarantee that eq:Rhigh's
dissipation term `ν‖∇u‖²_{H^m}` is not a `⊤ ↦ 0` artefact.  Credit: lane-128
reviewer (`research/A04/REVIEW_ENERGY_HIGH.md` §2(d)). -/
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

end NSFormalization.Section4.A04
