import NSFormalization.Section4.A01.SliceWiring

/-!
Reviewer probe (lane 157), **mutation 3**: is `hST : S < T` (classical horizon strictly above the
cylinder horizon) necessary, or would `S ≤ T` — in particular `T = S` — do?

Three parts:
* `endpoint_not_in_Ico` — a *proof* (not just an error) that at `T = S` the required slab
  membership `↑t ∈ Ico 0 T` genuinely FAILS at the right endpoint `t = S` of the pair's index
  `Icc 0 S`.  So the mutation is false, not merely unprovable-by-this-route.
* `control_lt` — with `S < T`, the membership holds for every `t : Icc 0 S` (positive control).
* `mutant_le` — the module's proof body with `hST : S ≤ T`.  Expected to FAIL.
-/

noncomputable section

namespace Rev157Mut3

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The mutation `T = S` is FALSE at the endpoint: `S ∉ Ico 0 S`, so neither `contDiff_slice` nor
`sobolevENorm_slice_ne_top` (both of which need `↑t ∈ Ico 0 T`) can be applied at `t = S`, which is
a genuine point of the pair's index `Icc 0 S`. -/
theorem endpoint_not_in_Ico (S : ℝ) (hS : 0 < S) :
    ∃ t : Icc (0 : ℝ) S, (↑t : ℝ) ∉ Ico (0 : ℝ) S :=
  ⟨⟨S, hS.le, le_rfl⟩, by simp⟩

/-- POSITIVE CONTROL — with `S < T` the membership holds at every `t`, endpoint included. -/
theorem control_lt {S T : ℝ} (hST : S < T) (t : Icc (0 : ℝ) S) : (↑t : ℝ) ∈ Ico (0 : ℝ) T :=
  ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩

/-- MUTANT — `hST : S ≤ T` instead of `S < T`, module body unchanged.  Expected to FAIL. -/
theorem mutant_le {q : ℕ} {ν : ℝ} {a : SpatialField}
    {f : SpaceTimeField} {S T : ℝ} (hST : S ≤ T) (w : ClassicalSolutionR ν a f T)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hslice : ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)) :
    ∀ t : Icc (0 : ℝ) S,
      ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t := by
  refine sobolevSpace_norm_le_sobolevNormAt u w.velocity
    (fun t => contDiff_slice w.velocity_smooth ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t => sobolevENorm_slice_ne_top w ⟨t.2.1, lt_of_le_of_lt t.2.2 hST⟩)
    (fun t n hn wrd => ?_)
  exact hword_jet_full (u t) (fun θ => hu θ t) (U t) (hU t)
    (C01.velocityField w hST t) (hslice t).symm n hn wrd

#print axioms endpoint_not_in_Ico
#print axioms control_lt

end Rev157Mut3
