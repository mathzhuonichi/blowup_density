import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets

/-!
# C01 unit U1 — velocity slices of a classical whole-space solution are `H^∞`

Task `collaboration/tasks/C01.md`, graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281`); this is unit **U1** of
`research/C01/COMPARISON.md:171`, the field `velocityJets` of the draft
specification `research/C01/Spec.lean:295-300`
(`BlowupDensity.C01.Draft.EnergyAbsorptionAPI`).

## What is proved

For a classical whole-space solution `u : ClassicalSolutionR ν a f T`
(`Contracts/V1/Data.lean:624-648`, restated in
`Section4/A02/SolutionClass.lean:100`) and every presingular time
`t ∈ [0,T)`, the velocity slice `u(t,·) = fun x => u.velocity (t, x)` lies in
both spellings of `H^∞(R³;R³)`:

* the **datum** form `MemHInfty` of `02-preliminaries.tex:12` eq:Rinitial
  (`Data.lean:495`, `A02.MemHInfty`), and
* the **jet** form `SmoothSquareIntegrableJets` on which the registered
  embedding contract `Contracts.V1.GradientL6` is stated (`GradientL6.lean:106`,
  restated as `A05.SmoothL2` in `Section4/A05/SmoothJets.lean:44` and as
  `D01.SmoothSquareIntegrableJets` in `Section4/D01/DatumToJets.lean:118`; all
  three are definitionally the contract predicate
  `ContDiff ℝ ∞ v ∧ ∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`).

## Route

This is the C01 clause `COMPARISON.md:171` rates `L` "because D01 unit L2's
datum ⟹ jet direction is open".  That direction is now closed: lane 025's
`D01.smoothSquareIntegrableJets_slice` (`DatumToJets.lean:396`) produces the jet
form of a velocity slice directly from `velocity_smooth` and the datum half of
`sobolev`, and lane 020/025's equivalence
`D01.memHInfty_iff_smoothSquareIntegrableJets` (`DatumToJets.lean:298`) recovers
the datum form from it.  Both are bound into the merged contract
`D01.datum_lemmas` as `solution_slice_smoothJets` and `memHInfty_iff_smoothJets`
(`verification/Bindings/DatumLemmas.lean`), so U1 is now `S`.

No `ContinuousOn`/time-regularity clause of `sobolev` is used: the `.imp` below
discards it, exactly as `smoothSquareIntegrableJets_slice`'s hypothesis shape
(`DatumToJets.lean:396-401`) requires.
-/

noncomputable section

namespace NSFormalization.Section4.C01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- **C01 unit U1, the field `velocityJets` of `research/C01/Spec.lean:295`.**
Every velocity slice `u(t,·)`, `t ∈ [0,T)`, of a classical whole-space solution
is an `H^∞(R³;R³)` field in both the datum form `A02.MemHInfty`
(definitionally `Contracts.V1.Data.MemHInfty`) and the jet form `A05.SmoothL2`
(definitionally `Contracts.V1.SmoothSquareIntegrableJets`).

Only `velocity_smooth` (`Data.lean:632`) and the datum half of `sobolev`
(`Data.lean:643`) are used; the `ContinuousOn` conjunct of `sobolev` is
discarded. -/
theorem velocity_slice_memHInfty_and_smoothL2 {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T : ℝ} (u : A02.ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    A02.MemHInfty (fun x : Space => u.velocity (t, x)) ∧
      A05.SmoothL2 (fun x : Space => u.velocity (t, x)) := by
  have hjets : D01.SmoothSquareIntegrableJets (fun x : Space => u.velocity (t, x)) :=
    D01.smoothSquareIntegrableJets_slice u.velocity_smooth
      (fun m => (u.sobolev m).imp fun _ h => h.2) ht
  exact ⟨D01.memHInfty_iff_smoothSquareIntegrableJets.mpr hjets, hjets⟩

/-- The datum-form half of `velocity_slice_memHInfty_and_smoothL2`, packaged
separately for consumers that want only `MemHInfty`. -/
theorem velocity_slice_memHInfty {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T : ℝ} (u : A02.ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    A02.MemHInfty (fun x : Space => u.velocity (t, x)) :=
  (velocity_slice_memHInfty_and_smoothL2 u ht).1

/-- The jet-form half of `velocity_slice_memHInfty_and_smoothL2`, the hypothesis
of the registered `A05.gradient_l6` and `A05.hessianLaplacianIdentity`. -/
theorem velocity_slice_smoothL2 {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T : ℝ} (u : A02.ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    A05.SmoothL2 (fun x : Space => u.velocity (t, x)) :=
  (velocity_slice_memHInfty_and_smoothL2 u ht).2

end NSFormalization.Section4.C01
