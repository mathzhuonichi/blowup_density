import NSFormalization.Section3.T17.SlabBridge2

/-! The exact T19 input: zero extension of a classical periodic reference.
The original negative regression is retained at the end. -/
noncomputable section
namespace NSFormalization.Section3.T17.SlabClassicalProbe
open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open scoped ContDiff Topology

def v_ext {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) : SpaceTimeField :=
  fun z => if z.1 ∈ Ico (0 : ℝ) S then reference.velocity z else 0

theorem v_ext_periodic {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) : IsPeriodicOn univ (v_ext reference) := by
  intro t _ x i
  by_cases ht : t ∈ Ico (0 : ℝ) S
  · simpa only [v_ext, ite_eq_left ht] using reference.velocity_periodic t ht x i
  · simp only [v_ext, ite_eq_right ht]

theorem v_ext_smooth {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) :
    ContDiffOn ℝ ∞ (v_ext reference) (Ioo (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  apply (reference.velocity_smooth.mono
    (prod_mono Ioo_subset_Ico_self Subset.rfl)).congr
  intro z hz
  simp only [v_ext, ite_eq_left (show z.1 ∈ Ico (0 : ℝ) S from ⟨hz.1.1.le, hz.1.2⟩)]

theorem v_ext_divergence {ν S : ℝ} {a : SpatialField} {g : SpaceTimeField}
    (reference : ClassicalSolutionT ν a g S) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S)
    (x : Space) : spatialDivergence (v_ext reference) t x = 0 := by
  have ht' : t ∈ Ico (0 : ℝ) S := ⟨ht.1.le, ht.2⟩
  simpa only [spatialDivergence, spatialDerivative, v_ext, ite_eq_left ht'] using
    reference.divergence t ht' x

theorem correction_from_classical (ν : ℝ) (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) (place : PlacementData u p f K)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (hν : 0 < ν) (hr : 0 < r) (hr2 : r < 1 / 2) (hδ : 0 < δ)
    (hsupp : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K)
    (hball : ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius) :
    ∃ D : CutoffData,
      LocalPotentialAPI (v_ext reference) u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place (v_ext reference) r δ D) := by
  exact correctionStatementSlab'_holds ν u p f K place (v_ext reference) r δ
    hν hr hr2 hδ (v_ext_periodic reference) (v_ext_smooth reference)
    (fun t ht x _ => v_ext_divergence reference t ht x) hsupp hball

example : ¬ correctionStatementSlab := not_correctionStatementSlab

example : ¬ ∃ D : CutoffData,
    Nonempty (CorrectionAPI 1 Nonvacuity.place slabCounterexample (1 / 4) 1 D) := by
  rintro ⟨D, ⟨A⟩⟩
  exact slabCounterexample_not_periodic A.reference_periodic

end NSFormalization.Section3.T17.SlabClassicalProbe

/-- info: 'NSFormalization.Section3.T17.SlabClassicalProbe.v_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.SlabClassicalProbe.v_ext

/-- info: 'NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_periodic

/-- info: 'NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_smooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_smooth

/-- info: 'NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.SlabClassicalProbe.v_ext_divergence

/-- info: 'NSFormalization.Section3.T17.SlabClassicalProbe.correction_from_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms NSFormalization.Section3.T17.SlabClassicalProbe.correction_from_classical
