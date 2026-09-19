import NSFormalization.Section3.T17.SlabBridge2

noncomputable section
namespace NSFormalization.Section3.T17.Rev460Mutation

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

/-- Substantive mutation of the continuation statement: delete the global
periodicity hypothesis while keeping every other binder and conclusion. -/
def correctionStatementSlab_noGlobalPeriodicity : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

/-- The mutation is false, witnessed by the original lane's reference that is
zero on the positive slab and nonperiodic at negative times. -/
theorem not_correctionStatementSlab_noGlobalPeriodicity :
    ¬ correctionStatementSlab_noGlobalPeriodicity := by
  intro h
  obtain ⟨D, _, ⟨A⟩⟩ := h 1 0 0 0 ∅ Nonvacuity.place slabCounterexample
    (1 / 4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((slabCounterexample_smooth _).mono
      (prod_mono Ioo_subset_Ico_self Subset.rfl))
    (fun t ht x _ => slabCounterexample_divergence t ht.1 x)
    (by simp) Subset.rfl
  exact slabCounterexample_not_periodic A.reference_periodic

-- Expected reviewer failure: the existing proof cannot inhabit the mutated
-- statement because no term of `IsPeriodicOn univ v` is available.
example : correctionStatementSlab_noGlobalPeriodicity := by
  intro ν u p f K place v r δ hν hr hr2 hδ hv hdiv hsupp hball
  exact correctionStatementSlab'_holds ν u p f K place v r δ
    hν hr hr2 hδ hv hdiv hsupp hball

end NSFormalization.Section3.T17.Rev460Mutation
