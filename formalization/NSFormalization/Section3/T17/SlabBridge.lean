import NSFormalization.Section3.T17.Assembly

/-! The proposed slab bridge is false for the unchanged global
`CorrectionAPI.reference_periodic` field. -/
noncomputable section
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

def correctionStatementSlab : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn (Ico (0 : ℝ) (place.T + δ)) v →
    ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

/-- Zero on the classical slab, spatial identity at negative times. -/
def slabCounterexample : SpaceTimeField :=
  fun z => if 0 ≤ z.1 then 0 else z.2

theorem slabCounterexample_periodic (S : ℝ) :
    IsPeriodicOn (Ico (0 : ℝ) S) slabCounterexample := by
  intro t ht x i
  simp [slabCounterexample, ht.1]

theorem slabCounterexample_smooth (S : ℝ) :
    ContDiffOn ℝ ∞ slabCounterexample (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  apply (contDiffOn_const (c := (0 : Space))).congr
  intro z hz
  simp [slabCounterexample, hz.1.1]

theorem slabCounterexample_divergence (t : ℝ) (ht : 0 < t) (x : Space) :
    spatialDivergence slabCounterexample t x = 0 := by
  simp [spatialDivergence, spatialDerivative, slabCounterexample, ht.le]

theorem slabCounterexample_not_periodic :
    ¬ IsPeriodicOn univ slabCounterexample := by
  intro h
  have he := h (-1) (mem_univ _) 0 (0 : Fin 3)
  have hc := congrArg (fun x : Space => x (0 : Fin 3)) he
  norm_num [slabCounterexample, coordinateVector] at hc

/-- The exact requested statement contradicts its global periodicity field. -/
theorem not_correctionStatementSlab : ¬ correctionStatementSlab := by
  intro h
  obtain ⟨D, _, ⟨A⟩⟩ := h 1 0 0 0 ∅ Nonvacuity.place slabCounterexample
    (1 / 4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (slabCounterexample_periodic _) (slabCounterexample_smooth _)
    (fun t ht x _ => slabCounterexample_divergence t ht.1 x)
    (by simp) Subset.rfl
  exact slabCounterexample_not_periodic A.reference_periodic

end NSFormalization.Section3.T17
