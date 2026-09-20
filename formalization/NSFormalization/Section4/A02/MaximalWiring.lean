import NSFormalization.Section4.A02.Maximal
import NSFormalization.Section4.A01.LocalTheoryBundle

/-! # A01 local existence wired to the A02 maximal solution
No local-existence hypothesis is retained. Quantitative restart is separate.
-/
noncomputable section
namespace NSFormalization.Section4.A02
open Set
open NavierStokes.ProblemStatement (Space)
open scoped ENNReal

/-- The manuscript maximal-existence field with A01 supplied. -/
theorem exists_maximal' :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p :=
  exists_maximal_of_localSolution A01.localHorizon'
    (fun ν a f hν ha hf => (A01.localCarrier ν a f hν ha hf).w)

/-- The selected A01 horizon is below the maximal lifespan. -/
theorem horizon_le_lifespan' (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    ENNReal.ofReal (A01.localHorizon' ν a f) ≤ maximalLifespanR ν a f :=
  horizon_le_lifespan (A01.localCarrier ν a f hν ha hf).w

/-- Admissible data have strictly positive lifespan. -/
theorem maximalLifespanR_pos (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) :
    0 < maximalLifespanR ν a f := by
  obtain ⟨u, p, hu⟩ := exists_maximal' ν a f hν ha hf
  exact hu.1

/-- Access a classical representative on a horizon strictly beyond a presingular time. -/
theorem IsMaximalSolution.exists_solution_after {ν : ℝ} {a : SpatialField}
    {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hu : IsMaximalSolution ν a f u p) {t : ℝ} (ht : t ∈ presingularTimes ν a f) :
    ∃ S : ℝ, t < S ∧ ∃ w : ClassicalSolutionR ν a f S,
      w.velocity = u ∧ w.pressure = p := by
  obtain ⟨S, htS, hw⟩ := exists_horizon_gt_of_lt_lifespan ht.1 ht.2
  have hmid : 0 < (t + S) / 2 := by linarith [ht.1]
  have hlt : ENNReal.ofReal ((t + S) / 2) < maximalLifespanR ν a f :=
    ((ENNReal.ofReal_lt_ofReal_iff hw.some.horizon_pos).mpr (by linarith)).trans_le
      (horizon_le_lifespan hw.some)
  exact ⟨(t + S) / 2, by linarith, hu.2 _ hmid hlt⟩

/-- Every classical velocity slice is admissible restart data. -/
theorem ClassicalSolutionR.restart_datum {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (fun x : Space => w.velocity (t, x)) ∈ initialClassR := by
  refine ⟨⟨D01.contDiff_slice w.velocity_smooth ht, ?_⟩, ?_⟩
  · intro m
    obtain ⟨G, _, hG⟩ := w.sobolev m
    exact ⟨G t, hG t ht⟩
  · exact w.divergence t ht

/-- The `MaximalSolutionAPI.restart_datum` accessor. -/
theorem restart_datum (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (_hν : 0 < ν) (_ha : a ∈ initialClassR) (_hf : MemForceR f)
    (u : SpaceTimeField) (p : SpaceTimeScalar) (hu : IsMaximalSolution ν a f u p)
    (t : ℝ) (ht : t ∈ presingularTimes ν a f) :
    (fun x : Space => u (t, x)) ∈ initialClassR := by
  obtain ⟨S, htS, w, hw, _⟩ := hu.exists_solution_after ht
  rw [← hw]
  exact w.restart_datum ⟨ht.1, htS⟩

end NSFormalization.Section4.A02
