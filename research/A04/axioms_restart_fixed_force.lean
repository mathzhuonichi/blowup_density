import NSFormalization.Section4.A04.RestartFixedForce
import NSFormalization.Section4.A04.ZeroSolution

open Set
open NSFormalization.Section4
open A02 A04
open scoped ENNReal

#print axioms RestartFixedForce
#print axioms referenceForce_timeShift_norm_le
#print axioms restartFixedForce_of_memForceR
#print axioms shiftedSolution
#print axioms compact_hSeven_bound
#print axioms exists_carrier_window
#print axioms classical_hasSmoothSobolevPath
#print axioms localCarrier_gronwall_bound
#print axioms running_hTwo_integral_le
#print axioms higherOrderBound_of_gronwall
#print axioms ShiftedLocalExtension
#print axioms restartBeyond_fixed
#print axioms extendsBeyond_fixed
#print axioms extendsBeyond_of_memForceR
#print axioms lifespanInfiniteOfLocallyFinite_fixed
#print axioms lifespanInfiniteOfLocallyFinite_of_memForceR

-- Check the unchanged G3 statement, including all orders and Ico rather than Icc.
example : HigherOrderBound =
    (∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      ∀ S : ℝ, 0 < S → ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        SolvesBelow ν a f S u p → squaredHTwoIntegral S u ≠ ⊤ →
        ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) S,
          D01.sobolevENorm (m : ℝ) (fun x => u (t, x)) ≤ M) := rfl

-- One window works for every restart time, on actual zero-solution data.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    δ ≤ A01.localHorizon' 1
      (fun x => (zeroSol 1 2 (by norm_num) (by norm_num)).velocity (t, x))
      (timeShift t (0 : SpaceTimeField)) := by
  obtain ⟨δ, hδ, hr⟩ := restartFixedForce_of_memForceR 1 (by norm_num)
    0 memForceR_zero 1 (by norm_num) 0 (by simp)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  apply hr t ht _
    ((zeroSol 1 2 (by norm_num) (by norm_num)).restart_datum
      ⟨ht.1, by linarith [ht.2]⟩)
  change D01.sobolevENorm 7 (fun _ => 0) ≤ 0
  rw [sobolevENorm_eq (D01.isSobolevDatum_zero 7)]
  simp

-- G3 is instantiated on a nonempty family of actual classical solutions.
example (m : ℕ) : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) 1,
    D01.sobolevENorm (m : ℝ)
      (fun x => (zeroSol 1 1 (by norm_num) (by norm_num)).velocity (t, x)) ≤ M := by
  apply higherOrderBound_of_gronwall 1 0 0 (by norm_num) zero_mem_initialClassR
    memForceR_zero (memL1Hm_of_memForceR memForceR_zero) 1 (by norm_num)
    (0 : SpaceTimeField) (0 : SpaceTimeScalar)
  · intro b hb _
    exact ⟨zeroSol 1 b (by norm_num) hb, rfl, rfl⟩
  · simp [squaredHTwoIntegral, sobolevENorm_eq (D01.isSobolevDatum_zero 2)]

-- The isolated extension conclusion is satisfiable for genuine solutions.
example (b L : ℝ) (hb : 0 ≤ b) (hL : 0 < L) :
    ENNReal.ofReal (b + L) ≤ maximalLifespanR 1 0 0 :=
  horizon_le_lifespan (zeroSol 1 (b + L) (by norm_num) (by linarith))
