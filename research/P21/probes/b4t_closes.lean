import NSFormalization.Section3.T11.H1Restart
import Bindings.TorusLocalTheory

noncomputable section
open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ENNReal

private theorem zeroForce : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, fun _ _ _ _ => rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
  simp

-- Non-vacuity: restart at 1/2 with explicit nonzero spatially constant datum e₀.
-- The returned solution retains that nonzero initial velocity and all-order regularity.
example : ∃ δ > 0,
    ∃ w : ClassicalSolutionT 1 (fun _ => coordinateVector 0)
      (timeShiftT (1 / 2) (0 : SpaceTimeField)) δ,
      PeriodicLocalRegularity 1 (fun _ => coordinateVector 0)
        (timeShiftT (1 / 2) (0 : SpaceTimeField)) δ w ∧
      w.velocity (0, 0) ≠ 0 := by
  let a : SpatialField := fun _ => coordinateVector 0
  have hK : periodicSobolevENorm 1 a ≠ ⊤ :=
    periodicSobolevENorm_ne_top_smooth 1 contDiff_const (fun _ _ => rfl)
  obtain ⟨δ, hδ, hr⟩ := h1RestartT 1 (by norm_num) 0 zeroForce
    1 (by norm_num) (periodicSobolevENorm 1 a) hK
  obtain ⟨w, hw⟩ := hr (1 / 2) (by constructor <;> norm_num) a
    (constantDatum_mem_initialClassT _) le_rfl
  refine ⟨δ, hδ, w, hw, ?_⟩
  rw [w.initial]
  change coordinateVector 0 ≠ 0
  intro he
  have hh := congrArg (fun x : Space => x (0 : Fin 3)) he
  norm_num [coordinateVector] at hh

-- Exact contract-vocabulary target of Targets.lean, transported through the
-- existing structure conversion; no contract or binding is changed.
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ ∈ Icc (0 : ℝ) S,
          ∀ (a' : SpatialField), a' ∈ initialClassT → periodicSobolevENorm 1 a' ≤ K →
            ∃ w : BlowupDensity.Contracts.V1.TorusLocalTheory.ClassicalSolutionT
              ν a' (timeShiftT t₀ f) δ,
              BlowupDensity.Contracts.V1.TorusLocalTheory.PeriodicLocalRegularity
                ν a' (timeShiftT t₀ f) δ w := by
  intro ν hν f hf S hS K hK
  obtain ⟨δ, hδ, hr⟩ := h1RestartT ν hν f hf S hS K hK
  refine ⟨δ, hδ, ?_⟩
  intro t₀ ht₀ a ha hnorm
  obtain ⟨w, hw⟩ := hr t₀ ht₀ a ha hnorm
  exact ⟨BlowupDensity.Bindings.TorusLocalTheory.toContract w,
    (BlowupDensity.Bindings.TorusLocalTheory.periodicLocalRegularity_toContract w).mpr hw⟩

-- Must-fail mutation: deleting the finite-ball hypothesis does not allow
-- specialization at K = infinity. The same application must be rejected.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : ∃ δ : ℝ, 0 < δ ∧ True := by
  obtain ⟨δ, hδ, _⟩ := h1RestartT 1 (by norm_num) 0 zeroForce 1 (by norm_num) ⊤ (by simp)
  exact ⟨δ, hδ, trivial⟩

-- Independent semantic check of the hypothesis removed by that mutation.
example : ¬ ((⊤ : ℝ≥0∞) ≠ ⊤) := by simp
