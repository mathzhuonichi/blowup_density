import research.P21.Targets
import NSFormalization.Section4.A04.H1Restart
import Bindings.LocalTheoryV2

/-! Exact registered target, concrete zero-data instance, and a bound-deletion mutation.
Build Targets.olean under tmp/research/P21, then add tmp to LEAN_PATH (see REPORT_507).
-/
noncomputable section
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4
open A02 A04
open D01 (sobolevENorm)
open scoped ENNReal ContDiff

namespace BlowupDensity.Research.P21.B4Probes

/-- The actual research target, transported through the existing solution/regularity conversions. -/
theorem registered_target : BlowupDensity.Research.P21.h1RestartR := by
  intro ν hν f hf S hS K hK
  obtain ⟨δ, hδ, hr⟩ := A04.h1RestartR ν hν f hf S hS K hK
  refine ⟨δ, hδ, ?_⟩
  intro t ht a ha hnorm
  obtain ⟨w, hw⟩ := hr t ht a ha hnorm
  exact ⟨BlowupDensity.Bindings.maximalPartial_ofA02 w,
    BlowupDensity.Bindings.localTheoryV2_regularity_ofA02 hw⟩

private theorem zero_force : MemForceR (fun _ => 0) := by
  refine ⟨contDiff_const.contDiffOn, ?_⟩
  intro m
  refine ⟨fun _ => 0, ?_, contDiffOn_const, ?_, ?_⟩
  · intro t _
    exact D01.isSobolevDatum_zero (m : ℝ)
  · exact MemLp.zero
  · exact MemLp.zero

private theorem zero_datum : (fun _ : Space => (0 : Space)) ∈ initialClassR := by
  refine ⟨⟨contDiff_const, fun m => ⟨0, D01.isSobolevDatum_zero (m : ℝ)⟩⟩, ?_⟩
  intro x
  simp [spatialDivergence, spatialDerivative]

/-- A concrete invocation with ν=1, zero force, S=1, and K=0. -/
example : ∃ δ > 0, ∀ t₀ ∈ Icc (0 : ℝ) 1,
    ∃ w : ClassicalSolutionR 1 (fun _ => 0) (timeShift t₀ (fun _ => 0)) δ,
      A01.ManuscriptLocalRegularity 1 (fun _ => 0) (timeShift t₀ (fun _ => 0)) δ w := by
  obtain ⟨δ, hδ, hr⟩ := A04.h1RestartR 1 (by norm_num) (fun _ => 0) zero_force
    1 (by norm_num) 0 (by simp)
  refine ⟨δ, hδ, fun t ht => hr t ht _ zero_datum ?_⟩
  rw [A03.sobolevENorm_eq (D01.isSobolevDatum_zero 1)]
  simp

/-- Mutation: deleting the H¹ bound prevents the same supplier application from typechecking. -/
example (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 ≤ S) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) S, ∀ a ∈ initialClassR,
      sobolevENorm 1 a ≤ K →
        ∃ w : ClassicalSolutionR ν a (timeShift t f) δ,
          A01.ManuscriptLocalRegularity ν a (timeShift t f) δ w := by
  obtain ⟨δ, hδ, hr⟩ := A04.h1RestartR ν hν f hf S hS K hK
  refine ⟨δ, hδ, ?_⟩
  intro t ht a ha hnorm
  fail_if_success (clear hnorm; exact hr t ht a ha (by assumption))
  exact hr t ht a ha hnorm

end BlowupDensity.Research.P21.B4Probes
