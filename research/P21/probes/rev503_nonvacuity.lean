import NSFormalization.Section4.A04.H1Bridges

/-!
Reviewer non-vacuity probe for lane 503: the whole-space bridge applies to a
concrete nonzero smooth compactly supported field, and its registered H¹ norm
is finite rather than being hidden by `ENNReal.top.toReal = 0`.
-/

noncomputable section

namespace NSFormalization.Research.P21.Rev503

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal

def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def field : Space → Space := fun x => bump x • coordinateVector 0

theorem field_contDiff : ContDiff ℝ ∞ field :=
  (bump.contDiff (n := (⊤ : ℕ∞))).smul contDiff_const

theorem field_hasCompactSupport : HasCompactSupport field := by
  show HasCompactSupport ((fun r : ℝ => r • coordinateVector 0) ∘ (bump : Space → ℝ))
  exact bump.hasCompactSupport.comp_left (by simp)

theorem field_ne_zero : field 0 ≠ 0 := by
  have hb : bump 0 = 1 :=
    bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)
  simp [field, hb, coordinateVector]

example :
    sobolevENorm 1 field ≠ ⊤ ∧
      sobolevENorm 2 field ≠ ⊤ ∧
        (sobolevENorm 2 field).toReal ^ 2 =
          (sobolevENorm 1 field).toReal ^ 2 +
            NSFormalization.Section4.A04.gradientEnergyR field +
            NSFormalization.Section4.A04.hessianEnergyR field := by
  constructor
  · rw [NSFormalization.Section4.A03.sobolevENorm_eq
      (NSFormalization.Section4.A04.isSobolevDatum_compactAngularDatumR
        1 field_contDiff field_hasCompactSupport)]
    exact enorm_ne_top
  · constructor
    · rw [NSFormalization.Section4.A03.sobolevENorm_eq
        (NSFormalization.Section4.A04.isSobolevDatum_compactAngularDatumR
          2 field_contDiff field_hasCompactSupport)]
      exact enorm_ne_top
    · exact NSFormalization.Section4.A04.sobolevENorm_two_eq_one_add_gradient_hessian
        field_contDiff field_hasCompactSupport

end NSFormalization.Research.P21.Rev503
