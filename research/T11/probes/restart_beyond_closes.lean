import NSFormalization.Section3.T11.RestartBeyond

/-! Exact target-shape and non-vacuity probe for T11/U13 (`restartBeyond`).

The first `example` is the `restartBeyond` field of `PeriodicContinuationAPI`
copied verbatim from `research/T11/probes/api_on_canonical.lean`, discharged by
the module theorem under the one named input `PeriodicQuantitativeLocalInput'`
(the same input lane 321 consumes through `restart`). -/

noncomputable section

namespace NSFormalization.Section3.T11.RestartBeyondProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

/-- **Target.** The `PeriodicContinuationAPI.restartBeyond` field copied
verbatim from `api_on_canonical.lean`: `∃ δ > 0` *before* the datum, hence
uniform over the `H¹` ball `K`. -/
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) := by
  exact restartBeyond H

/-- **Export for U14/U16.** The gluing constructor, with its agreement
conclusion on the whole of the first chart `[0, T)`. -/
example {ν T b L : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (w : ClassicalSolutionT ν a f T) (hb : b ∈ Ico (0 : ℝ) T)
    (w₂ : ClassicalSolutionT ν (fun x => w.velocity (b, x)) (timeShiftT b f) L)
    (hTL : T < b + L) :
    ∃ v : ClassicalSolutionT ν a f (b + L),
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, v.velocity (t, x) = w.velocity (t, x)) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, v.pressure (t, x) = w.pressure (t, x)) := by
  exact glueClassicalSolutionT hν w hb w₂ hTL

/-- **Export.** Interior restart data: every interior velocity slice is an
admissible initial datum for the shifted problem. -/
example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {b : ℝ} (hb : b ∈ Ico (0 : ℝ) T) :
    (fun x => w.velocity (b, x)) ∈ initialClassT :=
  velocitySlice_mem_initialClassT w hb

/-- **Export.** The time translation of a classical torus solution to an
interior basepoint solves the shifted problem. -/
example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (b : ℝ) (hb : b ∈ Ico (0 : ℝ) T) :
    ClassicalSolutionT ν (fun x => w.velocity (b, x)) (timeShiftT b f) (T - b) :=
  shiftedSolutionT w b hb

/-- **Export.** Restriction to a shorter horizon keeps both fields literally. -/
example {ν T T' : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hT' : 0 < T') (hle : T' ≤ T) :
    (restrictClassicalSolutionT w hT' hle).velocity = w.velocity ∧
      (restrictClassicalSolutionT w hT' hle).pressure = w.pressure :=
  ⟨rfl, rfl⟩

/-- **Non-vacuity of the `SolvesBelowT` hypothesis.** It is inhabited by a
genuinely nonzero solution driven by a nonzero smooth periodic force, so the
`restartBeyond` premise is not vacuous. -/
example :
    ∃ (a : SpatialField) (g : SpaceTimeField) (u : SpaceTimeField)
      (p : SpaceTimeScalar),
      a ∈ initialClassT ∧ SolvesBelowT 1 a g 1 u p ∧
        u (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨-, -, a, g, -, -, ha, -, -, -, -, w, -, hw0, hg0⟩ := nonzero_forced_witness'
  exact ⟨a, g, w.velocity, w.pressure, ha, solvesBelowT_of_classicalSolutionT w, hw0, hg0⟩

/-- **Non-vacuity of the glued conclusion.** The two charts really do paste
into a classical solution on a strictly longer horizon whose velocity at the
origin is nonzero; the conclusion is not satisfied by the zero field. -/
example :
    ∃ (a : SpatialField) (g : SpaceTimeField)
      (v : ClassicalSolutionT 1 a g ((1 : ℝ) / 4 + (1 - 1 / 4))),
      v.velocity (0, 0) ≠ 0 := by
  obtain ⟨-, -, a, g, -, -, -, -, -, -, -, w, -, hw0, -⟩ := nonzero_forced_witness'
  have hb : (1 : ℝ) / 4 ∈ Ico (0 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hb1 : (1 : ℝ) / 4 ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨v, hvv, -⟩ := glueClassicalSolutionT one_pos
    (restrictClassicalSolutionT w (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 ≤ 1))
    hb (shiftedSolutionT w (1 / 4) hb1) (by norm_num)
  exact ⟨a, g, v, by rw [hvv 0 ⟨le_rfl, by norm_num⟩ 0]; exact hw0⟩

end NSFormalization.Section3.T11.RestartBeyondProbe
