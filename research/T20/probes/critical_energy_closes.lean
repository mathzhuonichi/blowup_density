import NSFormalization.Section3.T20.CriticalEnergy

/-!
Exact target-shape and non-vacuity probe for T20 unit U8
(`criticalEnergy`, `03-torus.tex:420-440`, `eq:criticalenergy`).

§1 states the canonical field type with the structure constant `C₀` abstracted
and checks, by `exact`, (a) that it *is* the `criticalEnergy` field of every
`CriticalRegularityTAPI` (so the spelling below is verbatim, not a paraphrase)
and (b) that lane 415's `criticalEnergy` inhabits it at
`C₀ = criticalTrilinearConst` (lane 413's explicit constant).

§2 is the non-vacuity witness: the hypotheses of the field are simultaneously
inhabited by an actual force in `forceClassT` and an actual classical torus
solution from rest, and the conclusion at that instance produces an actual real
derivative witness.
-/

noncomputable section

namespace NSFormalization.Section3.T20.CriticalEnergyProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20
open scoped ContDiff ENNReal

/-! ## §1  The canonical field type, verbatim -/

/-- `Section3/T20/CriticalRegularity.lean:286-299`, the `criticalEnergy` field of
`CriticalRegularityTAPI`, with the structure constant `C₀` abstracted. -/
def criticalEnergyFieldType (C₀ : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - C₀ *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal

/-- The spelling above is the structure field itself. -/
example (API : CriticalRegularityTAPI) : criticalEnergyFieldType API.C₀ :=
  API.criticalEnergy

/-- **Lane 415's theorem inhabits the canonical field at
`C₀ = criticalTrilinearConst`.** -/
example : criticalEnergyFieldType criticalTrilinearConst := criticalEnergy

/-! ## §2  Non-vacuity -/

/-- The force class and the classical-solution-from-rest hypotheses are
simultaneously inhabited, on an actual positive horizon. -/
example :
    ∃ (g : SpaceTimeField) (_w : ClassicalSolutionT 1 (fun _ : Space ↦ 0) g 1),
      g ∈ forceClassT ∧ ((1 : ℝ) / 2) ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨(0 : SpaceTimeField), ?_, ?_, ⟨by norm_num, by norm_num⟩⟩
  · refine
      { velocity := fun _ ↦ (0 : Space)
        pressure := 0
        horizon_pos := zero_lt_one
        velocity_smooth := contDiff_const.contDiffOn
        pressure_smooth := contDiff_const.contDiffOn
        initial := fun _ ↦ rfl
        divergence := ?_
        momentum := ?_
        sobolev := ?_
        pressure_gradient := ?_
        velocity_periodic := fun _ _ _ _ ↦ rfl
        pressure_periodic := fun _ _ _ _ ↦ rfl
        pressure_gauge := ?_ }
    · intro t ht x
      simp [spatialDivergence, spatialDerivative]
    · intro t ht x
      simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
        temporalDerivative, advection, spatialDerivative, spatialLaplacian,
        pressureGradient]
    · intro m
      obtain ⟨A, hA⟩ := exists_periodicDatum_smooth (m : ℝ)
        (z := fun _ ↦ (0 : Space)) contDiff_const (fun _ _ ↦ rfl)
      exact ⟨fun _ ↦ A, continuous_const.continuousOn, fun _ _ ↦ hA⟩
    · intro t ht
      have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
        funext x
        simp [pressureGradient]
      rw [he]
      exact memLp_const (0 : Space)
    · intro t ht
      simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]
  · exact ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, by simp⟩

/-- At that instance the conclusion produces an actual derivative witness for
`(y²)'` and the displayed inequality. -/
example :
    ∃ (g : SpaceTimeField) (_hg : g ∈ forceClassT)
      (w : ClassicalSolutionT 1 (fun _ : Space ↦ 0) g 1) (E' : ℝ),
      HasDerivAt (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
          E' ((1 : ℝ) / 2) ∧
        E' / 2 +
            ((1 : ℝ) - criticalTrilinearConst *
              (criticalY (meanFreeVelocity g w.velocity) ((1 : ℝ) / 2)).toReal) *
              (criticalZ (meanFreeVelocity g w.velocity) ((1 : ℝ) / 2)).toReal ^ 2 ≤
          (criticalB (meanFreeForce g) ((1 : ℝ) / 2)).toReal *
            (criticalY (meanFreeVelocity g w.velocity) ((1 : ℝ) / 2)).toReal := by
  have hg : (0 : SpaceTimeField) ∈ forceClassT :=
    ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, by simp⟩
  refine ⟨(0 : SpaceTimeField), hg, ?_, ?_⟩
  · refine
      { velocity := fun _ ↦ (0 : Space)
        pressure := 0
        horizon_pos := zero_lt_one
        velocity_smooth := contDiff_const.contDiffOn
        pressure_smooth := contDiff_const.contDiffOn
        initial := fun _ ↦ rfl
        divergence := ?_
        momentum := ?_
        sobolev := ?_
        pressure_gradient := ?_
        velocity_periodic := fun _ _ _ _ ↦ rfl
        pressure_periodic := fun _ _ _ _ ↦ rfl
        pressure_gauge := ?_ }
    · intro t ht x
      simp [spatialDivergence, spatialDerivative]
    · intro t ht x
      simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
        temporalDerivative, advection, spatialDerivative, spatialLaplacian,
        pressureGradient]
    · intro m
      obtain ⟨A, hA⟩ := exists_periodicDatum_smooth (m : ℝ)
        (z := fun _ ↦ (0 : Space)) contDiff_const (fun _ _ ↦ rfl)
      exact ⟨fun _ ↦ A, continuous_const.continuousOn, fun _ _ ↦ hA⟩
    · intro t ht
      have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
        funext x
        simp [pressureGradient]
      rw [he]
      exact memLp_const (0 : Space)
    · intro t ht
      simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]
  · exact criticalEnergy 1 zero_lt_one (0 : SpaceTimeField) hg 1 _ ((1 : ℝ) / 2)
      ⟨by norm_num, by norm_num⟩

end NSFormalization.Section3.T20.CriticalEnergyProbe
