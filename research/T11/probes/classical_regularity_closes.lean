import NSFormalization.Section3.T11.ClassicalRegularity

/-! # Target-shape and non-vacuity probe for T11/U6b (lane 339)

`periodicLocalRegularity_of_classical` is the residual hypothesis recorded by
lanes 331 (`research/T11/REPORT_331.md` §3) and 321.  With it proved, three
fields of `research/T11/probes/api_on_canonical.lean` close unconditionally —
`transformed_solution` of `PeriodicMeanReductionAPI`, `to_unit` and `from_unit`
of `PeriodicViscosityRescalingAPI` — and so does the `regularity` field of
`PeriodicLocalTheoryAPI` for an arbitrary selected solution family.  Every
statement below is copied verbatim from that file (respectively from
`Section3/T11/Restart.lean`'s `PeriodicLocalTheoryInitialAPI.regularity`).

The last section exhibits a genuinely nonzero solution for which the record is
inhabited and whose order-`m` datum path is nonzero at the initial time, so the
`sobolev_smooth` clause is not vacuously satisfied by the zero datum.
-/

noncomputable section

namespace NSFormalization.Section3.T11.ClassicalRegularityProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T11.Transport
open scoped ContDiff ENNReal

/-! ## 0. The residual of lanes 331 and 321, discharged -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f T w :=
  periodicLocalRegularity_of_classical

/-! ## 1. `PeriodicViscosityRescalingAPI.to_unit`, verbatim -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            NSFormalization.Section3.T11.PeriodicLocalRegularity
              1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v :=
  NSFormalization.Section3.T11.to_unit

/-! ## 2. `PeriodicViscosityRescalingAPI.from_unit`, verbatim -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f T w :=
  NSFormalization.Section3.T11.from_unit

/-! ## 3. `PeriodicMeanReductionAPI.transformed_solution`, verbatim -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            NSFormalization.Section3.T11.PeriodicLocalRegularity ν (meanZeroPartT a)
              (galileanForceT a f) T v :=
  NSFormalization.Section3.T11.transformed_solution

/-! ## 4. `PeriodicLocalTheoryAPI.regularity`, for an arbitrary selected family -/

example (horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
    (solution : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ClassicalSolutionT ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
      (f : SpaceTimeField) (hf : f ∈ forceClassT),
        NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f (horizon ν a f)
          (solution ν hν a ha f hf) :=
  regularity_of_solution horizon solution

/-! ## 5. Non-vacuity: a nonzero constant flow with a nonzero datum path -/

/-- The constant flow `u ≡ e₀` at viscosity `ν` on `[0,1)` with zero force
(lane 331's witness, `research/T11/probes/transport_closes.lean`). -/
def constantFlow (ν : ℝ) : ClassicalSolutionT ν (fun _ ↦ coordinateVector 0) 0 1 := by
  refine
    { velocity := fun _ ↦ coordinateVector 0
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
  · intro t _ x
    simp [spatialDivergence, spatialDerivative]
  · intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  · intro m
    exact ⟨fun _ ↦ constantDatum (m : ℝ) (coordinateVector 0), continuous_const.continuousOn,
      fun _ _ ↦ isPeriodicDatum_const _ _⟩
  · intro t _
    have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    exact memLp_const (0 : Space)
  · intro t _
    simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]

theorem coordinateVector_ne_zero : (coordinateVector 0 : Space) ≠ 0 := by
  intro h
  have h₀ := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
  simp [coordinateVector] at h₀

/-- The regularity record holds for a solution whose velocity is nonzero, and every
datum path it produces is nonzero at the initial time. -/
example :
    ∃ (w : ClassicalSolutionT 2 (fun _ ↦ coordinateVector 0) 0 1),
      NSFormalization.Section3.T11.PeriodicLocalRegularity
        2 (fun _ ↦ coordinateVector 0) 0 1 w ∧
      w.velocity (0, 0) ≠ 0 ∧
      ∀ (m : ℕ) (G : ℝ → PeriodicSobolev (m : ℝ)),
        IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) 1) w.velocity G → G 0 ≠ 0 := by
  have hzero : ContDiff ℝ ∞ (0 : SpaceTimeField) := contDiff_const
  refine ⟨constantFlow 2, periodicLocalRegularity_of_classical' hzero _,
    coordinateVector_ne_zero, ?_⟩
  intro m G hG
  have hG0 := hG 0 ⟨le_rfl, zero_lt_one⟩
  intro hzeroG
  have hentry := hG0.2.2 0 0
  rw [hzeroG] at hentry
  have hcoeff : periodicFourierCoeff
      (fun x : Space ↦ (((constantFlow 2).velocity (0, x) 0 : ℝ) : ℂ)) 0 = 1 := by
    have hfun : (fun x : Space ↦ (((constantFlow 2).velocity (0, x) 0 : ℝ) : ℂ)) =
        fun _ : Space ↦ (1 : ℂ) := by
      funext x
      simp [constantFlow, coordinateVector]
    rw [hfun, periodicFourierCoeff_const]
    simp
  rw [hcoeff] at hentry
  have hw : periodicFrequencyWeight (0 : PeriodicFrequency) = 1 := by
    simp [periodicFrequencyWeight]
  rw [hw, Real.one_rpow] at hentry
  simp at hentry

end NSFormalization.Section3.T11.ClassicalRegularityProbe
