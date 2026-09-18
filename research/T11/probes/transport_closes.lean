import NSFormalization.Section3.T11.Transport

/-! # Target-shape and non-vacuity probe for T11/U6 (lane 331)

The three target fields of `research/T11/probes/api_on_canonical.lean` are
`transformed_solution` (of `PeriodicMeanReductionAPI`), `to_unit` and
`from_unit` (of `PeriodicViscosityRescalingAPI`).  Each body below is copied
verbatim from that file.

* `to_unit` and `from_unit` close from `Transport` once the **given** solution's
  `PeriodicLocalRegularity` is supplied.  The field statements quantify over an
  arbitrary `ClassicalSolutionT`, whose `sobolev` field carries only a
  `ContinuousOn` datum path, so that record cannot be produced for the
  transported solution without one for the source: the residual is exactly the
  hypothesis `hregular` below.
* `transformed_solution` closes verbatim except for its
  `PeriodicLocalRegularity` conjunct, whose `sobolev_smooth` clause is the
  residual (`pressure_poisson` and `projected` do transport; see
  `REPORT_331.md` §3).
-/

noncomputable section

namespace NSFormalization.Section3.T11.TransportProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T11.Transport
open scoped ContDiff ENNReal

/-! ## 1. `to_unit`, verbatim -/

example
    (hregular : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            NSFormalization.Section3.T11.PeriodicLocalRegularity
              1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v := by
  intro ν hν a ha f hf T w
  exact to_unit_of_regularity ν hν a ha f hf T w (hregular ν hν a ha f hf T w)

/-! ## 2. `from_unit`, verbatim -/

example
    (hregular : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w)
    (hclass : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧ unitViscosityForceT ν f ∈ forceClassT) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              NSFormalization.Section3.T11.PeriodicLocalRegularity ν a f T w := by
  intro ν hν a ha f hf T v
  refine from_unit_of_regularity ν hν a ha f hf T v ?_
  exact hregular 1 one_pos _ (hclass ν hν a ha f hf).1 _ (hclass ν hν a ha f hf).2 (ν * T) v

/-! ## 3. `transformed_solution` minus its regularity conjunct, verbatim -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure := by
  intro ν hν a ha f hf T w
  obtain ⟨v, hvel, hpre, _⟩ := transformed_solution_fields ν hν a ha f hf T w
  exact ⟨v, hvel, hpre⟩

/-- Two of the three `PeriodicLocalRegularity` clauses transport as well. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          PeriodicLocalRegularity ν a f T w →
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
              scalarSpatialLaplacianT v.pressure t x =
                spatialDivergence (galileanForceT a f) t x -
                  spatialDivergence
                    (fun z : SpaceTime ↦ convectionDivergenceT v.velocity z.1 z.2) t x) ∧
            (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
              temporalDerivative v.velocity t x - ν • spatialLaplacian v.velocity t x =
                (galileanForceT a f (t, x) - convectionDivergenceT v.velocity t x) -
                  pressureGradient v.pressure t x) :=
  transformed_solution_two_clauses

/-! ## 4. Non-vacuity: a genuinely nonzero solution and its two transports -/

/-- The constant flow `u ≡ e₀` at viscosity `ν` on `[0,1)` with zero force. -/
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

/-- The transport machinery applies to a nonzero solution: the unit-viscosity
rescaling of the constant flow at `ν = 2` is again nonzero and lives on the
dilated horizon, while the Galilean transform removes exactly its mean. -/
example :
    ∃ (w : ClassicalSolutionT 2 (fun _ ↦ coordinateVector 0) 0 1)
      (hν : (0 : ℝ) < 2),
      w.velocity (0, 0) ≠ 0 ∧
      (classicalSolutionT_toUnit hν w).velocity (0, 0) ≠ 0 ∧
      (classicalSolutionT_galilean contDiff_const w).velocity (0, 0) = 0 := by
  refine ⟨constantFlow 2, two_pos, coordinateVector_ne_zero, ?_, ?_⟩
  · rw [classicalSolutionT_toUnit_velocity]
    change (2 : ℝ)⁻¹ • (coordinateVector 0 : Space) ≠ 0
    simpa using coordinateVector_ne_zero
  · change (coordinateVector 0 : Space) -
      galileanMeanT (fun _ ↦ coordinateVector 0) (0 : SpaceTimeField) 0 = 0
    rw [galileanMeanT_zero]
    have hmean : meanT (fun _ : Space ↦ (coordinateVector 0 : Space)) = coordinateVector 0 := by
      simp [meanT, torusLift, NSFormalization.Paper1.torusLift]
    rw [hmean, sub_self]

end NSFormalization.Section3.T11.TransportProbe
