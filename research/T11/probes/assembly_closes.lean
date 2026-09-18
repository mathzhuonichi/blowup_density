import NSFormalization.Section3.T11.Assembly

/-! # Lane 340 (U17) probe — every specification field, closed by name

Each `example` below is a field of one of the five structures of
`research/T11/probes/api_on_canonical.lean` copied verbatim, discharged by a
projection of the assembled term in `Section3/T11/Assembly.lean`.  The two
`H¹`-ball fields of `PeriodicContinuationAPI` are discharged **only** from the
named predicates `PeriodicRestartH1` / `PeriodicRestartBeyondH1`, which is
exactly the gap recorded in `research/T11/H1_GAP.md`; the corresponding `H³`
fields are discharged unconditionally. -/

noncomputable section

namespace NSFormalization.Section3.T11.AssemblyProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators

/-! ## `PeriodicLocalTheoryAPI` (8 fields) -/

example : ℝ → SpatialField → SpaceTimeField → ℝ :=
  periodicLocalTheoryAPI.horizon

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (periodicLocalTheoryAPI.horizon ν a f) :=
  periodicLocalTheoryAPI.solution

example : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (periodicLocalTheoryAPI.horizon ν a f)
        (periodicLocalTheoryAPI.solution ν hν a ha f hf) :=
  periodicLocalTheoryAPI.regularity

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x) :=
  periodicLocalTheoryAPI.velocity_unique

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x) :=
  periodicLocalTheoryAPI.pressure_unique

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ENNReal.ofReal (periodicLocalTheoryAPI.horizon ν a f) ≤
          maximalLifespanT ν a f :=
  periodicLocalTheoryAPI.horizon_le_lifespan

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p :=
  periodicLocalTheoryAPI.exists_maximal

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x) :=
  periodicLocalTheoryAPI.maximal_unique

/-! ## `PeriodicContinuationAPI` (5 fields): three unconditional, two only from
the named `H¹` predicates -/

/-- `higherOrderBound`, verbatim, unconditional. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M :=
  periodicContinuationH3API.higherOrderBound

/-- `extendsBeyond`, verbatim, unconditional. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p :=
  periodicContinuationH3API.extendsBeyond

/-- `lifespanInfiniteOfLocallyFinite`, verbatim, unconditional. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤ :=
  periodicContinuationH3API.lifespanInfiniteOfLocallyFinite

/-- `restart` at the **`H³`** ball: proved. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w :=
  periodicContinuationH3API.restart

/-- `restartBeyond` at the **`H³`** ball: proved. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 3 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) :=
  periodicContinuationH3API.restartBeyond

/-- `restart` at the manuscript's **`H¹`** ball: available only from the named
predicate.  The binder is the whole content of the gap. -/
example (h₁ : PeriodicRestartH1) (h₂ : PeriodicRestartBeyondH1) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w :=
  (periodicContinuationAPI_of_h1 h₁ h₂).restart

/-- `restartBeyond` at the manuscript's **`H¹`** ball: same. -/
example (h₁ : PeriodicRestartH1) (h₂ : PeriodicRestartBeyondH1) :
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
                        v.pressure (t, x) = p (t, x)) :=
  (periodicContinuationAPI_of_h1 h₁ h₂).restartBeyond

/-! ## `PeriodicMeanReductionAPI` (6 fields) -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t :=
  periodicMeanReductionAPI.mean_formula

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t :=
  periodicMeanReductionAPI.mean_derivative

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            PeriodicLocalRegularity ν (meanZeroPartT a)
              (galileanForceT a f) T v :=
  periodicMeanReductionAPI.transformed_solution

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT :=
  periodicMeanReductionAPI.transformed_classes

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          meanT (meanZeroPartT a) = 0 ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanVelocityT a f w.velocity (t, x)) = 0) ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanForceT a f (t, x)) = 0) :=
  periodicMeanReductionAPI.transformed_mean_zero

example : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z :=
  periodicMeanReductionAPI.translation_preserves_sobolev

/-! ## `PeriodicViscosityRescalingAPI` (4 fields) -/

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT :=
  periodicViscosityRescalingAPI.scaled_classes

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f :=
  periodicViscosityRescalingAPI.inverse_identities

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v :=
  periodicViscosityRescalingAPI.to_unit

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              PeriodicLocalRegularity ν a f T w :=
  periodicViscosityRescalingAPI.from_unit

/-! ## Non-vacuity -/

/-- The assembled package applies to a genuine nonzero datum and a nonzero
compactly supported positive-time force. -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField) (ha : a ∈ initialClassT)
      (hf : f ∈ forceClassT),
      a 0 ≠ 0 ∧ f (2, 0) ≠ 0 ∧
      0 < periodicLocalTheoryAPI.horizon 1 a f ∧
      (periodicLocalTheoryAPI.solution 1 one_pos a ha f hf).velocity (0, 0) ≠ 0 :=
  periodicLocalTheoryAPI_nonvacuous

end NSFormalization.Section3.T11.AssemblyProbe
