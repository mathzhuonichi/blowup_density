import NSFormalization.Section3.T11.HighOrder

/-!
# U12 probe — the `higherOrderBound` target closes

The statement below is the `higherOrderBound` field of `PeriodicContinuationAPI`
copied **verbatim** from `research/T11/probes/api_on_canonical.lean:112-121`
(same binder order, same vocabulary, nothing weakened).  It closes from
`HighOrder.higherOrderBound_of_energyInequality` with the periodic `eq:Rhigh`
as the only hypothesis.
-/

noncomputable section

namespace NSFormalization.Section3.T11.HighOrderProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators

local instance highOrderProbeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance highOrderProbeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- **The target field, verbatim.**  Conditional on the periodic `eq:Rhigh`
(`appendix-a-local-theory.tex:127-138`) for the solutions of `SolvesBelowT`. -/
theorem higherOrderBound_closes
    (Chigh : ℕ → ℝ)
    (hRhigh : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
            HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * g ^ 2 ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                  torusSobolevNormAt (m : ℝ) w.velocity t * g +
                torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M :=
  higherOrderBound_of_energyInequality Chigh hRhigh

/-! ## Definitional checks -/

/-- The real profile is the canonical extended norm read as a real number. -/
example (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    torusSobolevNormAt s u t = (periodicSobolevENorm s (fun x ↦ u (t, x))).toReal := rfl

/-- The Grönwall constant produced by Young's absorption is `C_m²/(4ν)`. -/
example (C ν : ℝ) (_hν : 0 < ν) :
    ∀ {d g a n F : ℝ}, (1 / 2) * d + ν * g ^ 2 ≤ C * a * n * g + F * n →
      (1 / 2) * d ≤ C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 + F * n :=
  fun h ↦ torusYoungAbsorb _hν h

/-! ## Sharpness checks on the unconditional lemmas -/

/-- The order-descent direction is the one stated: at a nonzero constant the
lower order is bounded by the higher one, and both sides are finite. -/
example :
    periodicSobolevENorm 1 (fun _ ↦ coordinateVector 0) ≤
        periodicSobolevENorm 7 (fun _ ↦ coordinateVector 0) ∧
      periodicSobolevENorm 7 (fun _ ↦ coordinateVector 0) ≠ ⊤ :=
  ⟨periodicSobolevENorm_mono_order (by norm_num) _,
    periodicSobolevENorm_ne_top_smooth 7 contDiff_const fun _ _ ↦ rfl⟩

/-- The running `H²` cap is uniform in the horizon: the bound depends only on
`S` and `u`, never on the horizon `T` of the local solution that carries `u`. -/
example {ν S : ℝ} {a : SpatialField} {f u : SpaceTimeField}
    (hfin : squaredHTwoIntegralT S u ≠ ⊤) :
    ∀ (T₁ T₂ : ℝ) (w₁ : ClassicalSolutionT ν a f T₁) (w₂ : ClassicalSolutionT ν a f T₂),
      w₁.velocity = u → w₂.velocity = u → T₁ ≤ S → T₂ ≤ S →
        ∀ t₁ ∈ Ico (0 : ℝ) T₁, ∀ t₂ ∈ Ico (0 : ℝ) T₂,
          (∫ r in (0 : ℝ)..t₁, torusSobolevNormAt 2 u r ^ 2) ≤
              (squaredHTwoIntegralT S u).toReal ∧
            (∫ r in (0 : ℝ)..t₂, torusSobolevNormAt 2 u r ^ 2) ≤
              (squaredHTwoIntegralT S u).toReal :=
  fun _ _ w₁ w₂ h₁ h₂ hS₁ hS₂ _ ht₁ _ ht₂ ↦
    ⟨running_hTwo_integral_le w₁ h₁ hS₁ hfin ht₁,
      running_hTwo_integral_le w₂ h₂ hS₂ hfin ht₂⟩

end NSFormalization.Section3.T11.HighOrderProbe
