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

/-! ## A nonzero witness for the pressure drop

These live in the probe, not in `HighOrder.lean`: the frequency arithmetic below
depends on a strict subset of the three standard axioms (`shearFreq` and
`shearFreq_ne_neg` print `[propext]`, `shearFreq_component_one` prints
`[propext, Quot.sound]`), and every declaration of the module proper prints
exactly `[propext, Classical.choice, Quot.sound]`. -/

/-- The lattice frequency `(1,0,0)`. -/
def shearFreq : PeriodicFrequency := fun j ↦ if j = 0 then 1 else 0

theorem shearFreq_ne_neg : shearFreq ≠ -shearFreq := by
  intro h
  have h0 := congrFun h 0
  simp [shearFreq] at h0

theorem shearFreq_component_one : shearFreq 1 = 0 := by simp [shearFreq]

/-- A genuinely nonzero solenoidal velocity datum: the shear flow
`u(x) = 2 e₁ cos(2π x₀)`, carried by the conjugate mode pair `±(1,0,0)` in the
`e₁` component.  Its frequency is orthogonal to its amplitude, so it is
divergence free. -/
def torusShearDatum (s : ℝ) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦ if i = 1 then
      lp.single 2 shearFreq (1 : ℂ) + lp.single 2 (-shearFreq) (1 : ℂ) else 0), ?_⟩
  intro i k
  by_cases hi : i = 1
  · subst hi
    change ((lp.single 2 shearFreq (1 : ℂ) +
        lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData)) (-k) =
      star ((lp.single 2 shearFreq (1 : ℂ) +
        lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData) k)
    by_cases h1 : k = shearFreq
    · subst h1
      simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm]
    · by_cases h2 : k = -shearFreq
      · subst h2
        simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm, neg_neg]
      · have h3 : -k ≠ shearFreq := fun h ↦ h2 (by rw [← h, neg_neg])
        have h4 : -k ≠ -shearFreq := fun h ↦ h1 (neg_injective h)
        simp [lp.single_apply, h1, h2, h3, h4]
  · simp [hi]

theorem torusShearDatum_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    (torusShearDatum s).1 i k =
      if i = 1 then
        (if k = shearFreq then (1 : ℂ) else 0) + (if k = -shearFreq then (1 : ℂ) else 0)
      else 0 := by
  by_cases hi : i = 1
  · subst hi
    change ((lp.single 2 shearFreq (1 : ℂ) +
      lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData)) k = _
    simp [lp.single_apply, Pi.single_apply]
  · simp [torusShearDatum, hi]

theorem torusShearDatum_ne_zero (s : ℝ) : torusShearDatum s ≠ 0 := by
  intro h
  have hv := congrArg (fun A : PeriodicSobolev s ↦ A.1 1 shearFreq) h
  rw [torusShearDatum_apply] at hv
  simp [shearFreq_ne_neg] at hv

theorem torusShearDatum_solenoidal (s : ℝ) :
    IsSolenoidalPeriodicDatum (torusShearDatum s) := by
  intro k
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [torusShearDatum_apply]
  by_cases hj : j = 1
  · subst hj
    by_cases h1 : k = shearFreq
    · subst h1
      simp [periodicDerivativeSymbol, shearFreq_component_one]
    · by_cases h2 : k = -shearFreq
      · subst h2
        simp [periodicDerivativeSymbol, shearFreq_component_one]
      · simp [h1, h2]
  · simp [hj]

/-- The scalar symbol of the companion pressure: the same conjugate mode pair. -/
def shearPressureSymbol (k : PeriodicFrequency) : ℂ :=
  if k = shearFreq then 1 else if k = -shearFreq then 1 else 0

/-- The gradient datum of that pressure — genuinely nonzero. -/
def torusShearPressureDatum (s : ℝ) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦
      lp.single 2 shearFreq (periodicDerivativeSymbol i shearFreq) +
        lp.single 2 (-shearFreq) (periodicDerivativeSymbol i (-shearFreq))), ?_⟩
  intro i k
  change ((lp.single 2 shearFreq (periodicDerivativeSymbol i shearFreq) +
      lp.single 2 (-shearFreq) (periodicDerivativeSymbol i (-shearFreq)) :
        PeriodicScalarData)) (-k) =
    star ((lp.single 2 shearFreq (periodicDerivativeSymbol i shearFreq) +
      lp.single 2 (-shearFreq) (periodicDerivativeSymbol i (-shearFreq)) :
        PeriodicScalarData) k)
  by_cases h1 : k = shearFreq
  · subst h1
    simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm,
      periodicDerivativeSymbol_conj, periodicDerivativeSymbol_neg]
  · by_cases h2 : k = -shearFreq
    · subst h2
      simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm,
        periodicDerivativeSymbol_conj, periodicDerivativeSymbol_neg, neg_neg]
    · have h3 : -k ≠ shearFreq := fun h ↦ h2 (by rw [← h, neg_neg])
      have h4 : -k ≠ -shearFreq := fun h ↦ h1 (neg_injective h)
      simp [lp.single_apply, h1, h2, h3, h4]

theorem torusShearPressureDatum_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    (torusShearPressureDatum s).1 i k =
      periodicDerivativeSymbol i k * shearPressureSymbol k := by
  change ((lp.single 2 shearFreq (periodicDerivativeSymbol i shearFreq) +
      lp.single 2 (-shearFreq) (periodicDerivativeSymbol i (-shearFreq)) :
        PeriodicScalarData)) k = _
  by_cases h1 : k = shearFreq
  · subst h1
    simp [lp.single_apply, shearPressureSymbol, shearFreq_ne_neg]
  · by_cases h2 : k = -shearFreq
    · subst h2
      simp [lp.single_apply, shearPressureSymbol, (shearFreq_ne_neg).symm]
    · simp [lp.single_apply, shearPressureSymbol, h1, h2]

theorem torusShearPressureDatum_ne_zero (s : ℝ) : torusShearPressureDatum s ≠ 0 := by
  intro h
  have hv := congrArg (fun A : PeriodicSobolev s ↦ A.1 0 shearFreq) h
  rw [torusShearPressureDatum_apply] at hv
  simp [shearPressureSymbol, periodicDerivativeSymbol, shearFreq, Complex.ext_iff,
    Real.pi_ne_zero] at hv

/-- **The pressure drop is not vacuous.**  Both the velocity datum and the
pressure-gradient datum are nonzero, and the `H^s` pairing still vanishes. -/
example (s : ℝ) :
    torusShearDatum s ≠ 0 ∧ torusShearPressureDatum s ≠ 0 ∧
      torusRealPairing (torusShearDatum s) (torusShearPressureDatum s) = 0 :=
  ⟨torusShearDatum_ne_zero s, torusShearPressureDatum_ne_zero s,
    torusPressureDrop (torusShearDatum_solenoidal s) shearPressureSymbol
      (torusShearPressureDatum_apply s)⟩


end NSFormalization.Section3.T11.HighOrderProbe
