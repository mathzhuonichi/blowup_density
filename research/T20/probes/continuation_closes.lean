import NSFormalization.Section3.T20.Continuation

/-!
Exact target-shape and non-vacuity probe for T20 unit U11
(`continuationBound`, `03-torus.tex:486-500`, `eq:criterion`).

§1 states the canonical field type with the structure's smallness constant `c`
and its continuation constant `Ccriterion` abstracted, and checks by `exact`
(a) that it *is* the `continuationBound` field of every `CriticalRegularityTAPI`
(so the spelling below is verbatim, not a paraphrase) and (b) that lane 437's
`continuationBound` inhabits it at `c = criticalSmallnessH1` (lane 432) and
`Ccriterion = hTwoConst ^ 2 * CH1`.

§2 records the explicit constant and its positivity, the datum U13 installs in
the `Ccriterion` / `hCcriterion` fields.

§3 is the non-vacuity witness at lanes 415/428/432's zero-force zero-solution
instance: the smallness hypothesis is genuinely satisfiable (`ρ = 0 < c·ν`), and
at that instance all three conjuncts — the orthogonal mode identity, the
displayed bound, and its finiteness — are actually produced.
-/

noncomputable section

namespace NSFormalization.Section3.T20.ContinuationProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20
open scoped ContDiff ENNReal

/-! ## §1  The canonical field type, verbatim -/

/-- `Section3/T20/CriticalRegularity.lean:350-364`, the `continuationBound` field
of `CriticalRegularityTAPI`, with the structure constants `c` and `Ccriterion`
abstracted. -/
def continuationBoundFieldType (c Ccriterion : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤

/-- The spelling above is the structure field itself. -/
example (API : CriticalRegularityTAPI) :
    continuationBoundFieldType API.c API.Ccriterion := API.continuationBound

/-- **Lane 437's theorem inhabits the canonical field** at
`c = criticalSmallnessH1`, `Ccriterion = hTwoConst ^ 2 * CH1`. -/
example : continuationBoundFieldType criticalSmallnessH1 Ccriterion := continuationBound

/-! ## §2  The constant U13 installs -/

/-- `Ccriterion` is the explicit real number `(1 + 1/(4π²))² · 2`. -/
example : Ccriterion = (1 + 1 / (4 * Real.pi ^ 2)) ^ 2 * 2 := rfl

/-- It is positive, which is the structure's `hCcriterion`. -/
example : 0 < Ccriterion := Ccriterion_pos

/-! ## §3  Non-vacuity -/

/-- The zero field is an order-`s` datum of the zero periodic field. -/
theorem zero_datum (s : ℝ) :
    IsPeriodicDatum s (fun _ : Space ↦ (0 : Space)) 0 := zero_isPeriodicDatum s

/-- The smallness hypothesis is genuinely satisfiable: the zero force has
`ρ = 0`, and `c·ν > 0`. -/
theorem zero_criticalRho_le : criticalRho (0 : SpaceTimeField) ≤ 0 := by
  show forceSobolevENormT 1 (1 / 2) (0 : SpaceTimeField) ≤ 0
  refine le_trans (iInf_le (fun G : {G : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) (0 : SpaceTimeField) G ∧
        AEStronglyMeasurable G forceTimeMeasure} ↦
    eLpNorm G.1 1 forceTimeMeasure)
    ⟨fun _ ↦ (0 : PeriodicSobolev (1 / 2)),
      fun t _ ↦ zero_datum (1 / 2), aestronglyMeasurable_const⟩) ?_
  show eLpNorm (fun _ : ℝ ↦ (0 : PeriodicSobolev (1 / 2))) 1 forceTimeMeasure ≤ 0
  exact le_of_eq eLpNorm_zero'

/-- **The full hypothesis package is inhabited and all three conjuncts are
actually produced**, on the horizon `T = 1` at `S = 1` with `ν = 1`. -/
example :
    ∃ (g : SpaceTimeField) (_hg : g ∈ forceClassT)
      (_hsmall : criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * 1))
      (w : ClassicalSolutionT 1 (fun _ : Space ↦ 0) g 1),
      squaredHTwoIntegralT 1 w.velocity = meanModeCriterionIntegral 1 g w.velocity ∧
        meanModeCriterionIntegral 1 g w.velocity ≤
          ENNReal.ofReal 1 * criticalRho g ^ (2 : ℝ) +
            ENNReal.ofReal (Ccriterion * ((1 : ℝ)⁻¹) ^ 2) *
              meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
          ENNReal.ofReal 1 * criticalRho g ^ (2 : ℝ) +
              ENNReal.ofReal (Ccriterion * ((1 : ℝ)⁻¹) ^ 2) *
                meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤ := by
  have hg : (0 : SpaceTimeField) ∈ forceClassT :=
    ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, by simp⟩
  have hsmall : criticalRho (0 : SpaceTimeField) <
      ENNReal.ofReal (criticalSmallnessH1 * 1) :=
    lt_of_le_of_lt zero_criticalRho_le
      (ENNReal.ofReal_pos.2 (by simpa using criticalSmallnessH1_pos))
  refine ⟨(0 : SpaceTimeField), hg, hsmall, ?_, ?_⟩
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
      exact ⟨fun _ ↦ 0, continuous_const.continuousOn, fun _ _ ↦ zero_datum (m : ℝ)⟩
    · intro t ht
      have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
        funext x
        simp [pressureGradient]
      rw [he]
      exact memLp_const (0 : Space)
    · intro t ht
      simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]
  · exact continuationBound 1 zero_lt_one (0 : SpaceTimeField) hg hsmall 1 _ 1
      zero_lt_one le_rfl

end NSFormalization.Section3.T20.ContinuationProbe
