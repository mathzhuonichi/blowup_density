import NSFormalization.Section3.T20.YBound

/-!
Exact target-shape and non-vacuity probe for T20 unit U9
(`yBound`, `03-torus.tex:446-458`, `eq:ybound`).

§1 states the canonical field type with the structure's smallness constant `c`
abstracted and checks, by `exact`, (a) that it *is* the `yBound` field of every
`CriticalRegularityTAPI` (so the spelling below is verbatim, not a paraphrase)
and (b) that lane 428's `yBound` inhabits it at `c = criticalSmallness`
(`= 1/(8·criticalTrilinearConst)`, which is strictly below the structure's
shrinking threshold `1/(4·criticalTrilinearConst)`).

§2 is the non-vacuity witness at lane 415's zero-force zero-solution instance:
the smallness hypothesis is genuinely satisfiable (`ρ = 0 < c·ν`), and at that
instance the conclusion is the actual pair of extended-real inequalities.
-/

noncomputable section

namespace NSFormalization.Section3.T20.YBoundProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20
open scoped ContDiff ENNReal

/-! ## §1  The canonical field type, verbatim -/

/-- `Section3/T20/CriticalRegularity.lean:314-322`, the `yBound` field of
`CriticalRegularityTAPI`, with the structure constant `c` abstracted. -/
def yBoundFieldType (c : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g

/-- The spelling above is the structure field itself. -/
example (API : CriticalRegularityTAPI) : yBoundFieldType API.c := API.yBound

/-- **Lane 428's theorem inhabits the canonical field at `c = criticalSmallness`.** -/
example : yBoundFieldType criticalSmallness := yBound

/-- The constant is positive and strictly below the structure's shrinking
threshold `c < 1/(4 C₀)`, so U13 can install it together with U8's
`C₀ = criticalTrilinearConst`. -/
example : 0 < criticalSmallness ∧
    criticalSmallness < 1 / (4 * criticalTrilinearConst) :=
  ⟨criticalSmallness_pos, criticalSmallness_lt_quarter⟩

/-! ## §2  Non-vacuity -/

/-- The zero field is an order-`s` datum of the zero periodic field. -/
theorem zero_isPeriodicDatum (s : ℝ) :
    IsPeriodicDatum s (fun _ : Space ↦ (0 : Space)) 0 := by
  refine ⟨fun _ _ ↦ rfl, integrable_zero _ _ _, fun i k ↦ ?_⟩
  have hz : (fun x : Space ↦ (((0 : Space) i : ℝ) : ℂ)) = fun _ : Space ↦ (0 : ℂ) := by
    funext x
    norm_num
  rw [hz, periodicFourierCoeff_const]
  simp

/-- The smallness hypothesis is genuinely satisfiable: the zero force has
`ρ = 0`, and `c·ν > 0`. -/
theorem zero_criticalRho_le : criticalRho (0 : SpaceTimeField) ≤ 0 := by
  show forceSobolevENormT 1 (1 / 2) (0 : SpaceTimeField) ≤ 0
  refine le_trans (iInf_le (fun G : {G : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) (0 : SpaceTimeField) G ∧
        AEStronglyMeasurable G forceTimeMeasure} ↦
    eLpNorm G.1 1 forceTimeMeasure)
    ⟨fun _ ↦ (0 : PeriodicSobolev (1 / 2)),
      fun t _ ↦ zero_isPeriodicDatum (1 / 2), aestronglyMeasurable_const⟩) ?_
  show eLpNorm (fun _ : ℝ ↦ (0 : PeriodicSobolev (1 / 2))) 1 forceTimeMeasure ≤ 0
  exact le_of_eq eLpNorm_zero'

example : criticalRho (0 : SpaceTimeField) < ENNReal.ofReal (criticalSmallness * 1) :=
  lt_of_le_of_lt zero_criticalRho_le
    (ENNReal.ofReal_pos.2 (by simpa using criticalSmallness_pos))

/-- **The full hypothesis package is inhabited and the conclusion is the actual
pair of inequalities at `t = 1/2` on the horizon `T = 1`.** -/
example :
    ∃ (g : SpaceTimeField) (_hg : g ∈ forceClassT)
      (_hsmall : criticalRho g < ENNReal.ofReal (criticalSmallness * 1))
      (w : ClassicalSolutionT 1 (fun _ : Space ↦ 0) g 1),
      criticalY (meanFreeVelocity g w.velocity) ((1 : ℝ) / 2) ≤
          ∫⁻ s in Ioc (0 : ℝ) ((1 : ℝ) / 2), criticalB (meanFreeForce g) s ∧
        (∫⁻ s in Ioc (0 : ℝ) ((1 : ℝ) / 2), criticalB (meanFreeForce g) s) ≤
          criticalRho g := by
  have hg : (0 : SpaceTimeField) ∈ forceClassT :=
    ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, by simp⟩
  have hsmall : criticalRho (0 : SpaceTimeField) <
      ENNReal.ofReal (criticalSmallness * 1) :=
    lt_of_le_of_lt zero_criticalRho_le
      (ENNReal.ofReal_pos.2 (by simpa using criticalSmallness_pos))
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
      exact ⟨fun _ ↦ 0, continuous_const.continuousOn,
        fun _ _ ↦ zero_isPeriodicDatum (m : ℝ)⟩
    · intro t ht
      have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
        funext x
        simp [pressureGradient]
      rw [he]
      exact memLp_const (0 : Space)
    · intro t ht
      simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]
  · exact yBound 1 zero_lt_one (0 : SpaceTimeField) hg hsmall 1 _ ((1 : ℝ) / 2)
      ⟨by norm_num, by norm_num⟩

end NSFormalization.Section3.T20.YBoundProbe
