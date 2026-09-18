import NSFormalization.Section3.T20.H1Energy

/-!
Exact target-shape and non-vacuity probe for T20 unit U10b
(`hOneEnergy`, `03-torus.tex:467-484`, `eq:H1energy`).

§1 states the canonical field type with the structure's smallness constant `c`
and its `H¹` energy constant `CH1` abstracted, and checks by `exact`
(a) that it *is* the `hOneEnergy` field of every `CriticalRegularityTAPI` (so
the spelling below is verbatim, not a paraphrase) and (b) that lane 432's
`hOneEnergy` inhabits it at `c = criticalSmallnessH1`, `CH1 = 2`.

§2 records the two strict shrinkings the structure demands of `c`
(`c < 1/(4C₀)` and `c < 1/(4C₁)`) at the installed constants
`C₀ = criticalTrilinearConst` (U7/U8) and `C₁ = h1TrilinearConst` (U10a).

§3 is the non-vacuity witness at lanes 415/428's zero-force zero-solution
instance: the smallness hypothesis is genuinely satisfiable (`ρ = 0 < c·ν`),
and at that instance the conclusion is an actual real derivative together with
the displayed inequality.
-/

noncomputable section

namespace NSFormalization.Section3.T20.H1EnergyProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open NSFormalization.Section3.T20
open scoped ContDiff ENNReal

/-! ## §1  The canonical field type, verbatim -/

/-- `Section3/T20/CriticalRegularity.lean:330-342`, the `hOneEnergy` field of
`CriticalRegularityTAPI`, with the structure constants `c` and `CH1`
abstracted. -/
def hOneEnergyFieldType (c CH1 : ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x))

/-- The spelling above is the structure field itself. -/
example (API : CriticalRegularityTAPI) : hOneEnergyFieldType API.c API.CH1 :=
  API.hOneEnergy

/-- **Lane 432's theorem inhabits the canonical field** at
`c = criticalSmallnessH1`, `CH1 = 2`. -/
example : hOneEnergyFieldType criticalSmallnessH1 CH1 := hOneEnergy

/-! ## §2  The constants U13 installs -/

/-- `CH1 = 2` is positive, and the smallness radius is positive and strictly
below **both** shrinking thresholds: `c < 1/(4·C₀)` with
`C₀ = criticalTrilinearConst` (the constant U8 installs) and `c < 1/(4·C₁)`
with `C₁ = h1TrilinearConst` (the constant U10a installs). -/
example : 0 < CH1 ∧ 0 < criticalSmallnessH1 ∧
    criticalSmallnessH1 < 1 / (4 * criticalTrilinearConst) ∧
    criticalSmallnessH1 < 1 / (4 * h1TrilinearConst) :=
  ⟨CH1_pos, criticalSmallnessH1_pos, criticalSmallnessH1_lt_quarter_C₀,
    criticalSmallnessH1_lt_quarter_C₁⟩

/-- The radius is still inside U9's bootstrap range, so `yBound_of_le` applies
verbatim at this `c`. -/
example : criticalSmallnessH1 ≤ 1 / (2 * criticalTrilinearConst) :=
  criticalSmallnessH1_le_half

/-- `CH1` is the explicit real number `2`. -/
example : CH1 = 2 := rfl

/-! ## §3  Non-vacuity -/

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

/-- **The full hypothesis package is inhabited and the conclusion is an actual
real derivative together with the displayed inequality**, at `t = 1/2` on the
horizon `T = 1` with `ν = 1`. -/
example :
    ∃ (g : SpaceTimeField) (_hg : g ∈ forceClassT)
      (_hsmall : criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * 1))
      (w : ClassicalSolutionT 1 (fun _ : Space ↦ 0) g 1) (E' : ℝ),
      HasDerivAt
          (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)))
          E' ((1 : ℝ) / 2) ∧
        E' + 1 * laplacianSqT
            (fun x ↦ meanFreeVelocity g w.velocity ((1 : ℝ) / 2, x)) ≤
          CH1 * (1 : ℝ)⁻¹ * lTwoSqT (fun x ↦ meanFreeForce g ((1 : ℝ) / 2, x)) := by
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
  · exact hOneEnergy 1 zero_lt_one (0 : SpaceTimeField) hg hsmall 1 _ ((1 : ℝ) / 2)
      ⟨by norm_num, by norm_num⟩

end NSFormalization.Section3.T20.H1EnergyProbe
