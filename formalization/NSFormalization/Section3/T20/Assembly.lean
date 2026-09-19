import NSFormalization.Section3.T20.TransportLambda
import NSFormalization.Section3.T20.ConstantTransport
import NSFormalization.Section3.T20.GlobalRegularity
import NSFormalization.Section3.T10.ForcePaths
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# T20 U13 — assembly of critical periodic regularity

This module installs the constants selected by U7, U10, and U11 and bundles
the eleven mathematical fields proved by U1–U12 into the canonical
`CriticalRegularityTAPI` record.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

/-- The canonical 23-field T20 critical-regularity package. -/
def criticalRegularityT : CriticalRegularityTAPI where
  c := criticalSmallnessH1
  hc := criticalSmallnessH1_pos
  C₀ := criticalTrilinearConst
  C₀_pos := criticalTrilinearConst_pos
  C₁ := h1TrilinearConst
  C₁_pos := h1TrilinearConst_pos
  CH1 := CH1
  CH1_pos := CH1_pos
  Ccriterion := Ccriterion
  hCcriterion := Ccriterion_pos
  c_lt_C₀ := criticalSmallnessH1_lt_quarter_C₀
  c_lt_C₁ := criticalSmallnessH1_lt_quarter_C₁
  reductionRegular := reductionRegular
  meanBound := meanBound
  meanFreeEquation := meanFreeEquation
  constantTransportSkew := constantTransportSkew
  constantTransportCommutesLambda := constantTransportCommutesLambda
  criticalEnergy := criticalEnergy
  bIntegral := bIntegral
  yBound := yBound_of_le criticalSmallnessH1_le_half
  hOneEnergy := hOneEnergy
  continuationBound := continuationBound
  globalRegularity := globalRegularity

/-- The existential statement form of T20 holds. -/
theorem criticalRegularityStatement_holds : criticalRegularityStatement :=
  ⟨criticalRegularityT⟩

/-! ## Non-vacuity -/

/-- The compact positive-time bump used for the nonzero-force witness. -/
def criticalNonvacuityProfile : ContDiffBump (2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- A nonzero, spatially constant, compactly time-supported force. -/
def criticalNonvacuityForce : SpaceTimeField :=
  fun z ↦ criticalNonvacuityProfile z.1 • coordinateVector 0

theorem criticalNonvacuityForce_mem : criticalNonvacuityForce ∈ forceClassT := by
  have hsupport : tsupport (criticalNonvacuityProfile : ℝ → ℝ) ⊆ Ioi 0 := by
    rw [criticalNonvacuityProfile.tsupport_eq]
    intro t ht
    have habs : |t - 2| ≤ 1 / 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, criticalNonvacuityProfile] using ht
    have := (abs_le.mp habs).1
    change 0 < t
    linarith
  exact memForceT_time_smul criticalNonvacuityProfile.contDiff
    criticalNonvacuityProfile.hasCompactSupport hsupport contDiff_const
    (fun _ _ ↦ rfl)

theorem criticalNonvacuityForce_nonzero : criticalNonvacuityForce (2, 0) ≠ 0 := by
  have hp : criticalNonvacuityProfile 2 = 1 :=
    criticalNonvacuityProfile.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      exact criticalNonvacuityProfile.rIn_pos.le)
  have hc : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Space ↦ x 0) h
    simp [coordinateVector] at h0
  simpa only [criticalNonvacuityForce, hp, one_smul] using hc

/-- The witness force has finite critical size. -/
theorem criticalNonvacuityRho_ne_top : criticalRho criticalNonvacuityForce ≠ ⊤ := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum (1 / 2) contDiff_const
    (fun (_ : Space) (_ : Fin 3) ↦ rfl :
      IsPeriodicSpatial (fun _ : Space ↦ coordinateVector 0))
  let G : ℝ → PeriodicSobolev (1 / 2) := fun t ↦ criticalNonvacuityProfile t • A
  have hpath : IsPeriodicSobolevPath (1 / 2) criticalNonvacuityForce G := by
    intro t _ht
    change IsPeriodicDatum (1 / 2)
      (fun _ ↦ criticalNonvacuityProfile t • coordinateVector 0)
      (criticalNonvacuityProfile t • A)
    exact NSFormalization.Section3.T11.Transport.isPeriodicDatum_smul hA
      (criticalNonvacuityProfile t)
  have hcont : Continuous G := criticalNonvacuityProfile.continuous.smul continuous_const
  have hcompact : HasCompactSupport G := by
    apply HasCompactSupport.intro criticalNonvacuityProfile.hasCompactSupport
    intro t ht
    have hz : criticalNonvacuityProfile t = 0 := image_eq_zero_of_notMem_tsupport ht
    simp [G, hz]
  have hmem : MemLp G 1 forceTimeMeasure :=
    (hcont.memLp_of_hasCompactSupport (μ := volume) (p := 1) hcompact).mono_measure
      Measure.restrict_le_self
  have hstrong : StronglyMeasurable G := by
    exact criticalNonvacuityProfile.continuous.stronglyMeasurable.smul
      stronglyMeasurable_const
  let Gsub : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) criticalNonvacuityForce H ∧
        AEStronglyMeasurable H forceTimeMeasure} :=
    ⟨G, hpath, hstrong.aestronglyMeasurable⟩
  have hle : (⨅ H : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) criticalNonvacuityForce H ∧
        AEStronglyMeasurable H forceTimeMeasure},
      eLpNorm H.1 1 forceTimeMeasure) ≤ eLpNorm G 1 forceTimeMeasure :=
    iInf_le (fun H : {H : ℝ → PeriodicSobolev (1 / 2) //
      IsPeriodicSobolevPath (1 / 2) criticalNonvacuityForce H ∧
        AEStronglyMeasurable H forceTimeMeasure} ↦
      eLpNorm H.1 1 forceTimeMeasure) Gsub
  unfold criticalRho forceSobolevENormT
  exact ne_top_of_le_ne_top hmem.eLpNorm_ne_top hle

/-- The small-data hypothesis is genuinely inhabited by a nonzero compactly
time-supported force.  The viscosity is chosen after the finite force size;
equivalently, this is the unit-viscosity witness after amplitude scaling. -/
theorem criticalRegularityT_nonvacuous :
    ∃ (ν : ℝ) (g : SpaceTimeField) (_hg : g ∈ forceClassT),
      0 < ν ∧ g (2, 0) ≠ 0 ∧
        criticalRho g < ENNReal.ofReal (criticalRegularityT.c * ν) ∧
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  let ν : ℝ :=
    ((criticalRho criticalNonvacuityForce).toReal + 1) / criticalSmallnessH1
  have hν : 0 < ν := div_pos (by positivity) criticalSmallnessH1_pos
  have hmul : criticalSmallnessH1 * ν =
      (criticalRho criticalNonvacuityForce).toReal + 1 := by
    dsimp [ν]
    field_simp [criticalSmallnessH1_pos.ne']
  have hsmall : criticalRho criticalNonvacuityForce <
      ENNReal.ofReal (criticalRegularityT.c * ν) := by
    change criticalRho criticalNonvacuityForce <
      ENNReal.ofReal (criticalSmallnessH1 * ν)
    rw [hmul]
    calc
      criticalRho criticalNonvacuityForce =
          ENNReal.ofReal (criticalRho criticalNonvacuityForce).toReal :=
        (ENNReal.ofReal_toReal criticalNonvacuityRho_ne_top).symm
      _ < ENNReal.ofReal ((criticalRho criticalNonvacuityForce).toReal + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  exact ⟨ν, criticalNonvacuityForce, criticalNonvacuityForce_mem, hν,
    criticalNonvacuityForce_nonzero, hsmall,
    criticalRegularityT.globalRegularity ν hν criticalNonvacuityForce
      criticalNonvacuityForce_mem hsmall⟩

end NSFormalization.Section3.T20
