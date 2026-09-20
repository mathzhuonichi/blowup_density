import NSFormalization.Section4.R44.Absorption
import NSFormalization.Section4.R41.NonDensityL1

/-! Proposition 4.4 at zero initial datum, with the fixed explicit radius.
Lane 228's S1d, adapted to lane 227's constants, removes the last hypothesis.
The two conclusion fields below have RCritical2API's binders. -/
noncomputable section
namespace NSFormalization.Section4.R44
open A02 (SpaceTimeField maximalLifespanR)
open D01 Set MeasureTheory
open scoped ENNReal

/-- Proposition 4.4 with no differential-inequality hypothesis. -/
theorem rcritical2_endpoint_unconditional :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, A02.MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f := by
  intro ν S hν hS f hf hsmall
  exact rcritical2_endpoint_of_differential ν S hν hS f hf
    (rCritical2Differential_of_classical hν hf) hsmall

/-- RCritical2API.main, at the explicit radius theta/20 * ν^(3/2) * exp(-3νS). -/
theorem main :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, A02.MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f :=
  rcritical2_endpoint_unconditional

/-- RCritical2API.nonDensityBallZero, using the same explicit radius. -/
theorem nonDensityBallZero :
    ∀ ν T : ℝ, 0 < ν → 0 < T →
      ∀ f : SpaceTimeField, A02.MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν T) →
          f ∉ R41.breakdownSetRZero ν T := by
  intro ν T hν hT f hf hsmall hb
  exact (not_le_of_gt (main ν T hν hT f hf hsmall)) hb.2

/-- Zero force belongs to the actual strict smallness ball. -/
theorem zero_force_small (ν S : ℝ) (hν : 0 < ν) :
    forceSobolevENormL2 (-1 / 2) (0 : SpaceTimeField) < ENNReal.ofReal (radius ν S) := by
  have hz : forceSobolevENormL2 (-1 / 2) (0 : SpaceTimeField) = 0 := by
    apply le_antisymm _ bot_le
    apply iInf_le_of_le ⟨fun _ => 0, (fun _ _ => isSobolevDatum_zero _),
      aestronglyMeasurable_zero⟩
    simp [Homogeneous.bochnerDatumENorm]
  rw [hz]
  exact ENNReal.ofReal_pos.mpr (radius_pos hν)

example (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S) :
    ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) (0 : SpaceTimeField) :=
  main ν S hν hS 0 A04.memForceR_zero (zero_force_small ν S hν)

end NSFormalization.Section4.R44
