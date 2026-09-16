import NSFormalization.Section4.A04.ShiftedExtension

open Set
open NSFormalization.Section4
open A02 A04
open scoped ENNReal

-- Substantive mutation: demand one extra unit of lifespan from the same inputs.
def ShiftedLocalExtensionPlusOne : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
    ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
      ENNReal.ofReal (b + L + 1) ≤ maximalLifespanR ν a f

theorem shiftedLocalExtension_plus_one : ShiftedLocalExtensionPlusOne := by
  intro ν hν a f T w b hb L w₂
  by_cases h : T < b + L
  · exact horizon_le_lifespan (exists_shifted_glue hν w hb w₂ h).some
  · exact (ENNReal.ofReal_le_ofReal (le_of_not_gt h)).trans (horizon_le_lifespan w)
