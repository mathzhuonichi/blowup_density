import NSFormalization.Section4.R44.Prop44
noncomputable section
open NSFormalization.Section4
open NSFormalization.Section4.R44
open A02 D01
-- Substantive mutation: double the admissible radius, retaining the original proof.
example :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, A02.MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (2 * radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f := by
  intro ν S hν hS f hf hsmall
  exact rcritical2_endpoint_of_differential ν S hν hS f hf
    (rCritical2Differential_of_classical hν hf) hsmall
