import NSFormalization.Section3.T11.ConvolutionBound

noncomputable section
namespace NSFormalization.Section3.T11.Rev317

open NSFormalization.Section3.T10

local instance rev317NormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance rev317NormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- Deliberately false affine mutation of the main coefficient identity. Every
binder is retained, but the right side is shifted by the nonzero constant `1`. -/
def TorusConvolutionInputShifted : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k + 1

example : TorusConvolutionInputShifted := by
  obtain ⟨Q, hQ⟩ := torusConvolutionInput
  refine ⟨Q, ?_⟩
  intro A B i k
  exact hQ A B i k

end NSFormalization.Section3.T11.Rev317
