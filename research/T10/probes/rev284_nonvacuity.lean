import NSFormalization.Section3.T10.PhysicalBridge

noncomputable section

namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! Reviewer probe: the hypotheses hold for a concrete nonzero constant field. -/

example :
    let c : Space := coordinateVector (0 : Fin 3)
    c ≠ 0 ∧
      (forall x : Space,
        constantPartT (fun _ : Space ↦ c) x +
          meanZeroPartT (fun _ : Space ↦ c) x = c) ∧
        IsMeanZeroT (meanZeroPartT (fun _ : Space ↦ c)) := by
  dsimp
  constructor
  · intro h
    have h0 := congrArg (fun x : Space ↦ x (0 : Fin 3)) h
    simp [coordinateVector] at h0
  · apply mean_decomposition (fun _ : Space ↦ coordinateVector (0 : Fin 3))
    · intro x i
      rfl
    · change Integrable (fun _ : PeriodicTorus ↦ coordinateVector (0 : Fin 3))
        periodicTorusMeasure
      exact integrable_const _

/-! The sign-flipped reconstruction used by the negative probe is genuinely false. -/

example :
    ¬ (forall x : Space,
      constantPartT (fun _ : Space ↦ coordinateVector (0 : Fin 3)) x +
        meanZeroPartT (fun _ : Space ↦ coordinateVector (0 : Fin 3)) x =
          -coordinateVector (0 : Fin 3)) := by
  intro h
  have hx := h (0 : Space)
  have hx0 := congrArg (fun x : Space ↦ x (0 : Fin 3)) hx
  simp [constantPartT, meanZeroPartT, meanT_const, coordinateVector] at hx0
  norm_num at hx0

end NSFormalization.Section3.T10
