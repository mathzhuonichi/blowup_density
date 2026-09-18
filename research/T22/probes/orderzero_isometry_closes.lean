import NSFormalization.Section3.T22.OrderZeroIsometry

/-!
# Non-vacuity probe for `norm_orderZeroDatum_eq` (T22 · U-A4)

A concrete nonzero `ContDiffBump` field `z : Space → Space` (a scalar bump times the
first coordinate axis) is smooth with compact support, hence `MemLp z 2 volume`, and its
order-0 datum norm equals `eLpNorm z 2 volume` with both sides finite (`< ⊤`).  This shows
the identity is not vacuously about `⊤ = ⊤` or `0 = 0`.
-/

noncomputable section
namespace T22Probe
open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01

/-- A standard bump on `ℝ³` centred at the origin, `rIn = 1`, `rOut = 2`. -/
def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The nonzero vector field: the bump along the first coordinate axis. -/
def zField : Space → Space := fun x => bump x • coordinateVector 0

theorem zField_hasCompactSupport : HasCompactSupport zField := by
  show HasCompactSupport ((fun r : ℝ => r • coordinateVector 0) ∘ (bump : Space → ℝ))
  exact bump.hasCompactSupport.comp_left (by simp)

theorem zField_continuous : Continuous zField :=
  bump.continuous.smul continuous_const

theorem zField_memLp : MemLp zField 2 volume :=
  zField_continuous.memLp_of_hasCompactSupport zField_hasCompactSupport

/-- `z` is genuinely nonzero: at the centre `z 0 = coordinateVector 0 ≠ 0`. -/
theorem zField_ne_zero : zField 0 ≠ 0 := by
  have hf : bump 0 = 1 :=
    bump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact bump.rIn_pos.le)
  have hz : zField 0 = coordinateVector 0 := by simp only [zField, hf, one_smul]
  rw [hz, coordinateVector]
  simp

/-- The order-0 Plancherel identity holds for this concrete field, and both sides are finite. -/
theorem probe_closes :
    ‖orderZeroDatum zField_memLp‖ₑ = eLpNorm zField 2 volume
      ∧ eLpNorm zField 2 volume < ⊤
      ∧ ‖orderZeroDatum zField_memLp‖ₑ < ⊤ := by
  have hEq : ‖orderZeroDatum zField_memLp‖ₑ = eLpNorm zField 2 volume :=
    norm_orderZeroDatum_eq zField_memLp
  have hFin : eLpNorm zField 2 volume < ⊤ := zField_memLp.2
  exact ⟨hEq, hFin, hEq ▸ hFin⟩

end T22Probe
