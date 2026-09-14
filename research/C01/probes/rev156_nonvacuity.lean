import Bindings.EnergyAbsorptionPartialV3
import Bindings.MaximalPartial
import NSFormalization.Section4.A04.ZeroSolution

/-! REVIEW PROBE (lane 156): the two **V3 contract fields** are not vacuously satisfiable.
The whole hypothesis block (`0 < ν`, `a ∈ initialClassR`, `MemForceR f`, a
`Contracts.V1.Data.ClassicalSolutionR`) is satisfiable by `A04.zeroSol` moved across by
`Bindings.maximalPartial_ofA02`, and the registered witness `Bindings.energyAbsorptionPartialV3`
really produces both conclusions at concrete times (`t = 0` and `t = 1` inside `Ico 0 2`,
`t = 1` inside `Ioo 0 2`).  The `energyDifferentialBound` instance is fed the derivative coming
out of the inherited V2 `energyIdentity`, the consumer route the contract docstring advertises. -/

noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq pairing)
open BlowupDensity.Contracts.V3.EnergyAbsorptionPartial (forcePrimitive energyBudget)
open BlowupDensity.Bindings

/-- A concrete inhabitant of the contract's solution structure: `ν = 1`, `a = 0`, `f = 0`,
`T = 2`. -/
def W : ClassicalSolutionR 1 0 0 2 :=
  maximalPartial_ofA02 (NSFormalization.Section4.A04.zeroSol 1 2 one_pos (by norm_num))

/-- Both time windows are nonempty at this instance. -/
theorem rev156_windows : (0 : ℝ) ∈ Ico (0 : ℝ) 2 ∧ (1 : ℝ) ∈ Ioo (0 : ℝ) 2 :=
  ⟨⟨le_rfl, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

/-- **eq:RL2 out of the registered witness, at the left endpoint `t = 0`.** -/
theorem rev156_l2Bound_zero : l2Norm (slice W.velocity 0) ≤ energyBudget 0 0 0 :=
  energyAbsorptionPartialV3.l2Bound 1 one_pos 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero 2 W 0 ⟨le_rfl, by norm_num⟩

/-- **eq:RL2 out of the registered witness, at an interior time `t = 1`.** -/
theorem rev156_l2Bound_one : l2Norm (slice W.velocity 1) ≤ energyBudget 0 0 1 :=
  energyAbsorptionPartialV3.l2Bound 1 one_pos 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero 2 W 1 ⟨by norm_num, by norm_num⟩

/-- The derivative produced by the inherited V2 `energyIdentity` at `t = 1`. -/
theorem rev156_deriv :
    HasDerivAt (fun s => l2Sq (slice W.velocity s))
      (-2 * 1 * gradientSq (slice W.velocity 1) +
        2 * pairing (slice W.velocity 1) (slice (0 : SpaceTimeField) 1)) 1 :=
  energyAbsorptionPartialV3.toEnergyAbsorptionPartialV2API.energyIdentity 1 one_pos 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero 2 W 1 ⟨by norm_num, by norm_num⟩

/-- **The differential bound out of the registered witness**, fed the `energyIdentity`
derivative at `t = 1`. -/
theorem rev156_edb :
    (-2 * 1 * gradientSq (slice W.velocity 1) +
        2 * pairing (slice W.velocity 1) (slice (0 : SpaceTimeField) 1))
      + 2 * 1 * gradientSq (slice W.velocity 1)
      ≤ 2 * l2Norm (slice (0 : SpaceTimeField) 1) * l2Norm (slice W.velocity 1) :=
  energyAbsorptionPartialV3.energyDifferentialBound 1 one_pos 0
    NSFormalization.Section4.A04.zero_mem_initialClassR 0
    NSFormalization.Section4.A04.memForceR_zero 2 W 1 ⟨by norm_num, by norm_num⟩ _ rev156_deriv

#print axioms rev156_l2Bound_zero
#print axioms rev156_l2Bound_one
#print axioms rev156_edb
