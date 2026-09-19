import Contracts.V1.MultipleRegions
import Bindings.MultipleRegions
import TestSupport.Axioms

/-! Axiom and shape checks for `T04.multiple_regions`. -/
noncomputable section
namespace BlowupDensity.Tests

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal BigOperators Topology

/-- The complete packet-indexed existence statement of `prop:multiple`. -/
theorem checkedMultipleRegions : multipleRegionsStatement :=
  Bindings.multipleRegionsStatement_holds

run_cmd TestSupport.checkAxioms ``checkedMultipleRegions

/-! Independent checks of three conclusion fields from
`research/T24/Spec.lean:1305-1329`. -/

example {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : MultipleRegionsAPI P T c r) :
    ∀ j : Fin N,
      SpeedUnboundedAtOn T (Metric.ball (c j) (r j)) a.assembled_velocity :=
  a.region_blowup

example {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : MultipleRegionsAPI P T c r) :
    (energyEssSupT T a.assembled_velocity) ^ (2 : ℕ) ≤
      ENNReal.ofReal (P.energyBound ^ 2 * ∑ j : Fin N, a.ε j) :=
  a.energy_bound

example {ν T : ℝ} {P : PacketImportAPI ν} {N : ℕ}
    {c : Fin N → Space} {r : Fin N → ℝ}
    (a : MultipleRegionsAPI P T c r) :
    (energyGradientT T a.assembled_velocity) ^ (2 : ℕ) =
      ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j : Fin N, a.ε j) :=
  a.dissipation_bound

end BlowupDensity.Tests
