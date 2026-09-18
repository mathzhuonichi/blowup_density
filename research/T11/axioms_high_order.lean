import NSFormalization.Section3.T11.HighOrder
import NSFormalization.Section3.T11.LocalExistenceProbe

/-! Exact axiom audit of **every** declaration in
`Section3/T11/HighOrder.lean`: all 24 print exactly
`[propext, Classical.choice, Quot.sound]`.

No `sorry`, no new axiom, no `native_decide`, no `set_option maxHeartbeats`.
The nonzero shear-mode witness for `torusPressureDrop` lives in
`research/T11/probes/high_order_closes.lean` instead of the module, because its
frequency arithmetic prints a strict subset of these three axioms. -/

/-- info: 'NSFormalization.Section3.T11.highOrderNormedGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.highOrderNormedGroup

/-- info: 'NSFormalization.Section3.T11.highOrderNormedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.highOrderNormedSpace

/-- info: 'NSFormalization.Section3.T11.torusSobolevNormAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusSobolevNormAt

/-- info: 'NSFormalization.Section3.T11.torusSobolevNormAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusSobolevNormAt_nonneg

/-- info: 'NSFormalization.Section3.T11.torusSobolevNormAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusSobolevNormAt_eq

/-- info: 'NSFormalization.Section3.T11.periodicSobolevENorm_ne_top_of_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.periodicSobolevENorm_ne_top_of_datum

/-- info: 'NSFormalization.Section3.T11.continuousOn_torusSobolevNormAt_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.continuousOn_torusSobolevNormAt_velocity

/-- info: 'NSFormalization.Section3.T11.torusOrderDown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusOrderDown

/-- info: 'NSFormalization.Section3.T11.torusOrderDown_reweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusOrderDown_reweight

/-- info: 'NSFormalization.Section3.T11.torusOrderDown_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusOrderDown_norm_le

/-- info: 'NSFormalization.Section3.T11.periodicSobolevENorm_mono_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.periodicSobolevENorm_mono_order

/-- info: 'NSFormalization.Section3.T11.running_hTwo_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.running_hTwo_integral_le

/-- info: 'NSFormalization.Section3.T11.force_hm_profile_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.force_hm_profile_cap

/-- info: 'NSFormalization.Section3.T11.torusRealPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusRealPairing

/-- info: 'NSFormalization.Section3.T11.torusRealPairing_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusRealPairing_le

/-- info: 'NSFormalization.Section3.T11.periodicDerivativeSymbol_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.periodicDerivativeSymbol_conj

/-- info: 'NSFormalization.Section3.T11.periodicDerivativeSymbol_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.periodicDerivativeSymbol_neg

/-- info: 'NSFormalization.Section3.T11.torusPressureSymbol_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusPressureSymbol_drop

/-- info: 'NSFormalization.Section3.T11.torusPressureDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusPressureDrop

/-- info: 'NSFormalization.Section3.T11.torusLaplacianSymbol_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusLaplacianSymbol_pairing

/-- info: 'NSFormalization.Section3.T11.torusLaplacianSymbol_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusLaplacianSymbol_nonpos

/-- info: 'NSFormalization.Section3.T11.torusYoungAbsorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusYoungAbsorb

/-- info: 'NSFormalization.Section3.T11.torusGronwallChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusGronwallChain

/-- info: 'NSFormalization.Section3.T11.higherOrderBound_of_energyInequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.higherOrderBound_of_energyInequality

noncomputable section

namespace NSFormalization.Section3.T11.HighOrderAudit

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators

local instance auditNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance auditNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## Non-vacuity at genuine, nonzero data -/

/-- The nonzero constant datum `e₀` is a real datum of a nonzero field at every
order, so the order-descent lemma compares two finite nonzero-carrier norms. -/
example :
    IsPeriodicDatum 3 (fun _ ↦ coordinateVector 0)
        (torusConstantDatum 3 (coordinateVector 0)) ∧
      periodicSobolevENorm 2 (fun _ ↦ coordinateVector (0 : Fin 3)) ≤
        periodicSobolevENorm 3 (fun _ ↦ coordinateVector (0 : Fin 3)) :=
  ⟨torusConstantDatum_isDatum 3 (coordinateVector 0),
    periodicSobolevENorm_mono_order (by norm_num) _⟩

/-- The nonzero constant datum is solenoidal, so the hypothesis of
`torusPressureDrop` is satisfiable; the nonzero shear-mode witness (nonzero on
*both* sides of the pairing) is in `research/T11/probes/high_order_closes.lean`. -/
example (c : Space) : IsSolenoidalPeriodicDatum (torusConstantDatum 3 c) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [periodicDerivativeSymbol]
  · have hz : ∀ j : Fin 3, (torusConstantDatum 3 c).1 j k = 0 := by
      intro j
      simp [torusConstantDatum, lp.single_apply, hk]
    simp [hz]

/-- Young's absorption is sharp at the perfect square: equality holds exactly
when `2νg = C a n`. -/
example : (1 / 2) * (2 : ℝ) ≤ (2 : ℝ) ^ 2 / (4 * 1) * 1 ^ 2 * 1 ^ 2 + 0 * 1 :=
  torusYoungAbsorb (d := 2) (g := 1) (a := 1) (n := 1) (F := 0) (ν := 1) (C := 2)
    one_pos (by norm_num)

end NSFormalization.Section3.T11.HighOrderAudit
