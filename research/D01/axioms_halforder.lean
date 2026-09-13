import Contracts.V1.Data
import NSFormalization.Section4.D01.HalfOrder

/-!
# Conformance: G3 (inhomogeneous half) in `Contracts.V1.Data` vocabulary

Checks that `Section4.D01.HalfOrder`'s theorems discharge the R43 obligation
stated with the frozen contract declarations, that the local restatements are
`rfl`-equal to the contract's (so no drift), and that only the standard logical
axioms are used.

Run: `cd verification && lake env lean ../research/D01/axioms_halforder.lean`
-/

open scoped ENNReal

namespace BlowupDensity.Contracts.V1.Data

/-! ## `rfl` bridges: the local restatements are the contract declarations -/

/-- `HalfOrder.forceSobolevENorm` = `Data.forceSobolevENorm` (`Data.lean:225`). -/
theorem halforder_forceSobolevENorm_eq (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) :
    NSFormalization.Section4.D01.forceSobolevENorm q s f
      = Contracts.V1.Data.forceSobolevENorm q s f := rfl

/-- `HalfOrder.forceSobolevENormL1` = `Data.forceSobolevENormL1` (`Data.lean:231`). -/
theorem halforder_forceSobolevENormL1_eq (s : ℝ) (f : SpaceTimeField) :
    NSFormalization.Section4.D01.forceSobolevENormL1 s f
      = Contracts.V1.Data.forceSobolevENormL1 s f := rfl

/-! ## The R43 obligation (G3, inhomogeneous half), in contract vocabulary -/

/-- Proposition 4.3's smallness hypothesis `‖f‖_{L¹_t H^{1/2}_x} ≤ c`
(`04-whole-space.tex:97`) is not vacuous: the norm is finite on `𝓕_ℝ`. -/
example : ∀ f : SpaceTimeField, MemForceR f → forceSobolevENormL1 (1 / 2) f ≠ ⊤ :=
  fun _ hf => NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf

/-- The `L²_t H^{1/2}_x` companion is finite too. -/
example : ∀ f : SpaceTimeField, MemForceR f → forceSobolevENorm 2 (1 / 2) f ≠ ⊤ :=
  fun _ hf => NSFormalization.Section4.D01.forceSobolevENormL2_half_ne_top hf

/-- The general statement: every real order `s ≤ m` and `q ∈ {1, 2}`. -/
example : ∀ (f : SpaceTimeField), MemForceR f → ∀ (s : ℝ) (m : ℕ), s ≤ (m : ℝ) →
    ∀ q : ℝ≥0∞, q = 1 ∨ q = 2 → forceSobolevENorm q s f ≠ ⊤ :=
  fun _ hf _ _ hsm _ hq => NSFormalization.Section4.D01.forceSobolevENorm_ne_top hf hsm hq

#print axioms NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top
#print axioms NSFormalization.Section4.D01.forceSobolevENorm_ne_top
#print axioms NSFormalization.Section4.D01.forceSobolevENormL2_half_ne_top

end BlowupDensity.Contracts.V1.Data
