import Contracts.V1.EnergyHighPartial
import Bindings.Uniqueness
import Bindings.TameProduct
import NSFormalization.Section4.A04.EnergyIdentityHigh
import NSFormalization.Section4.A04.GradientFiniteness

/-! The only layer that knows the current implementation's names and paths for the
proved part of A04 unit G1 (eq:Rhigh).

`Contracts.V1.EnergyHighPartial` is self-contained — its only imports are
`Contracts.V1.Data` and `Contracts.V1.TameProduct` — so this adapter has two jobs:
record by `rfl` that each spec-local `def` the specification restates is the notion
the proof module uses, and assemble the proved theorem into the contract.

* `energyIdentityHigh` — `NSFormalization.Section4.A04.energyIdentityHigh` verbatim,
  applied to the solution moved across the two `ClassicalSolutionR` copies by the
  reused `Bindings.uniqueness_toA02` (`Contracts.V1.Data.ClassicalSolutionR` and the
  `Section4/A02` restatement are distinct inductive types, so a `rfl` bridge for the
  structure itself is impossible; each field type is defeq, so the field-wise
  conversion typechecks — the CLAUDE.md structure exception).  The conclusion needs
  no adjustment: `(uniqueness_toA02 w).velocity = w.velocity` by `rfl`, and
  `w.velocity` is the only projection the statement mentions; the three restated
  notions are drift-guarded by the `rfl` bridges below.
* `Chigh` / `Chigh_pos` — bound to `A04.Chigh` / `A04.Chigh_pos`.  Since
  `A04.Chigh m = A03.outerTameConst m` and the registered `TameProductAPI.Ctame` is
  the same `A03.outerTameConst` (`Bindings/TameProduct.lean`), the bonus
  `energyHighPartial_Chigh_eq_Ctame` records `Chigh = tameProduct.Ctame` by `rfl`
  (which unit G2's `Cgron` will want; `research/A04/REVIEW_ENERGY_HIGH.md` finding
  6).  The contract keeps `Chigh` opaque, so this is a binding-level fact only.

Every declaration here carries an `energyHighPartial_` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

section Correspondence

/-- The contract's `sobolevNormAt` is the implementation's
(`Section4/A04/Forcing.lean:74`); `Data.sobolevENorm` is defeq to `D01.sobolevENorm`. -/
theorem energyHighPartial_sobolevNormAt_eq :
    Contracts.V1.EnergyHighPartial.sobolevNormAt
      = NSFormalization.Section4.A04.sobolevNormAt := rfl

/-- The contract's `gradientSobolevNormAt` is the implementation's
(`Section4/A04/LaplacianDatum.lean:86`); `TameProduct.gradientSobolevENorm` is defeq
to `A03.gradientSobolevENorm`. -/
theorem energyHighPartial_gradientSobolevNormAt_eq :
    Contracts.V1.EnergyHighPartial.gradientSobolevNormAt
      = NSFormalization.Section4.A04.gradientSobolevNormAt := rfl

/-- The contract's `HasSmoothSobolevPath` is the implementation's
(`Section4/A04/DerivNorm.lean:87`); `Data.IsSobolevDatum` is defeq to
`D01.IsSobolevDatum`. -/
theorem energyHighPartial_hasSmoothSobolevPath_eq :
    Contracts.V1.EnergyHighPartial.HasSmoothSobolevPath
      = NSFormalization.Section4.A04.HasSmoothSobolevPath := rfl

end Correspondence

/-- Bind the proved eq:Rhigh field to the stable version-one contract. -/
def energyHighPartial :
    Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI where
  Chigh := NSFormalization.Section4.A04.Chigh
  Chigh_pos := NSFormalization.Section4.A04.Chigh_pos
  energyIdentityHigh := fun ν a f T hν ha hf w hpath m hm t ht =>
    NSFormalization.Section4.A04.energyIdentityHigh ν a f T hν ha hf
      (uniqueness_toA02 w) hpath m hm t ht

/-- Bonus (not a contract field): the bound constant `Chigh` is the registered
`TameProductAPI.Ctame`, both `A03.outerTameConst`, by `rfl`.  Unit G2's
`Cgron m ν = (Chigh m)²/(4ν)` will consume it. -/
theorem energyHighPartial_Chigh_eq_Ctame :
    energyHighPartial.Chigh = tameProduct.Ctame := rfl

/-- Bonus (not a contract field): eq:Rhigh's dissipation `‖∇u‖_{H^m}` is a genuine
finite norm on a classical-solution velocity slice — the contract's
`gradientSobolevNormAt` is not a `⊤ ↦ 0` artefact.  `Section4/A04/GradientFiniteness`
through the `TameProduct.gradientSobolevENorm = A03.gradientSobolevENorm` `rfl`
identification and `(uniqueness_toA02 w).velocity = w.velocity`. -/
theorem energyHighPartial_gradientSobolevENorm_velocity_ne_top
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    Contracts.V1.TameProduct.gradientSobolevENorm (m : ℝ)
        (fun x : Space => w.velocity (t, x)) ≠ ⊤ :=
  NSFormalization.Section4.A04.gradientSobolevENorm_velocity_ne_top (uniqueness_toA02 w) m ht

end BlowupDensity.Bindings
