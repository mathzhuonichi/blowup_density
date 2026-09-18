import Contracts.V1.Data
import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineEnergy

/-!
# Probe: T24a Ua6 `energy_finite` closes against the registered spelling

Three checks, in the pattern of `research/T24/probes/uc1_ua1_closes.lean`:

1. the three `rfl` bridges from the canonical `Section3.T24` restatement of
   `E_T` to the registered `Contracts.V1.Data.{energyEssSup, energyGradient,
   energyENorm}` (`verification/Contracts/V1/Data.lean:444-476`);
2. the `Spec.lean:1076-1077` field `energy_finite`, written in the registered
   vocabulary over `BlowupDensity.Bindings.packet ν hν`, discharged by
   `NSFormalization.Section3.T24.energy_finite`.  The packet's own
   `‖U‖_{E_1} < ∞` clause is threaded as a hypothesis: `Contracts.V1.PacketAPI`
   carries `energy_isLUB` and `dissipation_eq` instead of the assembled `E_1`
   bound, and assembling them is a separate unit, not Ua6;
3. non-vacuity: `b = 0` is admissible, so the quantifier in the field is not
   empty, and the `b = 0` instance really is the `U` statement.

Every `example` below is closed; the module itself is audited in `research/T24/axioms_ua6.lean`.
-/

noncomputable section

namespace BlowupDensity.T24.ProbeUa6

open Set MeasureTheory
open scoped ContDiff ENNReal

/-- The registered spacetime vector field type, spelled out so that the probe
depends on no `open`. -/
local notation "Field" => BlowupDensity.Contracts.V1.VelocityField

/-- The registered spatial type. -/
local notation "Pt" => BlowupDensity.Contracts.V1.Space

/-! ## 1. The canonical `E_T` restatement is the registered one -/

example (T : ℝ) (z : Field) :
    BlowupDensity.Contracts.V1.Data.energyEssSup T z =
      NSFormalization.Section3.T24.energyEssSup T z := rfl

example (T : ℝ) (z : Field) :
    BlowupDensity.Contracts.V1.Data.energyGradient T z =
      NSFormalization.Section3.T24.energyGradient T z := rfl

example (T : ℝ) (z : Field) :
    BlowupDensity.Contracts.V1.Data.energyENorm T z =
      NSFormalization.Section3.T24.energyENorm T z := rfl

example (z : Field) (t : ℝ) (x : Pt) :
    BlowupDensity.Contracts.V1.Data.spatialGradient z t x =
      NSFormalization.Section4.I02.spatialGradient z t x := rfl

/-! ## 2. The `Spec.lean` fragments, in the registered vocabulary

Copied here rather than importing a `research/` file as a Lean module, exactly
as in `uc1_ua1_closes.lean`. -/

namespace AffineSpec

def specAffineCylinder (c : Pt) (r τ₀ τ₁ : ℝ) : Set BlowupDensity.Contracts.V1.SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def specAffineAdmissible (c : Pt) (r τ₀ τ₁ : ℝ) (b : Field) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ specAffineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Pt,
      BlowupDensity.Contracts.V1.spatialDivergence b t x = 0)

def specAffineVelocity (U b : Field) : Field :=
  fun z ↦ U z + b z

end AffineSpec

example (c : Pt) (r τ₀ τ₁ : ℝ) (b : Field) :
    AffineSpec.specAffineAdmissible c r τ₀ τ₁ b =
      NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b := rfl

example (u b : Field) :
    AffineSpec.specAffineVelocity u b =
      NSFormalization.Section3.T24.affineVelocity u b := rfl

/-! ## 3. `Spec.lean:1076-1077` on the registered packet -/

example (ν : ℝ) (hν : 0 < ν) (c : Pt) (r τ₀ τ₁ : ℝ)
    (henergy : BlowupDensity.Contracts.V1.Data.energyENorm 1
      (BlowupDensity.Bindings.packet ν hν).velocity < ⊤) :
    ∀ b : Field, AffineSpec.specAffineAdmissible c r τ₀ τ₁ b →
      BlowupDensity.Contracts.V1.Data.energyENorm 1
        (AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b) < ⊤ :=
  NSFormalization.Section3.T24.energy_finite c r τ₀ τ₁ henergy

/-- The same statement for an arbitrary raw velocity, i.e. without selecting a
packet: the hypothesis is the only packet clause used. -/
example (U : Field) (c : Pt) (r τ₀ τ₁ : ℝ)
    (henergy : BlowupDensity.Contracts.V1.Data.energyENorm 1 U < ⊤) :
    ∀ b : Field, AffineSpec.specAffineAdmissible c r τ₀ τ₁ b →
      BlowupDensity.Contracts.V1.Data.energyENorm 1
        (AffineSpec.specAffineVelocity U b) < ⊤ :=
  NSFormalization.Section3.T24.energy_finite c r τ₀ τ₁ henergy

/-! ## 4. Non-vacuity -/

/-- The zero variation is admissible, so the `∀ b` in the field is not empty. -/
example (c : Pt) (r τ₀ τ₁ : ℝ) :
    AffineSpec.specAffineAdmissible c r τ₀ τ₁ (fun _ : BlowupDensity.Contracts.V1.SpaceTime => (0 : Pt)) := by
  refine ⟨contDiff_const, ?_, ?_, ?_⟩
  · exact HasCompactSupport.intro isCompact_empty (fun _ _ => rfl)
  · have h : tsupport (fun _ : BlowupDensity.Contracts.V1.SpaceTime => (0 : Pt)) = ∅ := by
      simp
    rw [h]
    exact Set.empty_subset _
  · intro t x
    show ∑ i : Fin 3, (fderiv ℝ (fun _ : Pt => (0 : Pt)) x
      (BlowupDensity.Contracts.V1.coordinateVector i)) i = 0
    simp

/-- At `b = 0` the conclusion is exactly the hypothesis, so the field is a
genuine constraint on `U` and not a vacuous one. -/
example (U : Field) :
    BlowupDensity.Contracts.V1.Data.energyENorm 1
        (AffineSpec.specAffineVelocity U (fun _ : BlowupDensity.Contracts.V1.SpaceTime => (0 : Pt))) =
      BlowupDensity.Contracts.V1.Data.energyENorm 1 U := by
  have h : AffineSpec.specAffineVelocity U (fun _ : BlowupDensity.Contracts.V1.SpaceTime => (0 : Pt)) = U := by
    funext z
    simp [AffineSpec.specAffineVelocity]
  rw [h]

end BlowupDensity.T24.ProbeUa6
