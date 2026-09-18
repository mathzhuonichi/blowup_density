import Contracts.V1.Packet
import Contracts.V1.Data
import Bindings.Packet
import NSFormalization.Section3.T24.AffineSpeed

noncomputable section

namespace BlowupDensity.T24.ProbeAffineSpeed

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff

/-! The registered-spelling fragment of `AffineVariationAPI.speed_unbounded`.
These definitions are copied exactly from `research/T24/Spec.lean`, as research
files are checked directly rather than imported as library modules. -/
namespace AffineSpec

def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space,
      BlowupDensity.Contracts.V1.spatialDivergence b t x = 0)

def affineVelocity (U b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ U z + b z

end AffineSpec

example (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) :
    AffineSpec.AffineAdmissible c r τ₀ τ₁ b =
      NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b := rfl

example (U b : SpaceTimeField) :
    AffineSpec.affineVelocity U b =
      NSFormalization.Section3.T24.affineVelocity U b := rfl

/-! Closure of the exact registered `AffineVariationAPI.speed_unbounded`
field on the packet selected by the binding. -/
example (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₁ : τ₁ < 1) :
    ∀ b : SpaceTimeField, AffineSpec.AffineAdmissible c r τ₀ τ₁ b →
      BlowupDensity.Contracts.V1.SpeedUnboundedAtOne
        (AffineSpec.affineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b) := by
  exact NSFormalization.Section3.T24.speed_unbounded c r τ₀ τ₁ hτ₁
    (BlowupDensity.Bindings.packet ν hν).speed_unbounded

/-! The zero variation is an actual admissible input, and the Ua5 conclusion
for it is the registered packet's non-vacuous unbounded-speed clause. -/
example (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₁ : τ₁ < 1) :
    AffineSpec.AffineAdmissible c r τ₀ τ₁ (0 : SpaceTimeField) ∧
      BlowupDensity.Contracts.V1.SpeedUnboundedAtOne
        (AffineSpec.affineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity 0) := by
  have hb : NSFormalization.Section3.T24.AffineAdmissible
      c r τ₀ τ₁ (0 : SpaceTimeField) := by
    refine ⟨contDiff_zero_fun, HasCompactSupport.zero, ?_, ?_⟩
    · simp
    · intro t x
      simp [spatialDivergence, spatialDerivative]
  refine ⟨hb, ?_⟩
  exact NSFormalization.Section3.T24.speed_unbounded c r τ₀ τ₁ hτ₁
    (BlowupDensity.Bindings.packet ν hν).speed_unbounded 0 hb

end BlowupDensity.T24.ProbeAffineSpeed
