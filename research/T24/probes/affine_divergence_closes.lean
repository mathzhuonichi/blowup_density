import Contracts.V1.Data
import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineDivergence

noncomputable section

namespace BlowupDensity.T24.ProbeUa2

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff

/-! `research/` is not a Lake source root, so the probe repeats only the three
registered-spelling definitions needed by the `AffineVariationAPI.divergence_free`
field.  The bridges below ensure that they remain definitionally identical to
the canonical raw-field definitions. -/
namespace AffineSpec

def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

def affineVelocity (U b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ U z + b z

end AffineSpec

example (c : Space) (r τ₀ τ₁ : ℝ) :
    AffineSpec.affineCylinder c r τ₀ τ₁ =
      NSFormalization.Section3.T24.affineCylinder c r τ₀ τ₁ := rfl

example (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) :
    AffineSpec.AffineAdmissible c r τ₀ τ₁ b =
      NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b := rfl

example (U b : SpaceTimeField) :
    AffineSpec.affineVelocity U b =
      NSFormalization.Section3.T24.affineVelocity U b := rfl

/-! Exact registered spelling of the Ua2 field, instantiated at the selected
packet.  Its two raw inputs are precisely `PacketAPI.velocity_smooth` and
`PacketAPI.divergence_free`. -/
example (nu : ℝ) (hnu : 0 < nu) (c : Space) (r τ₀ τ₁ : ℝ) :
    ∀ b : SpaceTimeField, AffineSpec.AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence
          (AffineSpec.affineVelocity
            (BlowupDensity.Bindings.packet nu hnu).velocity b) t x = 0 := by
  exact NSFormalization.Section3.T24.divergence_free c r τ₀ τ₁
    (BlowupDensity.Bindings.packet nu hnu).velocity_smooth
    (BlowupDensity.Bindings.packet nu hnu).divergence_free

/-! Non-vacuity: `b = 0` is admissible for every cylinder, and the registered
Ua2 conclusion closes for that concrete perturbation of the selected packet. -/
example (nu : ℝ) (hnu : 0 < nu) (c : Space) (r τ₀ τ₁ : ℝ) :
    AffineSpec.AffineAdmissible c r τ₀ τ₁
        (fun _ : SpaceTime ↦ (0 : Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
        spatialDivergence
          (AffineSpec.affineVelocity
            (BlowupDensity.Bindings.packet nu hnu).velocity
            (fun _ : SpaceTime ↦ (0 : Space))) t x = 0 := by
  have hzero : AffineSpec.AffineAdmissible c r τ₀ τ₁
      (fun _ : SpaceTime ↦ (0 : Space)) := by
    refine ⟨contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
    · simp [AffineSpec.affineCylinder]
    · intro t x
      simp [spatialDivergence, spatialDerivative]
  refine ⟨hzero, ?_⟩
  exact NSFormalization.Section3.T24.divergence_free c r τ₀ τ₁
    (BlowupDensity.Bindings.packet nu hnu).velocity_smooth
    (BlowupDensity.Bindings.packet nu hnu).divergence_free
    (fun _ : SpaceTime ↦ (0 : Space)) hzero

end BlowupDensity.T24.ProbeUa2
