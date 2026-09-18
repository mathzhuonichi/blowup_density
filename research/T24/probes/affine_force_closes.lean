import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineForce

/-!
# Ua4 probe — the registered `force_smooth`/`force_support` fields on the canonical packet

Run from `verification/` with
`lake env lean ../research/T24/probes/affine_force_closes.lean`.

Four things are checked:

* `force_smooth_on_canonical` — the `prop:affine` ② smoothness obligation of
  `AffineVariationAPI` (`research/T24/Spec.lean:1025`), stated in the **registered**
  `Contracts.V1` whole-space vocabulary on the selected packet
  `Bindings.packet ν hν`, is discharged by
  `NSFormalization.Section3.T24.force_smooth` fed the packet's own
  `velocity_smooth` and `force_smooth` fields.
* `force_support_on_canonical` — likewise `research/T24/Spec.lean:1032`, discharged
  by `NSFormalization.Section3.T24.force_support` fed the packet's `force_support`.

  The affine vocabulary is restated here byte-for-byte from
  `research/T24/Spec.lean:961-990` (Contracts operators); the
  `Contracts.V1 ≡ NavierStokesR3.ProblemStatement` operator/support identities are
  all `rfl` (`Bindings/Packet.lean` correspondence block), so `exact` closes across
  the ambient bridge.
* `zero_admissible` — the admissible class is inhabited, so the `∀ b` fields are
  not vacuous over an empty class.
* `affineForce_zero` + `force_smooth_zero_reduction` /
  `force_support_zero_reduction` — at `b = 0` the corrected force is exactly the
  packet force `F`, so the two Ua4 fields specialize to the packet's own
  `force_smooth` / `force_support` clauses: genuine, non-tautological identities.

A **nonzero** admissible witness and both conclusions instantiated at it are in
`research/T24/probes/affine_force_nonzero.lean`.
-/

noncomputable section

namespace BlowupDensity.T24.ForceProbe

open Set
open BlowupDensity.Contracts.V1
open scoped ContDiff

/-! ## Registered-vocabulary affine defs (verbatim `research/T24/Spec.lean:961-990`) -/

def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : VelocityField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

def crossAdvection (v w : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

def affineForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-! ## The two registered Ua4 fields, discharged on the canonical packet -/

/-- `AffineVariationAPI.force_smooth` (`research/T24/Spec.lean:1025`) for the
selected packet `Bindings.packet ν hν`, in registered `Contracts.V1` vocabulary.
The cylinder hypotheses `0 < τ₀`, `τ₁ < 1` are the parameter hypotheses of
`affineVariationStatement` (`:1117`). -/
theorem force_smooth_on_canonical (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ContDiff ℝ ∞ (affineForce ν (BlowupDensity.Bindings.packet ν hν).velocity
        (BlowupDensity.Bindings.packet ν hν).force b) := by
  intro b hb
  exact NSFormalization.Section3.T24.force_smooth c r τ₀ τ₁ hτ₀ hτ₁
    (BlowupDensity.Bindings.packet ν hν).velocity_smooth
    (BlowupDensity.Bindings.packet ν hν).force_smooth b hb

/-- `AffineVariationAPI.force_support` (`research/T24/Spec.lean:1032`) for the
selected packet `Bindings.packet ν hν`, in registered `Contracts.V1` vocabulary.
Only `0 < τ₀` is needed. -/
theorem force_support_on_canonical (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      CompactPositiveTimeSupport (affineForce ν
        (BlowupDensity.Bindings.packet ν hν).velocity
        (BlowupDensity.Bindings.packet ν hν).force b) := by
  intro b hb
  exact NSFormalization.Section3.T24.force_support c r τ₀ τ₁ hτ₀
    (BlowupDensity.Bindings.packet ν hν).force_support b hb

/-! ## Non-vacuity and the `b = 0` reduction -/

/-- The zero perturbation is admissible for any cylinder, so the admissible class
is inhabited (the `∀ b` fields are not vacuous). -/
theorem zero_admissible (c : Space) (r τ₀ τ₁ : ℝ) :
    AffineAdmissible c r τ₀ τ₁ (fun _ => 0) := by
  have h0 : tsupport (fun _ : SpaceTime => (0 : Space)) = (∅ : Set SpaceTime) := by
    simp [tsupport]
  refine ⟨contDiff_const, ?_, ?_, ?_⟩
  · show IsCompact (tsupport (fun _ : SpaceTime => (0 : Space)))
    rw [h0]; exact isCompact_empty
  · rw [h0]; exact empty_subset _
  · intro t x
    simp [spatialDivergence, spatialDerivative]

/-- At `b = 0` the corrected force is exactly the packet force `F`. -/
theorem affineForce_zero (ν : ℝ) (U F : VelocityField) :
    affineForce ν U F (fun _ => 0) = F := by
  funext z
  simp [affineForce, crossAdvection, spatialDerivative, temporalDerivative,
    spatialLaplacian]

/-- At `b = 0` the Ua4 smoothness field is exactly the packet clause
`PacketAPI.force_smooth` — a genuine, non-tautological identity. -/
theorem force_smooth_zero_reduction (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1) :
    ContDiff ℝ ∞ (BlowupDensity.Bindings.packet ν hν).force := by
  have h := force_smooth_on_canonical ν hν c r τ₀ τ₁ hτ₀ hτ₁ (fun _ => 0)
    (zero_admissible c r τ₀ τ₁)
  rwa [affineForce_zero] at h

/-- At `b = 0` the Ua4 support field is exactly the packet clause
`PacketAPI.force_support`. -/
theorem force_support_zero_reduction (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) :
    CompactPositiveTimeSupport (BlowupDensity.Bindings.packet ν hν).force := by
  have h := force_support_on_canonical ν hν c r τ₀ τ₁ hτ₀ (fun _ => 0)
    (zero_admissible c r τ₀ τ₁)
  rwa [affineForce_zero] at h

#print axioms force_smooth_on_canonical
#print axioms force_support_on_canonical
#print axioms zero_admissible
#print axioms affineForce_zero
#print axioms force_smooth_zero_reduction
#print axioms force_support_zero_reduction

end BlowupDensity.T24.ForceProbe
