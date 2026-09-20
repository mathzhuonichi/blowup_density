import Contracts.V1.Packet
import Bindings.Packet
import NSFormalization.Section3.T24.AffineMomentum

/-!
# Ua3 probe — the registered `AffineVariationAPI.momentum` field on the canonical packet

Run from `verification/` with
`lake env lean ../research/T24/probes/affine_momentum_closes.lean`.

Three things are checked:

* `momentum_on_canonical` — the `eq:affine` ① momentum obligation of
  `AffineVariationAPI` (`research/T24/Spec.lean:1047`), stated in the **registered**
  `Contracts.V1` whole-space vocabulary on the selected packet
  `Bindings.packet ν hν`, is discharged by `NSFormalization.Section3.T24.momentum`
  fed the packet's own `velocity_smooth` and `navier_stokes` fields.  The affine
  vocabulary is restated here byte-for-byte from `research/T24/Spec.lean:961-990`
  (Contracts operators); the `Contracts.V1 ≡ NavierStokesR3.ProblemStatement`
  residual/operator identities are all `rfl`, so `exact` closes across the
  ambient bridge.
* `zero_admissible` — the admissible class is inhabited (the zero perturbation is
  admissible for any cylinder), so the `∀ b` field is not vacuous over an empty
  class.
* `affineVelocity_zero` / `affineForce_zero` — at `b = 0` the affine variation is
  exactly the packet `(U, P, F)`, so `momentum` specializes to the packet PDE
  `navierStokesResidual ν U P = F` — a genuine, non-tautological identity.

A **nonzero** admissible witness (a smooth compactly supported divergence-free
`b` inside the cylinder) is the curl-bump construction of unit **Ua7**
(`NavierStokes.SpatialCurl.spatialDivergence_spatialCurl` + a compactly supported
vector potential + a time bump in `(τ₀,τ₁)`); it is not reproduced here.  The
proven `momentum` theorem is `∀ b` admissible, so it consumes any such `b`.
-/

noncomputable section

namespace BlowupDensity.T24.Probe

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

def affineVelocity (U b : VelocityField) : VelocityField :=
  fun z ↦ U z + b z

def affinePressure (P : PressureField) : PressureField := P

def affineForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-! ## The registered momentum field, discharged on the canonical packet -/

/-- `AffineVariationAPI.momentum` (`research/T24/Spec.lean:1047`) for the selected
packet `Bindings.packet ν hν`, in registered `Contracts.V1` vocabulary. -/
theorem momentum_on_canonical (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        navierStokesResidual ν
            (affineVelocity (BlowupDensity.Bindings.packet ν hν).velocity b)
            (affinePressure (BlowupDensity.Bindings.packet ν hν).pressure) t x =
          affineForce ν (BlowupDensity.Bindings.packet ν hν).velocity
            (BlowupDensity.Bindings.packet ν hν).force b (t, x) := by
  intro b hb t ht x
  exact NSFormalization.Section3.T24.momentum c r τ₀ τ₁
    (BlowupDensity.Bindings.packet ν hν).velocity_smooth
    (BlowupDensity.Bindings.packet ν hν).navier_stokes b hb t ht x

/-! ## Non-vacuity -/

/-- The zero perturbation is admissible for any cylinder, so the admissible class
is inhabited (the `∀ b` field is not vacuous). -/
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

/-- At `b = 0` the affine velocity is exactly the packet velocity. -/
theorem affineVelocity_zero (U : VelocityField) :
    affineVelocity U (fun _ => 0) = U := by
  funext z; simp [affineVelocity]

/-- At `b = 0` the modified force is exactly the packet force `F`, so `momentum`
specializes to the packet PDE — a genuine, non-tautological identity. -/
theorem affineForce_zero (ν : ℝ) (U F : VelocityField) :
    affineForce ν U F (fun _ => 0) = F := by
  funext z
  simp [affineForce, crossAdvection, spatialDerivative, temporalDerivative,
    spatialLaplacian]

#print axioms momentum_on_canonical
#print axioms zero_admissible
#print axioms affineVelocity_zero
#print axioms affineForce_zero

end BlowupDensity.T24.Probe
