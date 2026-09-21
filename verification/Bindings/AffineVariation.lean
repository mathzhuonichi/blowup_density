import Contracts.V1.AffineVariation
import Bindings.Packet
import NSFormalization.Section3.T24.AffineAssembly

/-! # Binding for the T24a affine-variation contract

Two jobs, as in `Bindings/Packet.lean`.

*Drift guards.*  The seven T24a notions the contract had to write out
(`affineCylinder`, `AffineAdmissible`, `crossAdvection`, `affineVelocity`,
`affinePressure`, `affineForce`, `ckSeminormE`) each get a whole-function `rfl`
bridge to the canonical `NSFormalization.Section3.T24` declaration, so a change
on either side breaks the build rather than the meaning.  Everything else in the
contract — the packet, the operators, `CompactPositiveTimeSupport`,
`SpeedUnboundedAtOne`, `energyENorm` — is registered vocabulary and needs no
bridge here.

*Assembly.*  `packetRawData` turns any registered `PacketAPI` into the canonical
`AffineRawData` bundle; its one non-field clause `‖U‖_{E_1} < ∞` is
`Section3.T24.energyENorm_lt_top_of_packet`, assembled from `velocity_smooth`,
`carrier_compact`, `velocity_support`, `square_integrable`, `energy_isLUB` and
`dissipation_integrable`.  `affineVariation` then transports the thirteen
canonical fields into the registered record, and `affineVariationStatement_holds`
is the existence form for every viscosity, every packet and every admissible
cylinder.  `affineVariationPacket` is the instance at the selected `I01.packet`
witness `Bindings.packet ν hν`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open scoped ContDiff ENNReal Topology

/-! ## Definitional drift guards -/

/-- The contract's affine cylinder is the canonical one. -/
theorem affineCylinder_eq :
    Contracts.V1.affineCylinder = NSFormalization.Section3.T24.affineCylinder := rfl

/-- The contract's admissible perturbation class is the canonical one. -/
theorem affineAdmissible_eq :
    Contracts.V1.AffineAdmissible = NSFormalization.Section3.T24.AffineAdmissible := rfl

/-- The contract's transport term is the canonical one. -/
theorem crossAdvection_eq :
    Contracts.V1.crossAdvection = NSFormalization.Section3.T24.crossAdvection := rfl

/-- The contract's varied velocity is the canonical one. -/
theorem affineVelocity_eq :
    Contracts.V1.affineVelocity = NSFormalization.Section3.T24.affineVelocity := rfl

/-- The contract's varied pressure is the canonical one. -/
theorem affinePressure_eq :
    Contracts.V1.affinePressure = NSFormalization.Section3.T24.affinePressure := rfl

/-- The contract's six-term corrected force is the canonical one. -/
theorem affineForce_eq :
    Contracts.V1.affineForce = NSFormalization.Section3.T24.affineForce := rfl

/-- The contract's fixed-support `C^m` seminorm is the canonical one. -/
theorem ckSeminormE_eq :
    Contracts.V1.ckSeminormE = NSFormalization.Section3.T24.affineCkSeminorm := rfl

/-! ## Assembly -/

/-- Every raw clause T24a consumes is a field of the registered packet, except
`‖U‖_{E_1} < ∞`, which `Section3.T24.energyENorm_lt_top_of_packet` assembles
from four of them. -/
theorem packetRawData {ν : ℝ} (P : Contracts.V1.PacketAPI ν) :
    NSFormalization.Section3.T24.AffineRawData ν P.velocity P.pressure P.force where
  velocity_smooth := P.velocity_smooth
  force_smooth := P.force_smooth
  force_support := P.force_support
  zero_initial_velocity := P.zero_initial_velocity
  divergence_free := P.divergence_free
  navier_stokes := P.navier_stokes
  speed_unbounded := P.speed_unbounded
  energy_finite :=
    NSFormalization.Section3.T24.energyENorm_lt_top_of_packet
      P.velocity_smooth P.carrier_compact P.velocity_support P.square_integrable
      P.energy_isLUB P.dissipation_integrable

/-- Bind the thirteen clauses of `prop:affine`
(`paper/sections/03-torus.tex:668-696`) to the stable version-one contract, for
any registered packet and any cylinder with `0 < r` and `0 < τ₀ < τ₁ < 1`. -/
theorem affineVariation {ν : ℝ} (P : Contracts.V1.PacketAPI ν) (c : Contracts.V1.Space)
    {r τ₀ τ₁ : ℝ} (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    Contracts.V1.AffineVariationAPI P c r τ₀ τ₁ :=
  let h := NSFormalization.Section3.T24.affineVariationCanonical
    (packetRawData P) c hr hτ₀ hτ₀τ₁ hτ₁
  { radius_pos := h.radius_pos
    window := h.window
    force_smooth := h.force_smooth
    force_support := h.force_support
    divergence_free := h.divergence_free
    momentum := h.momentum
    zero_initial := h.zero_initial
    late_agreement := h.late_agreement
    speed_unbounded := h.speed_unbounded
    energy_finite := h.energy_finite
    infinite_dimensional := h.infinite_dimensional
    distinct := h.distinct
    nonisolated := h.nonisolated }

/-- The same record at the packet the `I01.packet` binding selects, the packet
`prop:affine` actually varies. -/
theorem affineVariationPacket (ν : ℝ) (hν : 0 < ν) (c : Contracts.V1.Space)
    {r τ₀ τ₁ : ℝ} (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    Contracts.V1.AffineVariationAPI (packet ν hν) c r τ₀ τ₁ :=
  affineVariation (packet ν hν) c hr hτ₀ hτ₀τ₁ hτ₁

/-- The existence form of `prop:affine`. -/
theorem affineVariationStatement_holds : Contracts.V1.affineVariationStatement :=
  fun _ν _hν P c _r _τ₀ _τ₁ hr hτ₀ hτ₀τ₁ hτ₁ =>
    ⟨affineVariation P c hr hτ₀ hτ₀τ₁ hτ₁⟩

end BlowupDensity.Bindings
