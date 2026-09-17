import Contracts.V1.Packet

/-!
# T14 draft A: packet import and packet energy

This statement draft reuses the registered Euclidean packet interface from
`Contracts.V1.Packet`.  That is the packet imported into the torus construction:
its compact spatial carrier is rescaled into one coordinate ball and only then
periodized in T15 (`paper/sections/03-torus.tex:101-120`).  No periodic Sobolev
definition from T10 is needed at this node.

The registered interface already states Theorem `thm:packet`, the constants
`M` and `D`, initial-interval vanishing, and smooth zero extension.  The one
paper clause missing from that interface is the full displayed estimate
`eq:packetenergy`; it is added below without changing the packet data.
-/

noncomputable section

namespace BlowupDensity.Research.T14.DraftA

open Set MeasureTheory
open BlowupDensity.Contracts.V1

/-- **NEEDS REGISTRATION (T14).**  The local verbatim definition
`N(t) = ∫₀ᵗ ‖F(s)‖₂ ds` from the proof of `lem:packetenergy`,
`paper/sections/02-preliminaries.tex:141`.  This is a Euclidean packet quantity,
not periodic T10 vocabulary; no alignment with T10 is required. -/
def packetForceAccumulation (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, Real.sqrt (l2Sq F s)

/-- The T14 interface at one fixed viscosity.

All inherited fields are literally those of the registered Section 4
`PacketAPI`: the data `(U,P,F,K,M,D,τ)`, the complete `thm:packet` interface,
finite energy and dissipation, the common quiet interval, and the smooth
negative-time zero extensions.  See `paper/sections/01-introduction.tex:15-29`
and `paper/sections/02-preliminaries.tex:127-153`.

The new field is exactly the two relations in the chained display
`eq:packetenergy`, `paper/sections/02-preliminaries.tex:145-150`.  Set integrals
over `(0,t]` represent the displayed integrals from `0` to `t`; endpoints are
null. -/
structure TorusPacketEnergyAPI (nu : ℝ) extends PacketAPI nu where
  /--
  `‖U(t)‖₂² + 2ν ∫₀ᵗ ‖∇U(s)‖₂² ds
      ≤ 2 ∫₀ᵗ ‖F(s)‖₂ N(s) ds = N(t)²`,
  for every `0 ≤ t < 1`; `paper/sections/02-preliminaries.tex:146-149`.
  The conjunction records both relations in the paper's chained display. -/
  packet_energy : ∀ t : ℝ, t ∈ Ico (0 : ℝ) 1 →
    (l2Sq velocity t + 2 * nu * ∫ s in Ioc (0 : ℝ) t, dissipation velocity s ≤
      2 * ∫ s in Ioc (0 : ℝ) t,
        Real.sqrt (l2Sq force s) * packetForceAccumulation force s) ∧
    (2 * ∫ s in Ioc (0 : ℝ) t,
        Real.sqrt (l2Sq force s) * packetForceAccumulation force s =
      packetForceAccumulation force t ^ 2)

/-- The literal existential quantifier order of `thm:packet`:
`∀ ν, 0 < ν → ∃` a packet with the T14 energy clauses.
`paper/sections/01-introduction.tex:15-19` and
`paper/sections/02-preliminaries.tex:127-134`. -/
def torusPacketEnergyStatement : Prop :=
  ∀ nu : ℝ, 0 < nu → Nonempty (TorusPacketEnergyAPI nu)

/-- A chosen family of T14 packets, matching the manuscript's instruction to
fix one solution at each positive viscosity before rescaling it;
`paper/sections/01-introduction.tex:61-67`.  This data-carrying form has the same
`ν`-then-positivity quantifier order as `torusPacketEnergyStatement`. -/
structure TorusPacketEnergyFamily where
  select : ∀ nu : ℝ, 0 < nu → TorusPacketEnergyAPI nu

end BlowupDensity.Research.T14.DraftA
