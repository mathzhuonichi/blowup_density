import Contracts.V1.Packet

/-!
# T14 reconciled specification: packet import and packet energy

This contract asserts the whole-space packet import and the two `eq:packetenergy`
relations of `lem:packetenergy` (`paper/sections/02-preliminaries.tex:127-153`)
for the packet of `paper/sections/01-introduction.tex:15-29`, before the
placement and periodization consumed by T15 at
`paper/sections/03-torus.tex:101-123`.

This is the statement-only reconciliation selected by
`research/T14/RECONCILIATION.md`: Draft B's predicate over a given registered
packet and its two separate energy fields, together with Draft B's imported
packet/existential packaging and Draft A's data-carrying selected family.

T14 is the whole-space source packet consumed before the placement and
periodization in `paper/sections/03-torus.tex:101-123`.  It therefore reuses
`Contracts.V1.PacketAPI` literally and introduces no periodic proxy.

## T10 vocabulary policy

This standalone research file begins with the same two imports as
`research/T10/Spec.lean:1-2`, then imports the registered packet contract.
Research files are not Lake modules, so it does not import `research/T10/Spec.lean`.
The minimal set of T10 declarations needed by the binding T14 reconciliation is
empty: `lem:packetenergy` is wholly Euclidean, while the first T10 objects enter
only after T15 periodizes the rescaled packet.  Consequently no T10 declaration
is copied here.  In particular, this file neither duplicates nor renames
`PeriodicSobolev`, `IsPeriodicDatum`, `periodicSobolevENorm`, the homogeneous
datum/norm, `meanT`, `torusLift`, or `periodicFourierCoeff`.  If a later revision
needs one of them before `T01.torus_data` is registered, it must be copied
verbatim with the synchronization header required by the lane brief.

All inherited `M`, `D`, quiet-interval, and negative-time-extension clauses are
already concrete fields of `PacketAPI`; T14 adds only the two relations in
`eq:packetenergy`.  Declaring these structures or propositions supplies no
inhabitant and proves no existence theorem.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory

/-- `paper/sections/02-preliminaries.tex:141`: the accumulated force
`N(t) = ∫₀ᵗ ‖F(s)‖₂ ds` of the whole-space packet later rescaled and periodized
at `paper/sections/03-torus.tex:101-120`.

For T14 the paper only evaluates this at `0 ≤ t < 1`.  The set integral over
`Ioo 0 t` is endpoint-insensitive for Lebesgue measure and agrees with the
displayed integral once the packet's smooth compactly supported force supplies
integrability. -/
def accumulatedForce (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t, Real.sqrt (l2Sq F s)

/-- The two relations of `eq:packetenergy`,
`paper/sections/02-preliminaries.tex:145-150`, imposed on one fixed registered
whole-space packet.  The same packet is the input to the torus construction at
`paper/sections/03-torus.tex:101-123`; periodization is not part of T14.

The predicate is separate from `PacketImportAPI` so later consumers can state
the energy hypothesis over an already selected `PacketAPI`. -/
structure PacketEnergyAPI {ν : ℝ} (P : PacketAPI ν) : Prop where
  /-- `paper/sections/02-preliminaries.tex:146-148`: for every `0 ≤ t < 1`,
  `‖U(t)‖₂² + 2ν∫₀ᵗ‖∇U(s)‖₂² ds ≤ 2∫₀ᵗ‖F(s)‖₂N(s) ds`.
  This quantitative packet bound underlies the finite rescaled energy in
  `paper/sections/03-torus.tex:125-128`.

  Exact quantifier order: `∀ t`, then membership in `[0,1)`.

  Non-vacuity: both sides are explicit real-valued integrals of fields carried
  by `P`; the conclusion is the paper's inequality with exact factors `2ν` and
  `2`, not an unconstrained proposition parameter. -/
  energy_le_work : ∀ t ∈ Ico (0 : ℝ) 1,
    l2Sq P.velocity t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation P.velocity s)
      ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)

  /-- `paper/sections/02-preliminaries.tex:148`: the right-hand work integral
  is exactly `N(t)²`, with the same `N` used in `energy_le_work`; this is the
  identity behind the packet estimate consumed at
  `paper/sections/03-torus.tex:125-128`.

  Exact quantifier order: `∀ t`, then membership in `[0,1)`.

  Non-vacuity: this equates two concrete real quantities and retains the
  rightmost equality of the paper's chained display rather than weakening the
  entire chain to a single upper bound. -/
  work_eq_square : ∀ t ∈ Ico (0 : ℝ) 1,
    2 * (∫ s in Ioo (0 : ℝ) t,
      Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)
      = accumulatedForce P.force t ^ 2

/-- The registered packet of `paper/sections/01-introduction.tex:15-29`, with
the two-field energy predicate from `paper/sections/02-preliminaries.tex:127-153`.
This is the single source packet placed in a coordinate ball at
`paper/sections/03-torus.tex:101-123`.

All `U,P,F,K,M,D,τ`, regularity, support, PDE, blowup, exact `IsLUB`, exact
dissipation integral, common quiet interval, and smooth zero-extension clauses
are inherited literally from `PacketAPI`. -/
structure PacketImportAPI (ν : ℝ) extends PacketAPI ν where
  /-- The full `eq:packetenergy` predicate for the inherited packet, not for a
  separately chosen witness; its zero extensions are used at
  `paper/sections/03-torus.tex:108-123,141`.

  Non-vacuity: the field constrains `toPacketAPI` through two explicit numerical
  relations and cannot be filled by choosing an unrelated packet. -/
  energy : PacketEnergyAPI toPacketAPI

/-- The paper's existential quantifier order:
`∀ ν, 0 < ν → ∃` one imported packet with `eq:packetenergy`;
`paper/sections/01-introduction.tex:15-29`,
`paper/sections/02-preliminaries.tex:127-153`.  The resulting packet is later
placed and periodized at `paper/sections/03-torus.tex:101-123`.

This is only a proposition; defining it asserts no inhabitant. -/
def packetImportStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → Nonempty (PacketImportAPI ν)

/-- A data-carrying choice of one energy-enhanced source packet at every
positive viscosity.  It implements the manuscript instruction to fix one
packet before the rescaling at `paper/sections/03-torus.tex:101-111`, while
retaining the same `ν`-then-positivity order as `packetImportStatement`.

Declaring the structure does not construct such a family. -/
structure PacketImportFamily where
  /-- The chosen energy-enhanced packet at viscosity `ν > 0`.

  Non-vacuity: the result is the full concrete `PacketImportAPI ν`, so one
  choice simultaneously supplies all registered packet data and both exact
  energy relations used before `paper/sections/03-torus.tex:122-128`. -/
  select : ∀ ν : ℝ, 0 < ν → PacketImportAPI ν

end BlowupDensity.Contracts.V1
