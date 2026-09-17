import Contracts.V1.Packet

/-!
# T14: independent statement draft B

`thm:packet` is at `01-introduction.tex:15-28`, not in `03-torus.tex`;
`lem:packetenergy` is at `02-preliminaries.tex:127-153`.
Reuse the registered whole-space packet literally. The single-copy periodic
placement is the subsequent T15 operation (`03-torus.tex:101-123`).
No existence theorem or proof is asserted by these structure declarations.
-/

noncomputable section
namespace BlowupDensity.T14.DraftB

open Set MeasureTheory
open BlowupDensity.Contracts.V1

/-- `02-preliminaries.tex:141`: the literal expression
`N(t) = ∫₀ᵗ ‖F(s)‖₂ ds`. Needs registration / to be aligned with T10.
This is a whole-space norm, not a periodic norm. The set-integral convention
is used only for `0 ≤ t < 1`; endpoints are Lebesgue null. Smooth compact
support supplies integrability, so neither integral is a junk totalized value. -/
def accumulatedForce (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t, Real.sqrt (l2Sq F s)

/-- The missing display `eq:packetenergy`, `02-preliminaries.tex:146-148`,
for the *same* packet already carrying `M`, `D`, and `τ` in `PacketAPI`.
Quantification over time includes zero and excludes the singular endpoint.
The two fields retain both relations of the printed inequality/equality chain. -/
structure PacketEnergyAPI {ν : ℝ} (P : PacketAPI ν) : Prop where
  /-- `02-preliminaries.tex:147-148`: exact factor `2ν` on dissipation,
  and exact factor `2` on the force work upper bound. -/
  energy_le_work : ∀ t ∈ Ico (0 : ℝ) 1,
    l2Sq P.velocity t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation P.velocity s)
      ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)
  /-- `02-preliminaries.tex:148`: the rightmost equality, with no unspecified
  constant and no replacement of `N(t)` by its terminal bound. -/
  work_eq_square : ∀ t ∈ Ico (0 : ℝ) 1,
    2 * (∫ s in Ioo (0 : ℝ) t,
      Real.sqrt (l2Sq P.force s) * accumulatedForce P.force s)
      = accumulatedForce P.force t ^ 2

/-- The imported existential object of `01-introduction.tex:16-28`, enhanced
by `02-preliminaries.tex:130-133,146-152`. Inherited data are exactly
`U,P,F,K,M,D,τ`; inherited propositions include their regularity, supports,
PDE, blowup, exact `IsLUB` definition of `M`, exact integral definition of
`D`, initial quiet interval, and smooth negative-time zero extensions.
`PacketAPI` also retains the extension PDE clauses consumed at
`03-torus.tex:108-123,141`. No new torus norm is postulated here. -/
structure PacketImportAPI (ν : ℝ) extends PacketAPI ν where
  /-- The display `eq:packetenergy`, `02-preliminaries.tex:146-148`, for the
  inherited packet, not for a separately chosen existential witness. -/
  energy : PacketEnergyAPI toPacketAPI

/-- `01-introduction.tex:16-28` then `02-preliminaries.tex:127-153`:
`∀ ν > 0, ∃ U P F K M D τ, ...`. All packet data follow the viscosity.
This proposition is a statement only, with no claimed inhabitant. -/
def packetImportStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → Nonempty (PacketImportAPI ν)

/-- `02-preliminaries.tex:123-148`: energy holds for any fixed registered
packet. This universal obligation permits enhancing `Bindings.packet ν hν`
without replacing the already selected packet family. -/
def packetEnergyStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν), PacketEnergyAPI P

-- Mathlib and registered vocabulary checks used by the statements above.
#check Real.sqrt
#check IsLUB
#check MeasureTheory.IntegrableOn
#check MeasureTheory.integral
#check ContDiffOn
#check PacketAPI
#check PacketAPI.energy_isLUB
#check PacketAPI.dissipation_eq
#check PacketAPI.velocity_extension_smooth

end BlowupDensity.T14.DraftB
