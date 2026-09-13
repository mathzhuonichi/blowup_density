import NSFormalization.Source.ViscosityPacket
import NSFormalization.Source.PacketScaling

/-!
# I01 draft specification: packet energy and early vanishing

Task `collaboration/tasks/I01.md`, graph node `I01` in
`formalization/blueprint/DEPENDENCY_GRAPH.md`.

This file is a *specification draft only*.  It contains definitions and one
record of obligations; it proves nothing, assumes nothing, and introduces no
axiom.  Nothing here asserts that a packet exists: `PacketAPI` is a record of
hypotheses, `packetStatement` and `PacketFamily` are propositions/records whose
inhabitation is exactly what the source construction has to supply.

The record collects, for one fixed viscosity `ν`, the obligations of

* the restated OpenAI theorem, Theorem 1.1 (`thm:packet`),
  `paper/sections/01-introduction.tex:15-34`, and
* Lemma 2.2, "Energy, dissipation and initial vanishing" (`lem:packetenergy`),
  `paper/sections/02-preliminaries.tex:127-153`,

in the exact form consumed by Proposition 3.3 (`prop:scaling`,
`paper/sections/03-torus.tex:101-159`) and Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-79`).  The explicit zero extension of the
force to nonpositive source time is the clarification `C1` of
`logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`.

Conventions.  Time is the first spacetime coordinate.  `preSingularDomain` is
`[0,1) × ℝ³`; smoothness of `U` and `P` is relative to that half-domain, as in
the OpenAI statement, so no arbitrary negative-time extension is differentiated
at `t = 0`.  Spatial supports are topological supports (`tsupport`, the closure
of the nonvanishing set), which is the paper's `supp`.  The force is modelled by
its globally smooth zero extension: a total field, smooth on all of spacetime,
whose compact support lies in `{t > 0} × ℝ³`; this is exactly
`C_c^∞(ℝ³ × (0,∞); ℝ³)` together with the zero extension of `C1`.
-/

noncomputable section

namespace BlowupDensity.I01.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime VelocityField PressureField
  preSingularDomain spatialDivergence)
open NavierStokesR3.ProblemStatement (navierStokesResidual CompactPositiveTimeSupport
  SquareIntegrableAtTime SpeedUnboundedAtOne)
open NavierStokesR3.CompactEnergy (l2Sq dissipation)
open NSFormalization.Source.PacketScaling (zeroPastField)
open scoped ContDiff

/-- Every obligation the manuscript places on the chosen packet `(U, P, F)` at
one fixed viscosity `ν > 0`.

The first seven fields are the data: `U, P, F, K` of Theorem 1.1, the two
constants `M, D` named in Lemma 2.2, and the quiet length `τ` produced in its
proof.  The propositional fields are grouped as: Theorem 1.1 proper
(`viscosity_pos` through `speed_unbounded`), the energy and dissipation
constants of Lemma 2.2 (`square_integrable` through `dissipation_eq`), the
initial quiet interval (`quiet_pos` through `pressure_quiet`), and the smooth
zero extensions to nonpositive time (`velocity_extension_smooth` onwards).

This is a specification, not a theorem: no field is a placeholder and none is
an unproved abstract proposition variable. -/
structure PacketAPI (ν : ℝ) where
  /-- `U`, the packet velocity on `ℝ³ × [0,1)`.
  Theorem 1.1, `paper/sections/01-introduction.tex:18-19`;
  named `(U, P, F)` at `paper/sections/01-introduction.tex:63-66`. -/
  velocity : VelocityField
  /-- `P`, the packet pressure on `ℝ³ × [0,1)`.
  Theorem 1.1, `paper/sections/01-introduction.tex:18-19`. -/
  pressure : PressureField
  /-- `F`, the packet force, represented by its zero extension to all times.
  Theorem 1.1, `paper/sections/01-introduction.tex:17-18`; extension convention
  `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`. -/
  force : VelocityField
  /-- `K`, the single compact spatial carrier of `U(·,t)` and `P(·,t)`.
  Theorem 1.1, `paper/sections/01-introduction.tex:17-18, 24-25`. -/
  carrier : Set Space
  /-- `M`, the uniform `L²` bound of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:130`; consumed as the coefficient of
  `ε^{1/2}` in `eq:packetEscale` and `eq:REclose`. -/
  energyBound : ℝ
  /-- `D`, the total dissipation of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:131`; consumed as the coefficient of
  `ε^{1/2}` in `eq:packetEscale` and `eq:REclose`. -/
  dissipationBound : ℝ
  /-- `τ`, the length of the initial interval on which `F`, and hence `U` and
  `P`, vanish.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  quietTime : ℝ
  /-- "For every `ν > 0`", Theorem 1.1,
  `paper/sections/01-introduction.tex:16`. -/
  viscosity_pos : 0 < ν
  /-- `U` is smooth on `ℝ³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`. -/
  velocity_smooth : ContDiffOn ℝ ∞ velocity preSingularDomain
  /-- `P` is smooth on `ℝ³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`. -/
  pressure_smooth : ContDiffOn ℝ ∞ pressure preSingularDomain
  /-- `F` is smooth on all of spacetime, i.e. its zero extension past `t = 0`
  is smooth.  Theorem 1.1, `paper/sections/01-introduction.tex:17`, together
  with `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:66-73`. -/
  force_smooth : ContDiff ℝ ∞ force
  /-- `F ∈ C_c^∞(ℝ³ × (0,∞); ℝ³)`: compact spacetime support, contained in
  strictly positive time.  Theorem 1.1,
  `paper/sections/01-introduction.tex:17-18`, with the reading spelled out at
  `paper/sections/01-introduction.tex:61-63`. -/
  force_support : CompactPositiveTimeSupport force
  /-- `K` is compact.  Theorem 1.1,
  `paper/sections/01-introduction.tex:17-18`. -/
  carrier_compact : IsCompact carrier
  /-- `supp U(·,t) ⊆ K` for every `0 ≤ t < 1`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:24-25`. -/
  velocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => velocity (t, x)) ⊆ carrier
  /-- `supp P(·,t) ⊆ K` for every `0 ≤ t < 1`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:24-25`. -/
  pressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => pressure (t, x)) ⊆ carrier
  /-- `u(·,0) = 0`.  Theorem 1.1, `eq:packet`,
  `paper/sections/01-introduction.tex:22`. -/
  zero_initial_velocity : ∀ x : Space, velocity (0, x) = 0
  /-- `∇ · u = 0` on `ℝ³ × [0,1)`.  Theorem 1.1, `eq:packet`,
  `paper/sections/01-introduction.tex:22`. -/
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence velocity t x = 0
  /-- `∂_t u + (u·∇)u - νΔu + ∇p = f` at every interior time.  Theorem 1.1,
  `eq:packet`, `paper/sections/01-introduction.tex:20-23`.  The viscosity
  multiplies only the spatial Laplacian. -/
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual ν velocity pressure t x = force (t, x)
  /-- `limsup_{t↑1} ‖u(t)‖_∞ = ∞`, in the pointwise form used by the source.
  Theorem 1.1, `eq:packetblowup`, `paper/sections/01-introduction.tex:28`;
  consumed as "unbounded speed at `T`" in `prop:scaling`,
  `paper/sections/03-torus.tex:123`. -/
  speed_unbounded : SpeedUnboundedAtOne velocity
  /-- Each presingular slice of `U` is square integrable, so the `L²` norm
  below is the honest Lebesgue norm.  Implicit in `sup_{0≤t<1} ‖u(t)‖_{L²}`,
  Theorem 1.1, `paper/sections/01-introduction.tex:27`, and in `M` of
  Lemma 2.2, `paper/sections/02-preliminaries.tex:130`. -/
  square_integrable : ∀ t ∈ Ico (0 : ℝ) 1, SquareIntegrableAtTime velocity t
  /-- `M := sup_{0≤t<1} ‖U(t)‖₂ < ∞`: the real number `energyBound` is the least
  upper bound of the presingular `L²` norms, which in particular is the finite
  supremum asserted by `eq:packetblowup`.  Lemma 2.2,
  `paper/sections/02-preliminaries.tex:130`; Theorem 1.1,
  `paper/sections/01-introduction.tex:27`. -/
  energy_isLUB :
    IsLUB ((fun t : ℝ => Real.sqrt (l2Sq velocity t)) '' Ico (0 : ℝ) 1) energyBound
  /-- The dissipation rate `t ↦ ‖∇U(t)‖₂²` is time integrable on the whole open
  presingular interval; this is the monotone-convergence step of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:150`. -/
  dissipation_integrable : IntegrableOn (dissipation velocity) (Ioo (0 : ℝ) 1)
  /-- `D := ‖∇U‖_{L²((0,1)×ℝ³)}`, i.e. `D² = ∫₀¹ ‖∇U(t)‖₂² dt`.  Lemma 2.2,
  `paper/sections/02-preliminaries.tex:131`. -/
  dissipation_eq :
    dissipationBound = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation velocity t)
  /-- The initial quiet interval is nondegenerate: `τ > 0`.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  quiet_pos : 0 < quietTime
  /-- The quiet interval is a proper initial part of `[0,1)`.  Implicit in
  "vanish on an initial time interval", `paper/sections/02-preliminaries.tex:133`,
  and forced by `speed_unbounded`. -/
  quiet_lt_one : quietTime < 1
  /-- `F = 0` on the initial interval, because its temporal support is a compact
  subset of `(0,∞)`.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  force_quiet : ∀ t ∈ Ioo (0 : ℝ) quietTime, ∀ x : Space, force (t, x) = 0
  /-- `U = 0` on the initial interval, from the energy estimate `eq:packetenergy`.
  Proof of Lemma 2.2, `paper/sections/02-preliminaries.tex:152`. -/
  velocity_quiet : ∀ t ∈ Ioo (0 : ℝ) quietTime, ∀ x : Space, velocity (t, x) = 0
  /-- `P = 0` on the initial interval: the equation gives `∇P = 0` there and
  compact spatial support fixes the constant.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  pressure_quiet : ∀ t ∈ Ioo (0 : ℝ) quietTime, ∀ x : Space, pressure (t, x) = 0
  /-- `F` vanishes at every nonpositive time, so `force` really is the zero
  extension of the manuscript's `C_c^∞(ℝ³×(0,∞))` force.  Clarification `C1`,
  `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`; inserted text at
  `paper/sections/03-torus.tex:108-109`. -/
  force_zero_nonpos : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, force (t, x) = 0
  /-- The zero extension of `U` to nonpositive time is smooth on `(-∞,1) × ℝ³`.
  Lemma 2.2, `paper/sections/02-preliminaries.tex:133`; used at
  `paper/sections/03-torus.tex:108-111` and
  `paper/sections/03-torus.tex:141` ("the temporal extension is smooth by
  initial vanishing"). -/
  velocity_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField velocity) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  /-- The zero extension of `P` to nonpositive time is smooth on `(-∞,1) × ℝ³`.
  Lemma 2.2, `paper/sections/02-preliminaries.tex:133`. -/
  pressure_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField pressure) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  /-- The zero-extended triple still solves the momentum equation at every time
  below the singular time, including the whole inactive past.  This is what
  `prop:scaling` uses when it asserts that the rescaled fields "solve the
  periodic momentum equation at viscosity `ν`",
  `paper/sections/03-torus.tex:123, 141`, and what `thm:Rinsert` uses for
  `t ≤ T - 2ε²`, `paper/sections/04-whole-space.tex:36`. -/
  extension_navier_stokes : ∀ t : ℝ, t < 1 → ∀ x : Space,
    navierStokesResidual ν (zeroPastField velocity) (zeroPastField pressure) t x
      = zeroPastField force (t, x)
  /-- Incompressibility of the zero-extended velocity at every time below the
  singular time.  `prop:scaling`, "incompressibility is preserved",
  `paper/sections/03-torus.tex:141`. -/
  extension_divergence_free : ∀ t : ℝ, t < 1 → ∀ x : Space,
    spatialDivergence (zeroPastField velocity) t x = 0

/-- The existential form of Theorem 1.1 as Section 4 uses it: a packet with all
the Lemma 2.2 data at every positive viscosity.  Introducing this proposition
asserts nothing. -/
def packetStatement : Prop := ∀ ν : ℝ, 0 < ν → Nonempty (PacketAPI ν)

/-- Section 4 does not merely use existence: it "fixes one solution from
Theorem 1.1 and denotes its velocity, pressure, and force by `(U,P,F)`"
(`paper/sections/01-introduction.tex:63-66`) and then rescales that one packet.
`PacketFamily` is that choice, made uniformly in the viscosity. -/
structure PacketFamily where
  /-- The chosen packet at each positive viscosity. -/
  select : ∀ ν : ℝ, 0 < ν → PacketAPI ν

/-- Fixing a family fixes, for each `ν`, the manuscript's `U`. -/
def PacketFamily.velocity (𝔉 : PacketFamily) {ν : ℝ} (hν : 0 < ν) : VelocityField :=
  (𝔉.select ν hν).velocity

/-- Fixing a family fixes, for each `ν`, the manuscript's `P`. -/
def PacketFamily.pressure (𝔉 : PacketFamily) {ν : ℝ} (hν : 0 < ν) : PressureField :=
  (𝔉.select ν hν).pressure

/-- Fixing a family fixes, for each `ν`, the manuscript's `F`. -/
def PacketFamily.force (𝔉 : PacketFamily) {ν : ℝ} (hν : 0 < ν) : VelocityField :=
  (𝔉.select ν hν).force

/-- The constant `M` of Lemma 2.2 for the chosen packet. -/
def PacketFamily.energyBound (𝔉 : PacketFamily) {ν : ℝ} (hν : 0 < ν) : ℝ :=
  (𝔉.select ν hν).energyBound

/-- The constant `D` of Lemma 2.2 for the chosen packet. -/
def PacketFamily.dissipationBound (𝔉 : PacketFamily) {ν : ℝ} (hν : 0 < ν) : ℝ :=
  (𝔉.select ν hν).dissipationBound

end BlowupDensity.I01.Draft
