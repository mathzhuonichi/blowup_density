import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Support

/-! Stable specification for the compact forced packet used by Section 4.

Task `collaboration/tasks/I01.md`, graph node `I01`.  Version 1 fixes, for one
positive viscosity, exactly the obligations of

* the restated OpenAI theorem, Theorem 1.1 (`thm:packet`),
  `paper/sections/01-introduction.tex:15-34`,
* Lemma 2.2, "Energy, dissipation and initial vanishing" (`lem:packetenergy`),
  `paper/sections/02-preliminaries.tex:127-153`, and
* the zero-extension convention for the force at nonpositive source time,
  `paper/sections/03-torus.tex:108-109` (clarification `C1` of
  `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`),

in the form consumed by Proposition 3.3 (`prop:scaling`,
`paper/sections/03-torus.tex:122-159`) and Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-43`).  It does not assert the insertion theorem, any density
statement, or the "Consequently ..." nonexistence clause of Theorem 1.1.

Inhabiting `PacketAPI ν` is a real obligation: no field is a placeholder and
none is an abstract proposition variable.  Introducing `packetStatement` or
`PacketFamily` asserts nothing.

Self-containedness.  A registered specification may depend only on Mathlib, so
every Navier-Stokes notion below is written out here rather than imported from
`NavierStokes.*` or `NSFormalization.*`.  Each definition is definitionally
equal to the pinned upstream one, and the adapter checks every one of them with
a `rfl` bridge, except the three reducible type abbreviations `SpaceTime`,
`VelocityField` and `PressureField`, whose defeq is already forced by the
bridges that mention them.  Most of the definitions are additionally written
character-for-character as upstream; the exception is `dissipation`, which
inlines the upstream
`NavierStokes.PeriodicIntegration.spatialPartial i (fun y => u (t, y)) x`
(`vendor/NavierStokesAndEuler/NavierStokes/PeriodicIntegration.lean:43-45`) as
`fderiv ℝ (fun y : Space => u (t, y)) x (coordinateVector i)`, which is exactly
how that definition unfolds.

Cross references: `Space`, `SpaceTime`, `VelocityField`,
`PressureField`, `coordinateVector`, `preSingularDomain`, `temporalDerivative`,
`spatialDerivative`, `advection`, `spatialDivergence`, `pressureGradient`,
`spatialLaplacian`, `SpeedUnboundedAtOne` are
`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:30-96`;
`positiveTimeDomain`, `navierStokesResidual`, `CompactPositiveTimeSupport`,
`SquareIntegrableAtTime` are
`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:53-72`;
`l2Sq` and `dissipation` are
`vendor/NavierStokesAndEuler/NavierStokes/R3/CompactEnergy.lean:190,195-196`;
`zeroPastField` is
`formalization/NSFormalization/Source/PacketScaling.lean:243-244`.

Conventions.  Time is the first spacetime coordinate.  Velocity and pressure
are smooth relative to the half-domain `[0,1) x R^3`, so no arbitrary negative
time extension is differentiated at `t = 0`.  Spatial supports are topological
supports, the paper's `supp`.  The force is modelled by its globally smooth
zero extension, whose compact spacetime support lies in `{t > 0}`; this is
`C_c^∞(R^3 x (0,∞); R^3)` together with the extension convention `C1`.  The
`∞` of the `ContDiff` scope is "all finite orders", not analyticity.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory
open scoped ContDiff

/-- Three-dimensional real Euclidean space with its Euclidean norm. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Spacetime, with time as the first coordinate. -/
abbrev SpaceTime := ℝ × Space

/-- A vector field on spacetime. -/
abbrev VelocityField := SpaceTime → Space

/-- A scalar field on spacetime. -/
abbrev PressureField := SpaceTime → ℝ

/-- The standard unit coordinate vectors of `R^3`. -/
def coordinateVector (i : Fin 3) : Space := EuclideanSpace.single i 1

/-- `[0,1) x R^3`, the physical domain before the singular time, with the
initial time included.  Time is the first factor, as in the term below. -/
def preSingularDomain : Set SpaceTime := Ico 0 1 ×ˢ univ

/-- `(0,∞) x R^3`, time first as in the term below: the open set in which the
force must have compact support. -/
def positiveTimeDomain : Set SpaceTime := Ioi 0 ×ˢ univ

/-- `∂_t u`, evaluated on the positive unit time direction. -/
def temporalDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s : ℝ => u (s, x)) t 1

/-- The spatial Frechet derivative with time held fixed. -/
def spatialDerivative (u : VelocityField) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (fun y : Space => u (t, y)) x

/-- `(u · ∇)u`. -/
def advection (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative u t x (u (t, x))

/-- `∇ · u = ∑ᵢ ∂ᵢuᵢ`. -/
def spatialDivergence (u : VelocityField) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, (spatialDerivative u t x (coordinateVector i)) i

/-- `∇p = ∑ᵢ (∂ᵢp)eᵢ`. -/
def pressureGradient (p : PressureField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    (fderiv ℝ (fun y : Space => p (t, y)) x (coordinateVector i)) • coordinateVector i

/-- `Δu = ∑ᵢ ∂ᵢ∂ᵢu`, componentwise. -/
def spatialLaplacian (u : VelocityField) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y : Space => spatialDerivative u t y (coordinateVector i))
      x (coordinateVector i)

/-- `∂_t u + (u·∇)u - νΔu + ∇p`, with the viscosity on the spatial Laplacian
only, exactly as in `eq:NS`, `paper/sections/01-introduction.tex:4-7`. -/
def navierStokesResidual (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x : Space) : Space :=
  temporalDerivative u t x + advection u t x - ν • spatialLaplacian u t x +
    pressureGradient p t x

/-- Compact spacetime support contained in strictly positive time, using the
closure of the nonvanishing set. -/
def CompactPositiveTimeSupport (f : VelocityField) : Prop :=
  HasCompactSupport f ∧ tsupport f ⊆ positiveTimeDomain

/-- Spatial square integrability at one time, with respect to Lebesgue volume
on `R^3`.  Stated explicitly because the Bochner integral is totalized. -/
def SquareIntegrableAtTime (u : VelocityField) (t : ℝ) : Prop :=
  Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) (volume : Measure Space)

/-- Pointwise unbounded speed in every left neighborhood of time one; the
faithful reading of `limsup_{t↑1}‖u(t)‖_∞ = ∞` for continuous compactly
supported slices. -/
def SpeedUnboundedAtOne (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 1 ∧ 1 - δ < t ∧ M < ‖u (t, x)‖

/-- `‖u(t)‖_{L²(R³)}²`, the full squared spatial `L²` norm. -/
def l2Sq (u : VelocityField) (t : ℝ) : ℝ := ∫ x : Space, ‖u (t, x)‖ ^ 2

/-- `‖∇u(t)‖_{L²(R³)}²`, summed over the three coordinate directions. -/
def dissipation (u : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3,
    ∫ x : Space, ‖fderiv ℝ (fun y : Space => u (t, y)) x (coordinateVector i)‖ ^ 2

/-- Extension of a spacetime field by zero to nonpositive time. -/
def zeroPastField {V : Type*} [Zero V] (f : SpaceTime → V) : SpaceTime → V :=
  fun z => if 0 < z.1 then f z else 0

/-- Every obligation the manuscript places on the chosen packet `(U, P, F)` at
one fixed viscosity `ν > 0`.

The first seven fields are data: `U, P, F, K` of Theorem 1.1, the two constants
`M, D` named in Lemma 2.2, and the quiet length `τ` produced in its proof.  The
propositional fields are grouped as Theorem 1.1 proper (`viscosity_pos` through
`speed_unbounded`), the energy and dissipation constants of Lemma 2.2
(`square_integrable` through `dissipation_eq`), the initial quiet interval
(`quiet_pos` through `pressure_quiet`), and the smooth zero extensions to
nonpositive time (`force_zero_nonpos` onwards). -/
structure PacketAPI (ν : ℝ) where
  /-- `U`, the packet velocity on `R³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`; named `(U,P,F)` at
  `paper/sections/01-introduction.tex:63-65`. -/
  velocity : VelocityField
  /-- `P`, the packet pressure on `R³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`. -/
  pressure : PressureField
  /-- `F`, the packet force, represented by its zero extension to all times.
  Theorem 1.1, `paper/sections/01-introduction.tex:16-17`; extension convention
  `paper/sections/03-torus.tex:108-109`. -/
  force : VelocityField
  /-- `K`, the single compact spatial carrier of `U(·,t)` and `P(·,t)`.
  Theorem 1.1, `paper/sections/01-introduction.tex:17-18, 24-25`. -/
  carrier : Set Space
  /-- `M`, the uniform `L²` bound of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:130`; the coefficient of `ε^{1/2}` in
  `eq:packetEscale` and `eq:REclose`. -/
  energyBound : ℝ
  /-- `D`, the total dissipation of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:131`; the coefficient of `ε^{1/2}` in
  `eq:packetEscale` and `eq:REclose`. -/
  dissipationBound : ℝ
  /-- `τ`, the length of the initial interval on which `F`, and hence `U` and
  `P`, vanish.  Proof of Lemma 2.2, `paper/sections/02-preliminaries.tex:152`. -/
  quietTime : ℝ
  /-- "For every `ν > 0`", Theorem 1.1,
  `paper/sections/01-introduction.tex:16`. -/
  viscosity_pos : 0 < ν
  /-- `U` is smooth on `R³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`. -/
  velocity_smooth : ContDiffOn ℝ ∞ velocity preSingularDomain
  /-- `P` is smooth on `R³ × [0,1)`.  Theorem 1.1,
  `paper/sections/01-introduction.tex:18-19`. -/
  pressure_smooth : ContDiffOn ℝ ∞ pressure preSingularDomain
  /-- `F` is smooth on all of spacetime, i.e. its zero extension past `t = 0`
  is smooth.  Theorem 1.1, `paper/sections/01-introduction.tex:17`, with the
  extension convention of `paper/sections/03-torus.tex:108-109`. -/
  force_smooth : ContDiff ℝ ∞ force
  /-- `F ∈ C_c^∞(R³ × (0,∞); R³)`: compact spacetime support contained in
  strictly positive time.  Theorem 1.1,
  `paper/sections/01-introduction.tex:16-17`, read as spelled out at
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
  /-- `∇ · u = 0` on `R³ × [0,1)`.  Theorem 1.1, `eq:packet`,
  `paper/sections/01-introduction.tex:22`. -/
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence velocity t x = 0
  /-- `∂_t u + (u·∇)u - νΔu + ∇p = f` at every interior time.  Theorem 1.1,
  `eq:packet`, `paper/sections/01-introduction.tex:20-23`.  The viscosity
  multiplies only the spatial Laplacian. -/
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    navierStokesResidual ν velocity pressure t x = force (t, x)
  /-- `limsup_{t↑1} ‖u(t)‖_∞ = ∞`, in the pointwise form the source and both
  consumers use.  Theorem 1.1, `eq:packetblowup`,
  `paper/sections/01-introduction.tex:28`; consumed as "unbounded speed at `T`",
  `paper/sections/03-torus.tex:123`. -/
  speed_unbounded : SpeedUnboundedAtOne velocity
  /-- Each presingular slice of `U` is square integrable, so the `L²` norm
  below is the honest Lebesgue norm.  Implicit in `sup_{0≤t<1}‖u(t)‖_{L²}`,
  `paper/sections/01-introduction.tex:27`, and in `M`,
  `paper/sections/02-preliminaries.tex:130`. -/
  square_integrable : ∀ t ∈ Ico (0 : ℝ) 1, SquareIntegrableAtTime velocity t
  /-- `M := sup_{0≤t<1}‖U(t)‖₂`: `energyBound` is the least upper bound of the
  presingular `L²` norms, which in particular is the finite supremum asserted
  by `eq:packetblowup`.  Lemma 2.2,
  `paper/sections/02-preliminaries.tex:130`; Theorem 1.1,
  `paper/sections/01-introduction.tex:27`.  A least upper bound, not merely an
  upper bound, because `eq:packetEscale` asserts the equality
  `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M`, `paper/sections/03-torus.tex:125-126`. -/
  energy_isLUB :
    IsLUB ((fun t : ℝ => Real.sqrt (l2Sq velocity t)) '' Ico (0 : ℝ) 1) energyBound
  /-- The dissipation rate `t ↦ ‖∇U(t)‖₂²` is time integrable on the whole open
  presingular interval; the monotone-convergence step of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:150`. -/
  dissipation_integrable : IntegrableOn (dissipation velocity) (Ioo (0 : ℝ) 1)
  /-- `D := ‖∇U‖_{L²((0,1)×R³)}`, i.e. `D² = ∫₀¹‖∇U(t)‖₂² dt`.  Lemma 2.2,
  `paper/sections/02-preliminaries.tex:131`.  Spatial integrability of the
  gradient, the analogue of `square_integrable` inside `dissipation`, is not a
  separate field: it follows from `velocity_smooth` together with the compact
  carrier `velocity_support`. -/
  dissipation_eq :
    dissipationBound = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, dissipation velocity t)
  /-- The initial quiet interval is nondegenerate: `τ > 0`.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  quiet_pos : 0 < quietTime
  /-- The quiet interval is a proper initial part of `[0,1)`.  Implicit in
  "vanish on an initial time interval",
  `paper/sections/02-preliminaries.tex:133`, and forced by `speed_unbounded`. -/
  quiet_lt_one : quietTime < 1
  /-- `F = 0` on the closed initial interval `[0,τ]`, because its temporal
  support is a compact subset of `(0,∞)`.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  force_quiet : ∀ t ∈ Icc (0 : ℝ) quietTime, ∀ x : Space, force (t, x) = 0
  /-- `U = 0` on `[0,τ]`, from the energy estimate `eq:packetenergy`.  Proof of
  Lemma 2.2, `paper/sections/02-preliminaries.tex:152`. -/
  velocity_quiet : ∀ t ∈ Icc (0 : ℝ) quietTime, ∀ x : Space, velocity (t, x) = 0
  /-- `P = 0` on `[0,τ]`: the equation gives `∇P = 0` there and compact spatial
  support fixes the constant.  Proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`. -/
  pressure_quiet : ∀ t ∈ Icc (0 : ℝ) quietTime, ∀ x : Space, pressure (t, x) = 0
  /-- `F` vanishes at every nonpositive time, so `force` really is the zero
  extension of the manuscript's `C_c^∞(R³×(0,∞))` force.  Inserted text at
  `paper/sections/03-torus.tex:108-109`. -/
  force_zero_nonpos : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, force (t, x) = 0
  /-- The zero extension of `U` to nonpositive time is smooth on `(-∞,1) × R³`.
  Lemma 2.2, `paper/sections/02-preliminaries.tex:133`; used at
  `paper/sections/03-torus.tex:109-111` and at
  `paper/sections/03-torus.tex:141` ("the temporal extension is smooth by
  initial vanishing"). -/
  velocity_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField velocity) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  /-- The zero extension of `P` to nonpositive time is smooth on `(-∞,1) × R³`.
  Lemma 2.2, `paper/sections/02-preliminaries.tex:133`. -/
  pressure_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField pressure) (Iio (1 : ℝ) ×ˢ (univ : Set Space))
  /-- The zero-extended triple still solves the momentum equation at every time
  below the singular time, including the whole inactive past.  This is what
  `prop:scaling` uses when the rescaled fields "solve the periodic momentum
  equation at viscosity `ν`", `paper/sections/03-torus.tex:123, 141`, and what
  `thm:Rinsert` uses for `t ≤ T - 2ε²`,
  `paper/sections/04-whole-space.tex:36`. -/
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

/-- Section 4 does not merely use existence: it "fix[es] one solution from
Theorem 1.1 and denote[s] its velocity, pressure, and force by `(U,P,F)`"
(`paper/sections/01-introduction.tex:63-65`) and then rescales that one packet.
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

end BlowupDensity.Contracts.V1
