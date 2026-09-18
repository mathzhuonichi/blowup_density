import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.Packet
import Contracts.V1.InsertionFamily
import Contracts.V2.InsertionLifespan
import Contracts.V1.HomogeneousNorm
import Contracts.V1.GradientL6

/-!
# T18 double-blind draft A: exact local insertion on the torus

The declarations copied below are the unregistered T13--T17 vocabulary used
by the insertion proof.  Each copied block is delimited and retains its
source-line provenance.  The registered T10/T11 contracts are imported above.
-/

noncomputable section

open BlowupDensity.Contracts.V1.TorusLocalTheory

/- Compatibility namespace retained because the verbatim upstream blocks open
   it; all T10 declarations themselves come from the registered contracts. -/
namespace BlowupDensity.T10.Draft
end BlowupDensity.T10.Draft

/- copied verbatim from research/T13/Spec.lean:168-205,213-312;
   dependencies now resolve through registered Contracts.V1.TorusData -/
namespace BlowupDensity.T13.Spec

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:23,53,79-80`: the fixed closed unit fundamental cube
`[0,1]³`.  Its interior is the coordinate chart in which the support ball must
lie.  This is the fixed cube underlying T10's `(0,1]³` torus representative. -/
def fundamentalCube : Set Space :=
  {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

/-- `03-torus.tex:23`: the zero extension is supported in the open coordinate
ball with center `c` and radius `r`, in the topological-support sense. -/
def SupportedInBall (c : Space) (r : ℝ) (f : SpatialField) : Prop :=
  tsupport f ⊆ Metric.ball c r

/-- `03-torus.tex:53-56`: embed a lattice frequency as its Euclidean vector. -/
def latticeVector (n : PeriodicFrequency) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i ↦ (n i : ℝ))

/-- `03-torus.tex:23`: the actual spatial lattice periodization of the
whole-space zero extension; it is a function, not an existential relation. -/
def periodize (f : SpatialField) : SpatialField :=
  fun x ↦ ∑' n : PeriodicFrequency, f (x - latticeVector n)

/-! ## Fractional kernels and difference integrals -/

/-- `03-torus.tex:35,43-48,54-56`: the extended nonnegative singular power
`|h|^{-3-2s}`.  The singular value at `h=0` is retained as `⊤`. -/
def fractionalRadialKernel (s : ℝ) (h : Space) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖h‖) ^ (-(3 + 2 * s))

/-- `03-torus.tex:35-39`: the paper's single explicit constant
`c_s = ∫_ℝ³ |exp(i h₁)-1|² |h|^{-3-2s} dh`, with no hidden `2π` factor. -/
def cFrac (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Space,
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h

/-- `03-torus.tex:53-57`: the periodized fractional kernel
`K_s(h)=∑_{n∈ℤ³}|h+n|^{-3-2s}` on the fixed unit lattice. -/
def periodicKernel (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : PeriodicFrequency, fractionalRadialKernel s (h + latticeVector n)

/-- `03-torus.tex:40-48`: the vector-valued whole-space Gagliardo integral
`I_ℝ`, with the Euclidean norm summing the three component squares. -/
def IReal (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ h : Space, ∫⁻ x : Space,
    ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2) * fractionalRadialKernel s h

/-- `03-torus.tex:53-67`: the vector-valued torus Gagliardo integral over the
fixed fundamental cube, using the literal representative difference `x-y`. -/
def ITorus (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
    ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y)

/-! ## Endpoint quantities -/

/-- `03-torus.tex:29,97-98`: the physical `L²` gradient norm, with the
Hilbert--Schmidt convention (sum over all three spatial derivatives). -/
def gradientENorm (f : SpatialField) (μ : Measure Space) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2) ∂μ) ^
    ((2 : ℝ)⁻¹)

/-! ## Reconciled six-field API -/

/-- Statement-only API for `lem:localization` and the Fourier/Gagliardo
identifications used by its proof (`03-torus.tex:22-98`).  The range is always
`0 < s < 1`; the two endpoints are stated separately. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:35-39`: the defined constant `c_s` is strictly positive
  and finite for `0 < s < 1`.

  Non-vacuity: this constrains the concrete integral `cFrac s`, rather than
  allowing an arbitrary positive constant to be chosen. -/
  constant_pos_finite :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤

  /-- `03-torus.tex:40-51`: the whole-space Gagliardo integral of every smooth
  compactly supported real vector field equals `c_s` times the square of the
  registered `dotHomogeneousENorm`.

  Non-vacuity: compact smooth fields exist (in particular the zero field), and
  the conclusion both proves finiteness and fixes the exact norm value. -/
  wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)

  /-- `03-torus.tex:53-72`: the periodic Gagliardo integral of every smooth
  periodic vector field equals the same `c_s` times T10's homogeneous norm of
  its explicitly mean-zero part; the T10 weight retains the exact `2π` factor.

  Non-vacuity: the zero field is smooth and periodic, while the identity also
  applies to nonconstant trigonometric modes and asserts a finite integral. -/
  torus_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ)

  /-- `03-torus.tex:22-28,73-96`, equation `eq:localization`: for every fixed
  positive-radius ball strictly inside the fixed cube, one positive finite real
  constant is chosen before every smooth zero extension supported in that ball.
  The torus and whole-space terms use T10's `periodicSobolevENorm`, the
  registered `eLpNorm f 2 volume`, and the registered homogeneous norm.

  Non-vacuity: positive-radius balls with closure inside `(0,1)³` exist, and
  the quantifier order makes one `C_{s,B}` control every smaller support. -/
  localization :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)

  /-- `03-torus.tex:29,96-98`: at `s=0`, integration over the single copy of
  the support gives equality of the physical `L²` norms.

  Non-vacuity: the equality compares the concrete periodization on the fixed
  cube with the whole-space field, under the same nonempty ball condition as
  the fractional statement. -/
  endpoint_zero :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume

  /-- `03-torus.tex:29,96-98`: at `s=1`, integration over the single copy of
  the support gives equality of the corresponding physical `L²` gradient
  norms, without identifying them with the full inhomogeneous `H¹` norm.

  Non-vacuity: this is an equality of explicit Hilbert--Schmidt gradient norms
  for every supported smooth field, not a restatement of `endpoint_zero`. -/
  endpoint_one :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume

end BlowupDensity.T13.Spec
namespace BlowupDensity.T14.Draft

open Set MeasureTheory
open BlowupDensity.Contracts.V1

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

end BlowupDensity.T14.Draft
/- end verbatim T14 copy -/

namespace BlowupDensity.T15.Draft

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open BlowupDensity.T14.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Definitional drift checks -/

/-- `Contracts/V1/Data.lean:743-744`: the registered inhomogeneous
abbreviation is definitionally `CompletedDenseVia` with `IsSobolevPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- `Contracts/V1/Data.lean:752-753`: the registered homogeneous
abbreviation is definitionally `CompletedDenseVia` with
`IsHomogeneousPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-! ## Explicit scaling and lattice periodization -/

/-- `03-torus.tex:106`: the shifted packet start time `t_ε=T-ε²`. -/
def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

/-- `03-torus.tex:112-118`: the time-first source point
`((t-t_ε)/ε²,(x-x₀)/ε)`, written with the same inverse-scale tokens as
`Contracts.V1.dilateField`. -/
def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:108-114`: the velocity formula of `eq:scaling`, using
the packet's smooth negative-time zero extension. -/
def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.velocity (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-116`: the pressure formula of `eq:scaling`, using
the packet's smooth negative-time zero extension. -/
def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 *
    zeroPastField P.pressure (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-109,117-118`: the force formula of `eq:scaling`;
the packet force is already its globally smooth zero extension. -/
def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.force (scaledSourcePoint x₀ T ε z)

/-- The local velocity rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:112-114`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledVelocity P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPacket P.velocity x₀ T ε := rfl

/-- The local pressure rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:115-116`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledPressure P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPressure P.pressure x₀ T ε := rfl

/-- The local force rescaling is definitionally the registered
`I03.scaling` rescaling, `03-torus.tex:117-118`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    scaledForce P x₀ T ε =
      BlowupDensity.Contracts.V1.scaledForce P.force x₀ T ε := rfl

/-- `03-torus.tex:120`: the spatial lattice sum of the scaled velocity. -/
def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledVelocity P x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:120`: the spatial lattice sum of the raw scaled pressure. -/
def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure P x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: the spatial lattice sum of the scaled force. -/
def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledForce P x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:123`: subtract the normalized Haar mean from every raw
pressure slice.  The subtracted value is spatially constant by definition. -/
def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

/-- The pressure-adjustment formula dropped as a structure field is
definitionally true, `03-torus.tex:123`. -/
example {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε t : ℝ) (x : Space) :
    normalizedScaledPressure P x₀ T ε (t, x) =
      periodizedScaledPressure P x₀ T ε (t, x) -
        pressureMeanT (periodizedScaledPressure P x₀ T ε) t := rfl

/-! ## Honest mixed, Sobolev, and energy carriers -/

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `03-torus.tex:129-133`: an honest whole-space mixed Bochner path;
`MemLp` supplies both strong measurability and finiteness. -/
def MemMixedLebesgueR (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p (volume : Measure Space),
    IsLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:129-133`: an honest torus mixed Bochner path; this guard
prevents the mixed identity from degenerating to `⊤=⊤`. -/
def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:133-138`: an honest periodic Sobolev Bochner path; the
registered `IsPeriodicDatum` includes Haar integrability. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:125-128`: honest Haar-`L²` velocity and full-gradient
slices for both packet-energy identities. -/
def EnergySlicesMemLpT (T : ℝ) (u : SpaceTimeField) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ u (t, x))) 2 periodicTorusMeasure) ∧
    ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ spatialGradient u t x)) 2 periodicTorusMeasure

/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`, with
`ENNReal.toReal ⊤=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-- The torus exponent is definitionally the registered `I03.scaling`
exponent, `03-torus.tex:130-131`. -/
example (p q : ℝ≥0∞) :
    alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-! ## Placement data fixed before every scale -/

/-- The choices and smallness conditions made at `03-torus.tex:101-107`.
`Kstar` contains both spatial packet supports.  Its scaled translate lies in a
fixed coordinate ball whose closure is inside the fundamental cube; this is
the hypothesis that makes the lattice sum a single copy on that cube. -/
structure PlacementData {ν : ℝ} (P : PacketAPI ν) where
  /-- `03-torus.tex:103-106`: the target singular time `T`.

  Non-vacuity: positivity makes `(0,T)` a genuine evolution interval. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`.

  Non-vacuity: this rules out the empty or reversed time interval. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`.

  Non-vacuity: it is used in the concrete ball containment below. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`.

  Non-vacuity: the next field requires this radius to be positive. -/
  chartRadius : ℝ
  /-- `03-torus.tex:22-23,102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:22-23,102-105`: the closure of `B` is contained in the
  coordinate chart, here the interior of the fixed fundamental cube.

  Non-vacuity: this is the separation from other lattice translates used by
  the single-copy clauses. -/
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`.

  Non-vacuity: the point is tied to the same concrete chart ball. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`.

  Non-vacuity: this is membership in the explicit ball above. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`.

  Non-vacuity: the following three fields constrain this actual set. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact.

  Non-vacuity: this is an assertion about the carried set, not an existential
  choice made separately for each scale. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is T14's packet carrier.

  Exact quantifier order: every point of `P.carrier` lies in the fixed
  `Kstar`.  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : P.carrier ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales.

  Non-vacuity: every conclusion below uses the same interval `(0,ε₀]`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`.

  Non-vacuity: `(0,ε₀]` contains admissible scales. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`.

  Non-vacuity: this is a quantitative restriction on the one threshold. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined.

  Exact quantifier order: first `ε∈(0,ε₀]`, then the inequality.
  Non-vacuity: it gives `t_ε>0`, so positive-time force norms contain the
  complete rescaled temporal support. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`.

  Exact quantifier order: first `ε∈(0,ε₀]`, then every `y∈Kstar`.
  Non-vacuity: together with `chartBall_in_cube`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-! ## Proposition 3.3 -/

/-- The reconciled statement of scaling at fixed viscosity,
`paper/sections/03-torus.tex:101-159`, for one energy-enhanced packet and the
shared placement data that T17 and T18 will consume.

The record is Type-valued because `sobolevConst` is selected as data before
every scale.  Every totalized lattice sum, Haar integral, and Bochner norm used
by an identity below has its corresponding explicit honesty guard. -/
structure ScalingAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.toPacketAPI) where
  /-- `03-torus.tex:22-98,150-158`: the T13 localization witness used to
  transfer the whole-space packet estimates to the single torus copy.

  Exact quantifier order: this witness is structure data, fixed after `P` and
  `place` and before every scale.
  Non-vacuity: this is T13's concrete six-field API, whose localization and
  endpoint fields constrain explicit norms and periodization. -/
  localization : LocalizationAPI

  /-- `03-torus.tex:120`: at every admissible scale, presingular time, and
  spatial point, the velocity lattice family is summable.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, `∀ t<T`, then `∀ x`.
  Non-vacuity: this guard prevents the totalized `tsum` in
  `periodizedScaledVelocity` from taking its nonsummable junk value. -/
  velocity_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledVelocity P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: at every admissible scale, presingular time, and
  spatial point, the raw pressure lattice family is summable.

  Exact quantifier order matches `velocity_summable`.
  Non-vacuity: this guard makes the raw pressure `tsum`, and hence the mean
  later taken from it, an honest lattice sum. -/
  pressure_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledPressure P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:108-120`: at every admissible scale and every spacetime
  point, the globally defined force lattice family is summable.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, `∀ t`, then `∀ x`.
  Non-vacuity: this guard prevents a nonsummable force family from being
  totalized to the junk value used by `tsum`. -/
  force_summable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledForce P place.x₀ place.T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the velocity
  periodization is its single zero-lattice copy.

  Exact quantifier order: `ε`, admissibility, `t<T`, then `x∈Q`.
  Non-vacuity: this is equality of the explicit lattice sum and rescaling, with
  `velocity_summable` making the sum honest. -/
  velocity_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledVelocity P place.x₀ place.T ε (t, x) =
        scaledVelocity P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the raw pressure
  periodization is its single zero-lattice copy.

  Exact quantifier order matches `velocity_singleCopy`.
  Non-vacuity: this is a concrete equality before mean normalization, with
  `pressure_summable` validating the lattice sum. -/
  pressure_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledPressure P place.x₀ place.T ε (t, x) =
        scaledPressure P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed fundamental cube, the force
  periodization is its single zero-lattice copy at every real time.

  Exact quantifier order: `ε`, admissibility, `t`, then `x∈Q`.
  Non-vacuity: this is the concrete equality transferring the whole-space
  force norms to the torus, and `force_summable` makes its sum honest. -/
  force_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x ∈ fundamentalCube,
      periodizedScaledForce P place.x₀ place.T ε (t, x) =
        scaledForce P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:108-123` and `02-preliminaries.tex:10,23-26`: each
  periodized rescaled force is smooth, unit-periodic, and compactly supported
  in positive time, i.e. it belongs to `F_T`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: `MemForceT` expands to concrete smoothness, periodicity, and a
  compact positive-time support witness for this explicit force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    MemForceT (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:122-123,141` and `02-preliminaries.tex:28-36,75-115`:
  at every admissible scale, the explicit periodized fields form a periodic
  classical solution at the unchanged viscosity `ν`, with zero initial datum
  and the mean-zero pressure representative.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, then one
  `ClassicalSolutionT ν 0 F_ε place.T`, followed by both field-pinning
  equations.
  Non-vacuity: the two equations forbid substitution of unrelated solution
  fields; `ClassicalSolutionT` concretely includes regularity, divergence,
  momentum, Sobolev paths, pressure-gradient membership, periodicity, initial
  data, and the pressure gauge. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∃ S : ClassicalSolutionT ν (0 : SpatialField)
        (periodizedScaledForce P place.x₀ place.T ε) place.T,
      S.velocity = periodizedScaledVelocity P place.x₀ place.T ε ∧
        S.pressure = normalizedScaledPressure P place.x₀ place.T ε

  /-- `03-torus.tex:123` and `02-preliminaries.tex:28,84-88`: every raw
  periodized pressure slice on `[0,T)` is Haar-integrable.

  Exact quantifier order: `ε`, admissibility, then `t∈[0,T)`.
  Non-vacuity: this is the guard that makes the Bochner integral in
  `pressureMeanT`, hence the pressure normalization and gauge carried by
  `solution`, honest rather than the nonintegrable junk value. -/
  pressureSlice_integrable : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      Integrable
        (torusLift
          (fun x ↦ periodizedScaledPressure P place.x₀ place.T ε (t, x)))
        periodicTorusMeasure

  /-- `03-torus.tex:123,142-143`: the explicit periodized velocity has
  unbounded speed in every left neighborhood of `place.T`.

  Exact quantifier order: scale first, then `SpeedUnboundedAt`'s
  `M>0`, `δ>0`, and witnesses `t,x`.
  Non-vacuity: this constrains the actual periodized velocity and approaches
  the prescribed terminal time, rather than asserting unboundedness somewhere
  on an unrelated interval. -/
  unboundedSpeed : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    SpeedUnboundedAt place.T
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:125-128`: every velocity and full-gradient slice in the
  two packet-energy identities is an honest Haar-`L²(T³)` function.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`, with the slice-time
  quantifiers inside `EnergySlicesMemLpT`.
  Non-vacuity: this is the `MemLp` guard for both `energyEssSupT` and
  `energyGradientT`; it supplies the strong measurability/integrability that
  a finite-looking totalized expression alone would not provide. -/
  energySlices_memLp : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    EnergySlicesMemLpT place.T
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:125-126,145`, the first identity of
  `eq:packetEscale`: `‖U_ε‖_{L∞_tL²_x}=ε^{1/2}M`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this is an equality in `ℝ≥0∞` with
  `M=P.energyBound`; `energySlices_memLp` is the guard making its spatial
  Bochner norms honest. -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T
        (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound)

  /-- `03-torus.tex:127-128,145-146`, the second identity of
  `eq:packetEscale`: `‖∇U_ε‖_{L²_tL²_x}=ε^{1/2}D`.

  Exact quantifier order: `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this independent equality uses `D=P.dissipationBound`;
  `energySlices_memLp` is the guard that makes every gradient slice honest. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyGradientT place.T
        (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound)

  /-- `03-torus.tex:129-133,148-149`: both sides of every mixed-norm
  identity have honest Bochner `MemLp` representatives, including the
  essential-supremum endpoints.

  Exact quantifier order: `∀ p q`, the `Fact (1≤p)` instance, `1≤q`,
  the source witness, then every admissible scale's torus witness.
  Non-vacuity: this is the guard that prevents `packetMixedScaling` from
  degenerating to the totalized equality `⊤=⊤`. -/
  mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    MemMixedLebesgueR q p P.force ∧
      ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
        MemMixedLebesgueT q p
          (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:129-133,148-149`, equation `eq:packetFscale`:
  `‖F_ε‖_{L^q_tL^p(T³)}=ε^{α(p,q)}‖F‖_{L^q_tL^p(R³)}` for every
  `1≤p,q≤∞`, with `α=-3+3/p+2/q`.

  Exact quantifier order: `∀ p q`, `Fact (1≤p)`, `1≤q`, then
  `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: `mixed_memLp` supplies the honest Bochner paths on both sides;
  the right side is the unrescaled source force's registered whole-space norm. -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      mixedLebesgueENormT q p
          (periodizedScaledForce P place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ alphaT p q) * mixedLebesgueENorm q p P.force

  /-- `03-torus.tex:133-136`: the family `s↦C_s`, selected as data before
  every scale.

  Exact quantifier order: the whole function is a structure field before the
  later `s` and `ε` quantifiers.
  Non-vacuity: `sobolevConst_pos` and `packetSobolevBound` constrain this
  concrete family on all of `[0,1]`. -/
  sobolevConst : ℝ → ℝ

  /-- `03-torus.tex:133-136`: `C_s>0` at every `0≤s≤1`.

  Exact quantifier order: `∀ s`, then its lower and upper range proofs.
  Non-vacuity: strict positivity excludes a junk negative constant whose
  `ENNReal.ofReal` image would collapse the displayed upper bound. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s

  /-- `03-torus.tex:133-138,150-158`: each rescaled force has an honest
  `L¹(0,∞;H^s(T³))` Fourier-data path for `0≤s≤1`.

  Exact quantifier order: `∀ s`, its two range proofs, then
  `∀ ε ∈ (0,place.ε₀]`.
  Non-vacuity: this is the guard that makes the Bochner infimum in
  `forceSobolevENormT` honest; its path uses registered `IsPeriodicDatum`,
  including the Haar-integrability conjunct. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s
        (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:133-137,150-158`, equation `eq:packetHs`:
  `‖F_ε‖_{L¹_tH^s(T³)}≤C_s(ε^{1/2}+ε^{1/2-s})` for `0≤s≤1`.

  Exact quantifier order: `∀ s`, both range proofs, then every admissible
  `ε`, so the carried `C_s` is uniform in scale.
  Non-vacuity: `forceSobolev_memLp` is the guard making the Bochner integral
  honest, and `sobolevConst_pos` makes the finite real upper bound meaningful. -/
  packetSobolevBound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s
          (periodizedScaledForce P place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)))

  /-- `03-torus.tex:129-138,148-158`: the promoted subcritical convergence
  conclusion, in the lane-required registered threshold shape:
  for `q∈{1,2}` and `s<criticalOrder(q)=2/q-3/2`, the force norm tends to
  zero as `ε↓0`.  At `q=1` this is exactly the proposition's “in
  particular” clause `03-torus.tex:138`, including every negative `s`.

  Exact quantifier order: `q : ℝ≥0∞`, its disjunction, `s`, the strict
  threshold, then the right-neighborhood limit.
  Non-vacuity: the limit concerns the same explicit force family; convergence
  to finite zero in `ℝ≥0∞` rules out an eventually-`⊤` totalized norm, while
  `forceSobolev_memLp` gives the direct Bochner guard on the displayed
  `q=1`, `0≤s≤1` range. -/
  forceConvergence : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < criticalOrder q.toReal →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT q s
          (periodizedScaledForce P place.x₀ place.T ε))
        (𝓝[>] 0) (𝓝 0)

/-! ## Existential form -/

/-- `03-torus.tex:101-159`: for the packet chosen at each positive
viscosity and for any already selected shared placement record, the scaling
package is inhabited.

The placement is a parameter, not existentially substituted inside the
result, so T17 and T18 can consume definitionally the same `T,x₀,B,K_*,ε₀`.
Introducing this definition proves no inhabitant. -/
def scalingStatement : Prop :=
  ∀ (𝔉 : PacketImportFamily) (ν : ℝ) (hν : 0 < ν)
    (place : PlacementData (𝔉.select ν hν).toPacketAPI),
      Nonempty (ScalingAPI (𝔉.select ν hν) place)

end BlowupDensity.T15.Draft

-- copied verbatim from research/T17/Spec.lean:223-519
namespace BlowupDensity.T16.Draft

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open Set MeasureTheory
open scoped ContDiff Topology

/-! ## Periodic physical-layer helpers -/

/-- The Euclidean lattice vector associated with a torus frequency;
`paper/sections/03-torus.tex:188,212`.

Non-vacuity: this is the actual integer translation in the physical
`R³` lift, not an abstract quotient label. -/
def latticeVector (k : PeriodicFrequency) : Space :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- The lift to `R³` of a spatial set on the unit torus;
`paper/sections/03-torus.tex:188,212`.

Non-vacuity: membership supplies a concrete lattice translate whose
representative lies in `S`. -/
def periodicSet (S : Set Space) : Set Space :=
  {x | ∃ k : PeriodicFrequency, x - latticeVector k ∈ S}

/-- The periodized rescaled packet used by `eq:bgzero`;
`paper/sections/03-torus.tex:112-120,214-215`.

Non-vacuity: this is the locally finite integer-translate formula consumed
later for T14's compactly supported packet, not an unspecified packet family. -/
def periodicScaledPacket (U : SpaceTimeField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z => ∑' k : PeriodicFrequency,
    scaledPacket U x₀ T ε (z.1, z.2 - latticeVector k)

/-- The corrected background `v + w_ε` in `eq:bgzero`;
`paper/sections/03-torus.tex:190-192`.

Non-vacuity: evaluation is the pointwise sum of the given reference and the
chosen correction at the specified scale. -/
def correctedBackground (v : SpaceTimeField) (w : ℝ → SpaceTimeField) (ε : ℝ) :
    SpaceTimeField :=
  fun z => v z + w ε z

/-! ## Construction data and the reconciled API -/

/-- The witnesses chosen once before the small scale `ε` is quantified;
`paper/sections/03-torus.tex:167-188,212`.

The data live in `Type`, while `LocalPotentialAPI` lives in `Prop`, so
downstream consumers can project the actual cutoffs, threshold, potential, and
correction family. -/
structure CutoffData where
  /-- Spatial cutoff from the Urysohn construction;
  `paper/sections/03-torus.tex:167-172,181`.

  Non-vacuity: this is a concrete real-valued function on physical space. -/
  θ : Space → ℝ
  /-- Temporal cutoff used in `eq:cutoff`;
  `paper/sections/03-torus.tex:173-174,182-186`.

  Non-vacuity: this is a concrete real-valued function of physical time. -/
  η : ℝ → ℝ
  /-- Open plateau on which `θ` is one;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: the set is retained as data and is constrained below to contain
  the prescribed compact set. -/
  plateau : Set Space
  /-- Fixed support radius for `θ`;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: the API requires this actual real radius to be strictly
  positive and to bound `tsupport θ`. -/
  θRadius : ℝ
  /-- Common upper threshold for every sufficiently small `ε`;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the API requires one strictly positive threshold shared by all
  scale-dependent conclusions. -/
  ε₀ : ℝ
  /-- Radial vector potential `A` from `eq:potential`;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: this is a concrete time-first spacetime vector field whose
  formula and curl are fixed below. -/
  potential : SpaceTimeField
  /-- Scale-indexed correction family `w_ε` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-193`.

  Non-vacuity: this is one concrete family shared by smoothness, periodicity,
  support, divergence, and cancellation fields. -/
  correction : ℝ → SpaceTimeField

/-- The reconciled clauses of Lemma `lem:potential`;
`paper/sections/03-torus.tex:167-215`.

All witnesses are stored in `D` before `ε` is quantified.  The local curl
formula is stated in the selected Euclidean chart; the global correction is a
unit-periodic physical lift and therefore has translated rather than compact
support in all of `R³`. -/
structure LocalPotentialAPI (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData) : Prop where
  /-- The spatial Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:167-174,181`.

  Non-vacuity: this is global `C∞` regularity of the concrete function
  `D.θ`. -/
  theta_smooth : ContDiff ℝ ∞ D.θ
  /-- The spatial Urysohn cutoff has compact support;
  `paper/sections/03-torus.tex:167-174,181`.

  Non-vacuity: this constrains the topological support of `D.θ`, rather than
  merely asserting existence of some compact set. -/
  theta_compactSupport : HasCompactSupport D.θ
  /-- The spatial cutoff takes values in `[0,1]`;
  `paper/sections/03-torus.tex:171-172`.

  Non-vacuity: the closed-interval membership is required pointwise for every
  spatial input. -/
  theta_range : ∀ x, D.θ x ∈ Icc (0 : ℝ) 1
  /-- The plateau is an open neighborhood;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: openness is imposed on the actual stored set `D.plateau`. -/
  plateau_open : IsOpen D.plateau
  /-- The prescribed enlarged compact set `K_*` lies in the plateau;
  `paper/sections/03-torus.tex:101-102,168-172,181`.

  Non-vacuity: every point of the caller-supplied `K` is forced into the
  same plateau used by the cancellation field. -/
  prescribed_subset_plateau : K ⊆ D.plateau
  /-- The spatial cutoff is identically one on its plateau;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: this is a pointwise equality on the open set that contains
  `K`. -/
  theta_one : EqOn D.θ (fun _ => 1) D.plateau
  /-- The fixed cutoff-support radius is positive;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: strict positivity rules out a degenerate radius witness. -/
  theta_radius_pos : 0 < D.θRadius
  /-- The spatial cutoff support lies in the fixed reference ball;
  `paper/sections/03-torus.tex:168-172,181,212`.

  Non-vacuity: this bounds the actual `tsupport D.θ` by the radius later used
  in `eps_space`. -/
  theta_support : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius
  /-- The temporal Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:173-174,182`.

  Non-vacuity: this is global `C∞` regularity of the concrete function
  `D.η`. -/
  eta_smooth : ContDiff ℝ ∞ D.η
  /-- The temporal cutoff has compact support;
  `paper/sections/03-torus.tex:173-174,182`.

  Non-vacuity: this constrains the actual topological support of `D.η`. -/
  eta_compactSupport : HasCompactSupport D.η
  /-- The temporal cutoff takes values in `[0,1]`;
  `paper/sections/03-torus.tex:171-174`.

  Non-vacuity: the closed-interval membership is required for every time. -/
  eta_range : ∀ t, D.η t ∈ Icc (0 : ℝ) 1
  /-- The temporal cutoff equals one throughout `[-1,1]`;
  `paper/sections/03-torus.tex:182,214-215`.

  Non-vacuity: the equality is pointwise on the entire closed active
  interval. -/
  eta_one : EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- The temporal cutoff is supported strictly inside `(-2,2)`;
  `paper/sections/03-torus.tex:182,188-189`.

  Non-vacuity: this is an inclusion for the actual `tsupport D.η`, with open
  endpoints as in the manuscript. -/
  eta_support : tsupport D.η ⊆ Ioo (-2 : ℝ) 2
  /-- The common small-scale threshold is positive;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: strict positivity ensures that admissible scales exist. -/
  eps_pos : 0 < D.ε₀
  /-- Every admissible time window remains inside the positive regular slab;
  `paper/sections/03-torus.tex:103-106,188,212`.

  Non-vacuity: the strict inequality holds for each concrete
  `ε ∈ (0,D.ε₀]`. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
  /-- Every admissible scaled cutoff lies strictly inside the coordinate ball;
  `paper/sections/03-torus.tex:103-105,188,212`.

  Non-vacuity: the same threshold controls the concrete product
  `ε * D.θRadius` relative to `r`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
  /-- The radial potential is smooth on the local spacetime slab;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: regularity is asserted for the stored potential on the actual
  open time-ball product. -/
  potential_smooth : ContDiffOn ℝ ∞ D.potential
    (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r)
  /-- The radial integral formula `eq:potential`;
  `paper/sections/03-torus.tex:177-180`.

  Non-vacuity: this fixes `D.potential` pointwise to the displayed integral,
  including the center, cross product, and integration interval. -/
  potential_formula : ∀ t x, D.potential (t, x) =
    ∫ ρ in (0 : ℝ)..1,
      ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- The spatial curl of the radial potential is the reference velocity;
  `paper/sections/03-torus.tex:181,196-210`.

  Non-vacuity: this is pointwise equality of concrete vector fields throughout
  the local regularity slab. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    curl (fun y => D.potential (t, y)) x = v (t, x)
  /-- The chart formula `w_ε=-curl(η_ε θ_ε A)` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-188,212`.

  Non-vacuity: for every admissible scale, this identifies the stored
  correction pointwise on the coordinate ball with the registered cutoff and
  curl expression. -/
  correction_formula : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    ∀ x ∈ Metric.ball x₀ r,
      D.correction ε (t, x) =
        -curl (fun y =>
          (scaledTemporalCutoff D.η T ε t *
            scaledSpatialCutoff D.θ x₀ ε y) • D.potential (t, y)) x
  /-- The zero-extended, periodized correction is globally smooth;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: global `C∞` regularity is required of the same concrete
  correction family used by all later fields. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (D.correction ε)
  /-- The physical lift of the correction is unit-periodic in space;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: T10's `IsPeriodicOn` requires equality under every coordinate
  unit shift, at every real time and spatial point. -/
  correction_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (D.correction ε)
  /-- The correction is divergence free because it is a spatial curl;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the registered physical divergence vanishes pointwise for every
  time and position. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
    spatialDivergence (D.correction ε) t x = 0
  /-- The correction is supported in the prescribed temporal window;
  `paper/sections/03-torus.tex:188-189,212`.

  Non-vacuity: the inclusion forces the full spacetime support to vanish
  outside `(T-2ε²,T+2ε²)`; spatial localization is imposed separately below. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (D.correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)
  /-- Each spatial slice is supported in the periodic lift of the coordinate
  ball; `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: this rules out correction support outside all integer
  translates of the concrete ball `Metric.ball x₀ r`. -/
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    tsupport (fun x => D.correction ε (t, x)) ⊆
      periodicSet (Metric.ball x₀ r)
  /-- `eq:bgzero` on the packet's active interval;
  `paper/sections/03-torus.tex:190-193,214-215`.

  Non-vacuity: for every admissible scale and active time, this supplies an
  actual open neighborhood containing the periodized packet support on which
  the concrete corrected background vanishes pointwise. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, correctedBackground v D.correction ε (t, x) = 0

/-- Exact construction quantifiers for Lemma `lem:potential`;
`paper/sections/03-torus.tex:101-105,163-188,212-215`.

The reference is assumed only periodic and locally smooth/divergence-free.
The packet input contributes only its compact source-time spatial support.
Every cutoff, potential, threshold, and correction witness is chosen before
the scale quantified inside `LocalPotentialAPI`. -/
def localPotentialStatement : Prop :=
  ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
    0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
    IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
    ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D

end BlowupDensity.T16.Draft

/- end verbatim T16 copy -/

/- copied verbatim from research/T15/Spec.lean:510-653; only mixed-norm
   vocabulary and `PlacementData` are retained. -/
-- copied verbatim from research/T17/Spec.lean:525-662
namespace BlowupDensity.T15.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Honest mixed, Sobolev, and energy carriers -/

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure


/-- `03-torus.tex:133-138`: an honest periodic Sobolev Bochner path; the
registered `IsPeriodicDatum` includes Haar integrability. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure


/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`, with
`ENNReal.toReal ⊤=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-- The torus exponent is definitionally the registered `I03.scaling`
exponent, `03-torus.tex:130-131`. -/
example (p q : ℝ≥0∞) :
    alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-! ## Placement data fixed before every scale -/

/-- The choices and smallness conditions made at `03-torus.tex:101-107`.
`Kstar` contains both spatial packet supports.  Its scaled translate lies in a
fixed coordinate ball whose closure is inside the fundamental cube; this is
the hypothesis that makes the lattice sum a single copy on that cube. -/
structure PlacementData {ν : ℝ} (P : PacketAPI ν) where
  /-- `03-torus.tex:103-106`: the target singular time `T`.

  Non-vacuity: positivity makes `(0,T)` a genuine evolution interval. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`.

  Non-vacuity: this rules out the empty or reversed time interval. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`.

  Non-vacuity: it is used in the concrete ball containment below. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`.

  Non-vacuity: the next field requires this radius to be positive. -/
  chartRadius : ℝ
  /-- `03-torus.tex:22-23,102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:22-23,102-105`: the closure of `B` is contained in the
  coordinate chart, here the interior of the fixed fundamental cube.

  Non-vacuity: this is the separation from other lattice translates used by
  the single-copy clauses. -/
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`.

  Non-vacuity: the point is tied to the same concrete chart ball. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`.

  Non-vacuity: this is membership in the explicit ball above. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`.

  Non-vacuity: the following three fields constrain this actual set. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact.

  Non-vacuity: this is an assertion about the carried set, not an existential
  choice made separately for each scale. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is T14's packet carrier.

  Exact quantifier order: every point of `P.carrier` lies in the fixed
  `Kstar`.  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : P.carrier ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales.

  Non-vacuity: every conclusion below uses the same interval `(0,ε₀]`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`.

  Non-vacuity: `(0,ε₀]` contains admissible scales. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`.

  Non-vacuity: this is a quantitative restriction on the one threshold. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined.

  Exact quantifier order: first `ε∈(0,ε₀]`, then the inequality.
  Non-vacuity: it gives `t_ε>0`, so positive-time force norms contain the
  complete rescaled temporal support. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`.

  Exact quantifier order: first `ε∈(0,ε₀]`, then every `y∈Kstar`.
  Non-vacuity: together with `chartBall_in_cube`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

end BlowupDensity.T15.Spec
/- end verbatim T15 copy -/

-- copied verbatim from research/T17/Spec.lean:665-987
namespace BlowupDensity.T17.Spec

/- The correction block is copied verbatim, with this local spelling making
   the shared placement record the T15.Draft one used by the scaling block. -/
abbrev PlacementData {ν : ℝ} (P : BlowupDensity.Contracts.V1.PacketAPI ν) :=
  BlowupDensity.T15.Draft.PlacementData P

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open BlowupDensity.T15.Spec
open BlowupDensity.T16.Draft
open scoped ContDiff ENNReal Topology BigOperators

/-- `03-torus.tex:245-260`: the fixed manuscript cylinder in rescaled
coordinates.  Its endpoints and radius are independent of `ε`. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) D.θRadius

/-- `03-torus.tex:256-259`: the correction chart based at `T`, not at
`T-ε²`; this is the chart used by both profile identities. -/
def correctionChartPoint {ν : ℝ} {P : PacketAPI ν}
    (place : PlacementData P) (ε : ℝ) (z : SpaceTime) : SpaceTime :=
  (place.T + ε ^ 2 * z.1, place.x₀ + ε • z.2)

/-- `03-torus.tex:245,262-263`: `V_ε(z,σ)=v(T+ε²σ,x₀+εz)`. -/
def rescaledReference {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) : SpaceTimeField :=
  fun z => v (place.T + ε ^ 2 * z.1, place.x₀ + ε • z.2)

/-- `03-torus.tex:247-253`: the amplitude-one radial-potential profile
`𝒜_ε(z,σ)=∫₀¹ρ v(T+ε²σ,x₀+ερz)×z dρ`. -/
def rescaledPotential {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) : SpaceTimeField :=
  fun z => ∫ ρ in (0 : ℝ)..1,
    ρ • cross
      (v (place.T + ε ^ 2 * z.1,
        place.x₀ + ε • (ρ • z.2))) z.2

/-- `03-torus.tex:256-259`: the exact amplitude-one correction profile
`W_ε=-curl_z(η(σ)θ(z)𝒜_ε)`. -/
def rescaledCorrectionProfile (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) (D : CutoffData) : SpaceTimeField :=
  fun z => -curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotential v place ε (z.1, y)) z.2

/-- `03-torus.tex:264-272`: the bracketed amplitude-one force profile. -/
def rescaledForceProfile (ν : ℝ) (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) (D : CutoffData) : SpaceTimeField :=
  let W := rescaledCorrectionProfile v place ε D
  let V := rescaledReference v place ε
  fun z =>
    temporalDerivative W z.1 z.2 - ν • spatialLaplacian W z.1 z.2 +
      ε • spatialDerivative W z.1 z.2 (V z) +
      (ε ^ 2) • spatialDerivative v
        (place.T + ε ^ 2 * z.1) (place.x₀ + ε • z.2) (W z) +
      ε • advection W z.1 z.2

/-- `03-torus.tex:219-223`: the registered force formula
`∂ₜw−νΔw+(v·∇)w+(w·∇)v+(w·∇)w`. -/
def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2

/-- `03-torus.tex:225`: the torus-lifted spacetime field used to measure one
periodic copy of the force support. -/
def torusSpaceTimeLift (f : SpaceTimeField) : ℝ × PeriodicTorus → Space :=
  fun z => torusLift (fun x => f (z.1, x)) z.2

/-- `03-torus.tex:225`: spatial projection of the lifted support. -/
def torusSpatialSupport (f : SpaceTimeField) : Set PeriodicTorus :=
  Prod.snd '' tsupport (torusSpaceTimeLift f)

/-- `03-torus.tex:225`: temporal projection of the same lifted support. -/
def torusTemporalSupport (f : SpaceTimeField) : Set ℝ :=
  Prod.fst '' tsupport (torusSpaceTimeLift f)

/-- Reconciled Type-valued API for `lem:correction`,
`paper/sections/03-torus.tex:218-285`.  The placement packet is threaded only
so T15/T17/T18 share definitionally the same `T,x₀,K_*,B,ε₀`; no packet field
is used by the correction mathematics.  Every norm bound carries the guard
that makes its Bochner integrals honest. -/
structure CorrectionAPI (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData) : Type where
  /-- `03-torus.tex:176-217`: a T16 local-potential witness for the same
  reference, enlarged set, chart center, radius, time, margin, and cutoffs.
  Non-vacuity: this field carries the concrete potential and correction family
  used by every later field. -/
  potential : LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D
  /-- `03-torus.tex:22-98`: the T13 localization witness used for the fractional
  torus estimate.  Non-vacuity: its six concrete integral identities and
  endpoint transfers are available to the `H^s` consumer. -/
  localization : LocalizationAPI
  /-- `03-torus.tex:219-223`: positive viscosity.  Non-vacuity: excludes the
  degenerate zero-viscosity force formula. -/
  viscosity_pos : 0 < ν
  /-- `03-torus.tex:102-105`: positive chart radius.  Non-vacuity: the local
  ball used by the potential is nonempty. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:102-105`: `ball x₀ r ⊆ ball chartCenter chartRadius`.
  Non-vacuity: this is the chart inclusion consumed by T13's localization
  witness together with `place.chartBall_in_cube`. -/
  ball_in_chart : Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius
  /-- `03-torus.tex:103,242`: the T16 threshold is within the shared placement
  threshold.  Non-vacuity: all scale clauses use one common interval. -/
  eps_le_placement : D.ε₀ ≤ place.ε₀
  /-- `03-torus.tex:2-4`: the reference velocity is unit-periodic.
  Non-vacuity: this is the actual periodicity hypothesis used by every chart
  and torus norm. -/
  reference_periodic : IsPeriodicOn univ v

  /-- `03-torus.tex:256-260`: the correction profile is smooth on the fixed
  cylinder.  Non-vacuity: this is regularity of the displayed `W_ε`, not an
  unspecified profile. -/
  correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile v place ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:256-260`: `W_ε` is supported in the fixed cylinder.
  Non-vacuity: the topological support of the concrete profile is bounded. -/
  correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile v place ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:254-260`: data constants for every full derivative order.
  Non-vacuity: the constants are selected before `ε`. -/
  correctionProfileConst : ℕ → ℝ
  /-- `03-torus.tex:254-260`: nonnegative profile constants.  Non-vacuity:
  excludes a negative real witness collapsed by `ENNReal.ofReal`. -/
  correctionProfileConst_nonneg : ∀ k, 0 ≤ correctionProfileConst k
  /-- `03-torus.tex:254-260`: uniform derivative bounds for `W_ε`.
  Non-vacuity: each fixed order has one bound on every admissible scale. -/
  correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v place ε D) z‖ ≤
        correctionProfileConst k
  /-- `03-torus.tex:262-273`: the force profile is smooth on the fixed
  cylinder.  Non-vacuity: this regularity applies to the displayed bracket. -/
  force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν v place ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:262-273`: the bracketed force profile is supported in the
  fixed cylinder.  Non-vacuity: no unbounded rescaled support is admitted. -/
  force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν v place ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:262-273`: data constants for force-profile derivatives.
  Non-vacuity: the constants are fixed before `ε`. -/
  forceProfileConst : ℕ → ℝ
  /-- `03-torus.tex:262-273`: nonnegative force-profile constants.
  Non-vacuity: excludes a negative witness collapsed by `ENNReal.ofReal`. -/
  forceProfileConst_nonneg : ∀ k, 0 ≤ forceProfileConst k
  /-- `03-torus.tex:262-273`: uniform derivative bounds for the bracket.
  Non-vacuity: every fixed order is controlled throughout the cylinder. -/
  force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v place ε D) z‖ ≤
        forceProfileConst k
  /-- `03-torus.tex:256-259`: physical correction equals `W_ε` in the chart.
  Non-vacuity: this links the bound-bearing family `D.correction` to the
  profile family rather than leaving them independent. -/
  correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint place ε z) =
        rescaledCorrectionProfile v place ε D z
  /-- `03-torus.tex:264-272`: physical force equals `ε⁻²` times the bracket.
  Non-vacuity: this is the exact affine rescaling identity with all three
  interior powers present in the profile definition. -/
  force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint place ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v place ε D z
  /-- `03-torus.tex:225`: global smoothness across `T` and zero extension.
  Non-vacuity: this is a regularity property of the concrete `H_ε`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν v D ε)
  /-- `03-torus.tex:225,235-240`: unit periodicity of `H_ε`.
  Non-vacuity: it makes the torus lift represent the physical force. -/
  force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν v D ε)
  /-- `03-torus.tex:225`: force support on the torus lift uses the manuscript's
  open spatial ball.  Non-vacuity: no closed-ball weakening is allowed. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν v D ε) ⊆
      Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.ball place.x₀ (ε * D.θRadius))
  /-- `03-torus.tex:225`: real spatial-volume constant.  Non-vacuity:
  nonnegativity below makes its `ENNReal.ofReal` bound meaningful. -/
  spatialVolumeConst : ℝ
  /-- `03-torus.tex:225`: spatial-volume constant is nonnegative.
  Non-vacuity: this rules out a negative constant erased by `ENNReal.ofReal`. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- `03-torus.tex:225`: one-copy torus spatial support has volume `O(ε³)`.
  Non-vacuity: the support is measured after the torus lift, not in periodic
  Euclidean space where it would have infinite volume. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- `03-torus.tex:225`: temporal projection has length at most `4ε²`.
  Non-vacuity: the same lifted support is used for both projections. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2)
  /-- `03-torus.tex:226-229`: derivative constants for `w_ε`.
  Non-vacuity: these are concrete data fixed before the scale quantifier. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- `03-torus.tex:226-229`: nonnegative correction derivative constants.
  Non-vacuity: each displayed rate has a nonnegative real coefficient. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `03-torus.tex:226-229`: arbitrary unit time/spatial directions give
  `C_{j,m} ε^{-2j-m}`.  Non-vacuity: the guard `(∀ i, ‖u i‖≤1)` makes the
  iterated Fréchet derivative a genuine directional derivative bound. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)
  /-- `03-torus.tex:229-232`: force derivative constants.
  Non-vacuity: these coefficients are selected before `ε`. -/
  forceDerivConst : ℕ → ℝ
  /-- `03-torus.tex:229-232`: nonnegative force derivative constants.
  Non-vacuity: no negative coefficient is hidden by `ENNReal.ofReal`. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `03-torus.tex:229-232`: spatial directional bound including `m=0`.
  Non-vacuity: the unit-direction guard makes the derivative tensor honest. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (ε⁻¹) ^ (2 + m)
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` slices of
  `w_ε`.  Non-vacuity: these guards make both Bochner integrals in `energyENormT`
  honest rather than junk-small. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction ε (t, x))) 2 periodicTorusMeasure
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` full-gradient
  slices.  Non-vacuity: this is the second honesty guard for `energyENormT`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction ε) t x)) 2
      periodicTorusMeasure
  /-- `03-torus.tex:234,242`: real energy constant fixed before `ε`.
  Non-vacuity: its nonnegative field prevents a collapsed negative witness. -/
  energyConst : ℝ
  /-- `03-torus.tex:234,242`: energy constant nonnegative.
  Non-vacuity: the real coefficient cannot collapse to zero through `ofReal`. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- `03-torus.tex:234-280`: `‖w_ε‖_{E_T}≤Cε^{3/2}` with T10's torus
  energy norm.  Non-vacuity: the two preceding `MemLp` fields make the
  ess-supremum and lower Bochner integral honest. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT place.T (D.correction ε) ≤
      ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:235-237`: every force slice has an honest Haar-`L^p`
  representative.  Non-vacuity: this is the slice guard for the mixed norm. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v D ε (t, x))) p
        periodicTorusMeasure
  /-- `03-torus.tex:235-237,242`: real mixed constants fixed before `ε`.
  Non-vacuity: nonnegativity below prevents `ENNReal.ofReal` collapse. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:235-237,242`: mixed constants are nonnegative.
  Non-vacuity: this applies on the exact `1≤p,q` range of the bound. -/
  mixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst p q
  /-- `03-torus.tex:235-237,281-282`: for `[Fact (1≤p)]` and `1≤q`,
  `‖H_ε‖_{L^q_tL^p_x}≤C_{p,q} ε^{alpha(p,q)+1}`.  The slice `MemLp`
  field above is the hygiene guard making each representing path honest. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (mixedConst p q * ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1))
  /-- `03-torus.tex:239-242`: real Sobolev constants fixed before `ε`.
  Non-vacuity: strict positivity below makes the displayed finite bound
  meaningful on the full `[0,1]` range. -/
  sobolevConst : ℝ → ℝ
  /-- `03-torus.tex:239-242`: `C_s>0` on `0≤s≤1`.
  Non-vacuity: strict positivity excludes a collapsed Sobolev coefficient. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s
  /-- `03-torus.tex:239-242`: an honest `L¹_tH^s_x` Fourier-data path.
  Non-vacuity: `MemLp` makes the Bochner infimum in `forceSobolevENormT` honest. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      MemForceSobolevT 1 s (correctionForce ν v D ε)
  /-- `03-torus.tex:239-242,284`: the `H^s` estimate, with its honest
  `MemForceSobolevT 1 s` guard and `0≤s≤1` quantifiers. -/
  force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))

/-- `Contracts.V1.Correction.lean:160`: arithmetic drift check for the
registered exponent.  It is intentionally not a record field. -/
example (p q : ℝ≥0∞) :
    -2 + 3 / p.toReal + 2 / q.toReal =
      BlowupDensity.Contracts.V1.alpha p q + 1 := by
  simp [BlowupDensity.Contracts.V1.alpha]
  ring

/-- The local mixed norm is definitionally the copied T15 vocabulary. -/
example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    mixedLebesgueENormT q p f = BlowupDensity.T15.Spec.mixedLebesgueENormT q p f := rfl

/-- The copied T15 exponent is definitionally the registered exponent. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.T15.Spec.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-- The existential closure matches the registered statement style without
adding a mathematical field. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P)
    (v : SpaceTimeField) (r δ : ℝ),
    ∃ D : CutoffData,
      LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (CorrectionAPI ν place v r δ D)

end BlowupDensity.T17.Spec
-- copied verbatim from research/T12/Spec.lean:166-470
namespace BlowupDensity.T12.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## Definitional checks required by the lane brief -/

/-- `Contracts/V1/Data.lean:741-744`: the registered inhomogeneous
completed-density abbreviation is definitionally `CompletedDenseVia` with
`IsSobolevPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- `Contracts/V1/Data.lean:746-753`: the registered homogeneous
completed-density abbreviation is definitionally `CompletedDenseVia` with
`IsHomogeneousPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-! ## Scalar datum and physical membership classes -/

/-- `01-introduction.tex:83-84`: `A` is the order-`s` weighted Fourier
datum of a real scalar periodic field.  This is the scalar mirror of T10's
`IsPeriodicDatum`, including its periodicity and Haar-integrability
conjuncts; the exact coefficient quantifier is `∀ k : PeriodicFrequency`. -/
def IsPeriodicScalarDatum (s : ℝ) (z : Space → ℝ)
    (A : PeriodicScalarData) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧
    ∀ k : PeriodicFrequency,
      A k = (periodicFrequencyWeight k) ^ (s / 2) •
        periodicFourierCoeff (fun x ↦ ((z x : ℝ) : ℂ)) k

/-- `01-introduction.tex:83-84`: the total scalar `H^s(T³)` extended norm,
defined exactly like T10's vector norm.  The empty infimum is `⊤`. -/
def periodicScalarSobolevENorm (s : ℝ) (z : Space → ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicScalarData // IsPeriodicScalarDatum s z A}, ‖A.1‖ₑ

/-- `appendix-a-local-theory.tex:8-12`: scalar membership in periodic
`H^m`.  The conjunct order is periodicity, physical `L²`, then finiteness of
the total scalar datum norm. -/
def MemPeriodicHmScalar (m : ℕ) (z : Space → ℝ) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    periodicScalarSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-a-local-theory.tex:8-12`: vector membership in periodic
`H^m`.  The conjunct order is periodicity, physical `L²`, then finiteness of
T10's total vector datum norm. -/
def MemPeriodicHmVector (m : ℕ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    periodicSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-b-embeddings.tex:20-22,26-27`: a physical mean-zero periodic
representative with finite displayed homogeneous norm.  The exact conjunct
order is periodicity, physical `L²`, physical Haar mean zero, then finiteness. -/
def MemPeriodicHomogeneous (s : ℝ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    IsMeanZeroT z ∧ periodicHomogeneousENorm s z ≠ ⊤

/-- `appendix-b-embeddings.tex:34-37`: the smooth periodic fields used by the
article's derivative displays.  Smoothness precedes physical periodicity. -/
def SmoothPeriodicT (z : SpatialField) : Prop :=
  ContDiff ℝ ∞ z ∧ IsPeriodicSpatial z

/-- `01-introduction.tex:104`: the physical `L^p(T³)` extended norm of any
normed additive target, against normalized Haar measure. -/
def periodicLpENorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (z : Space → E) : ℝ≥0∞ :=
  eLpNorm (torusLift z) p periodicTorusMeasure

/-! ## Registered derivative spelling and the periodic Lambda graph -/

/-- `appendix-b-embeddings.tex:34-37` and `03-torus.tex:467-477`: the
time-independent lift used to reuse the registered spatial operators.
Copied token-for-token from `Contracts/V1/GradientL6.lean:78`. -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-b-embeddings.tex:30-32,97-100`: the physical Frobenius gradient
tensor.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:89-90`. -/
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `appendix-b-embeddings.tex:32,97-100` and `03-torus.tex:467-477`: the
componentwise spatial Laplacian.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:94-95`. -/
def laplacian (v : SpatialField) : SpatialField :=
  fun x => spatialLaplacian (lift v) 0 x

/-- The local lift is definitionally the registered A05 lift. -/
example (v : SpatialField) :
    lift v = BlowupDensity.Contracts.V1.lift v := rfl

/-- The local gradient tensor is definitionally the registered A05 tensor. -/
example (v : SpatialField) :
    gradientTensor v = BlowupDensity.Contracts.V1.gradientTensor v := rfl

/-- The local Laplacian is definitionally the registered A05 Laplacian. -/
example (v : SpatialField) :
    laplacian v = BlowupDensity.Contracts.V1.laplacian v := rfl

/-- `appendix-b-embeddings.tex:8-9,97`: `Lv` is the chosen smooth periodic
physical representative of `Λv`, fixed coefficientwise by the unit-torus
multiplier `2π|k| = sqrt(4π²|k|²)`.  The exact quantifier order after the
smoothness conjunct is component, then lattice frequency. -/
def IsPeriodicLambda (v Lv : SpatialField) : Prop :=
  SmoothPeriodicT Lv ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff (fun x ↦ ((Lv x i : ℝ) : ℂ)) k =
        Real.sqrt (periodicAngularFrequencySq k) *
          periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k

/-! ## Reconciled Type-valued API -/

/-- The torus halves of Lemma A.1 and Lemma B.1, together with the mean-zero
order-two comparison used by Proposition 3.7.  Constants are data fields of
this Type-valued structure and therefore precede every field they control
(`appendix-b-embeddings.tex:109-110`). -/
structure MeanZeroSobolevCalculusAPI where
  /-- `appendix-a-local-theory.tex:8-11`: the tame-product constant family.
  Exact quantifier order: the family is fixed as structure data before `m`,
  the lower-bound proof, and both scalar factors.
  Non-vacuity: `Cproduct_pos` below forces every used value to be positive. -/
  Cproduct : ℕ → ℝ

  /-- `appendix-a-local-theory.tex:8-11`: positivity of the tame-product
  constants.  Exact quantifier order: `∀ m : ℕ`.
  Non-vacuity: this constrains the preceding data family at every order rather
  than permitting a zero constant. -/
  Cproduct_pos : ∀ m : ℕ, 0 < Cproduct m

  /-- `appendix-a-local-theory.tex:12`: the `H²(T³) → L∞(T³)` constant,
  fixed before the vector field.
  Non-vacuity: `Cinfty_pos` below forces this concrete datum to be positive. -/
  Cinfty : ℝ

  /-- `appendix-a-local-theory.tex:12`: positivity of `Cinfty`; there are no
  later quantifiers.
  Non-vacuity: it rules out a zero embedding constant. -/
  Cinfty_pos : 0 < Cinfty

  /-- `appendix-b-embeddings.tex:20-22,26-29`: the critical
  `Ḣ^(1/2)(T³) → L³(T³)` constant, fixed before the field.
  Non-vacuity: `CcriticalHalf_pos` forces a positive datum. -/
  CcriticalHalf : ℝ

  /-- `appendix-b-embeddings.tex:12-17,20-22`: positivity of the half-order
  critical constant; there are no later quantifiers.
  Non-vacuity: it constrains the actual constant used by
  `velocityCriticalL3`. -/
  CcriticalHalf_pos : 0 < CcriticalHalf

  /-- `appendix-b-embeddings.tex:26-31`: the one constant for the displayed
  sum of the gradient and Lambda `L³` norms, fixed before both fields.
  Non-vacuity: `CcriticalThreeHalves_pos` forces a positive datum. -/
  CcriticalThreeHalves : ℝ

  /-- `appendix-b-embeddings.tex:12-13,26-31`: positivity of the
  three-halves constant; there are no later quantifiers.
  Non-vacuity: it constrains the constant used in the combined display. -/
  CcriticalThreeHalves_pos : 0 < CcriticalThreeHalves

  /-- `appendix-b-embeddings.tex:26-32`: the gradient-`L⁶` constant, fixed
  before the field.
  Non-vacuity: `Csix_pos` forces the registered-spelling constant to be
  positive. -/
  Csix : ℝ

  /-- `appendix-b-embeddings.tex:12-13,26-32`: positivity of `Csix`; there
  are no later quantifiers.
  Non-vacuity: it rules out a zero right-hand coefficient. -/
  Csix_pos : 0 < Csix

  /-- `03-torus.tex:490-500`: the mean-zero `H²`/Laplacian comparison
  constant, fixed before the field.
  Non-vacuity: `CHtwo_pos` forces a positive datum. -/
  CHtwo : ℝ

  /-- `03-torus.tex:490-500`: positivity of `CHtwo`; there are no later
  quantifiers.
  Non-vacuity: it constrains the actual continuation constant. -/
  CHtwo_pos : 0 < CHtwo

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: the spectral-gap constant family,
  fixed before the nonnegative order and field.
  Non-vacuity: `Cgap_pos` forces every value used at `0 ≤ s` to be positive. -/
  Cgap : ℝ → ℝ

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: positivity of the gap constant.
  Exact quantifier order: `∀ s : ℝ`, then `0 ≤ s`.
  Non-vacuity: the guard is exactly the guard of `spectralGap`, so every
  applied constant is genuinely positive. -/
  Cgap_pos : ∀ s : ℝ, 0 ≤ s → 0 < Cgap s

  /-- `appendix-a-local-theory.tex:8-11`, `eq:Rproduct`, torus half.
  Exact quantifier order: `m`, `2 ≤ m`, scalar `a`, scalar `b`, membership
  of `a`, then membership of `b`; `Cproduct m` was fixed first.
  Non-vacuity: the two `MemPeriodicHmScalar` hypotheses supply genuine
  periodic `L²` representatives with finite totalized `H^m` norms. -/
  tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : Space → ℝ,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x ↦ a x * b x) ≤
          ENNReal.ofReal (Cproduct m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a)

  /-- `appendix-a-local-theory.tex:8-12`, the torus
  `H² → L∞` clause.  Exact quantifier order: vector `v`, then its order-two
  membership; no mean-zero hypothesis is inserted.
  Non-vacuity: `MemPeriodicHmVector 2 v` supplies a periodic `L²`
  representative and a finite totalized `H²` norm. -/
  boundedRepresentative :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤
        ENNReal.ofReal Cinfty * periodicSobolevENorm 2 v

  /-- `appendix-b-embeddings.tex:20-22,26-29`: the mean-zero torus
  `Ḣ^(1/2) → L³` clause.  Exact quantifier order: vector `v`, then the bundled
  homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous (1 / 2) v` supplies periodicity, a
  physical `L²` representative, zero Haar mean, and a finite homogeneous
  datum norm. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemPeriodicHomogeneous (1 / 2) v →
      periodicLpENorm 3 v ≤
        ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v

  /-- `appendix-b-embeddings.tex:8-9,26-31,97`: every smooth periodic field
  has a chosen physical representative of `Λv`.
  Exact quantifier order: vector `v`, smooth-periodic hypothesis, then
  `∃ Lv : SpatialField`.
  Non-vacuity: the zero field witnesses the hypothesis, while the existential
  conclusion supplies the representative required by the next field. -/
  lambda_exists :
    ∀ v : SpatialField, SmoothPeriodicT v →
      ∃ Lv : SpatialField, IsPeriodicLambda v Lv

  /-- `appendix-a-local-theory.tex:22-26` and
  `appendix-b-embeddings.tex:26-31`: the single displayed order-three-halves
  sum inequality.  Exact quantifier order: `v`, `Lv`, smooth periodicity of
  `v`, bundled order-three-halves membership, then the Lambda graph.
  Non-vacuity: the preceding `lambda_exists` field supplies an `Lv` witness
  for every `SmoothPeriodicT v`; `MemPeriodicHomogeneous (3 / 2) v` supplies
  the finite right-hand norm. -/
  gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicT v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v

  /-- `appendix-b-embeddings.tex:26-32`, used at
  `03-torus.tex:467-477`: the paper-literal mean-zero periodic
  `‖∇v‖₆ ≤ C‖Δv‖₂` clause.  Exact quantifier order: `v`, smooth periodicity,
  then physical zero mean.
  Non-vacuity: the zero field satisfies both hypotheses, while
  `SmoothPeriodicT v` supplies the classical gradient and Laplacian fields;
  the mean-zero hypothesis is retained even though derivatives kill constants. -/
  gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)

  /-- `03-torus.tex:490-500`: the mean-zero comparison used by continuation.
  Exact quantifier order: `v`, smooth periodicity, then physical zero mean.
  Non-vacuity: the zero field witnesses the hypotheses, and for every such
  field the conclusion compares T10's concrete total `H²` norm with the
  registered-spelling classical Laplacian norm. -/
  hTwo_le_laplacian :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal CHtwo * periodicLpENorm 2 (laplacian v)

  /-- `02-preliminaries.tex:50-54` and
  `appendix-b-embeddings.tex:85-90`: the spectral-gap direction of the
  mean-zero norm equivalence.  Exact quantifier order: real `s`, proof
  `0 ≤ s`, vector `v`, then bundled homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous s v` supplies zero mean and a finite
  homogeneous datum norm, and hence excludes the empty-witness `⊤` case on
  the right. -/
  spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (Cgap s) * periodicHomogeneousENorm s v

  /-- `02-preliminaries.tex:50-54`: the converse direction needed for the
  stated equivalence of homogeneous and inhomogeneous norms.
  Exact quantifier order: real `s`, proof `0 ≤ s`, vector `v`, then bundled
  homogeneous membership.
  Non-vacuity: `MemPeriodicHomogeneous s v` supplies a genuine mean-zero
  periodic `L²` representative with finite homogeneous datum; the conclusion
  fixes the converse constant to exactly one. -/
  homogeneous_le_sobolev :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicHomogeneousENorm s v ≤ periodicSobolevENorm s v

end BlowupDensity.T12.Draft

/-!
## The insertion record

The packet import, placement, scaling, and correction records are parameters:
they are the proof's already-constructed data and must be shared definitionally
by every clause.  The reference datum/force and the three inserted fields are
record data because the theorem concludes existence of one common family.
-/

namespace BlowupDensity.T18.DraftA

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T12.Draft
open BlowupDensity.T14.Draft
open BlowupDensity.T15.Draft
open BlowupDensity.T16.Draft
open BlowupDensity.T17.Spec
open scoped ContDiff ENNReal BigOperators Topology

/-- The exact torus insertion theorem of `thm:insertion`,
`paper/sections/03-torus.tex:287-306`, together with the identities used in
its proof at `paper/sections/03-torus.tex:312-346`.

The parameters are the positive-viscosity packet import, one shared placement,
the torus scaling API, the reference field/cutoff data, and the correction API.
The two T11 APIs and T12 calculus are also parameters because the lifespan
argument consumes uniqueness, continuation, and `H² ↪ L∞` rather than
silently postulating those facts as tautological fields.  Every scale-dependent
field is guarded by `ε ∈ Ioc 0 ε₀`; every displayed totalized norm has a
corresponding `MemMixedLebesgueT` or `MemForceSobolevT` witness. -/
structure PeriodicInsertionAPI
    (ν : ℝ) (hν : 0 < ν) (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI P place)
    (localTheory : PeriodicLocalTheoryAPI)
    (continuation : PeriodicContinuationH3API)
    (calculus : MeanZeroSobolevCalculusAPI)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (correction : CorrectionAPI ν place v r δ D)
    (a : SpatialField) (π : SpaceTimeScalar) (g : SpaceTimeField)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (ε₀ : ℝ) : Type where
  /-- `03-torus.tex:287-289`: the reference velocity is the field used by the
  correction API.  Non-vacuity: this pins the proof's `v` to the solution
  rather than allowing an unrelated smooth field. -/
  reference_velocity : reference.velocity = v

  /-- `03-torus.tex:287-289`: the reference pressure is the field used in the
  correction construction.  Non-vacuity: this pins the pressure representative
  used in the insertion formula. -/
  reference_pressure : reference.pressure = π

  /-- `03-torus.tex:287-289`: `δ>0`.  Non-vacuity: the reference horizon is a
  genuine extension beyond the singular time. -/
  delta_pos : 0 < δ

  /-- `03-torus.tex:287-289`: `g ∈ forceClassT`.  Non-vacuity: the concrete
  smooth periodic compact-positive-time force class excludes arbitrary junk
  functions. -/
  reference_force_mem : g ∈ BlowupDensity.Contracts.V1.TorusLocalTheory.forceClassT

  /-- `03-torus.tex:287-289`: `a ∈ initialClassT`.  Non-vacuity: the initial
  field is genuinely smooth, periodic, and solenoidal. -/
  initial_mem : a ∈ initialClassT

  /-- `03-torus.tex:290-291`: `ε₀>0`. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:290-291`: the insertion family only shrinks the scaling
  threshold.  Non-vacuity: all packet and correction estimates remain valid. -/
  eps_le_scaling : ε₀ ≤ place.ε₀
  /-- `03-torus.tex:290-291`: the correction threshold is also respected.
  Non-vacuity: the concrete `CorrectionAPI` bounds apply on every accepted
  scale. -/
  eps_le_correction : ε₀ ≤ D.ε₀

  /-- `03-torus.tex:314`: the inserted velocity family `u_ε`. -/
  velocity : ℝ → VelocityField
  /-- `03-torus.tex:314`: the inserted pressure family `p_ε`. -/
  pressure : ℝ → PressureField
  /-- `03-torus.tex:314`: the inserted force family `g_ε`. -/
  force : ℝ → VelocityField

  /-- `03-torus.tex:314`, `eq:insertion`: `u_ε=v+w_ε+U_ε`, with the
  periodized rescaled packet from `eq:scaling`.  Non-vacuity: the equation is
  pointwise for every spacetime point and fixes the family used below. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = v z + D.correction ε z +
      periodizedScaledVelocity P place.x₀ place.T ε z

  /-- `03-torus.tex:314`, `eq:insertion`: `p_ε=π+P_ε`, with the normalized
  periodized packet pressure.  Non-vacuity: this is a pointwise identity for
  the concrete pressure representative. -/
  pressure_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    pressure ε z = π z + normalizedScaledPressure P place.x₀ place.T ε z

  /-- `03-torus.tex:314`, `eq:insertion`: `g_ε=g+H_ε+F_ε`.
  Non-vacuity: the correction force and packet force are the displayed
  concrete formulas, not unrelated witnesses. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ν v D ε z +
      periodizedScaledForce P place.x₀ place.T ε z

  /-- `03-torus.tex:291-292`: every inserted force lies in `forceClassT`.
  Non-vacuity: class membership expands to smoothness, periodicity and a
  compact positive-time support witness for the actual `force ε`. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    force ε ∈ BlowupDensity.Contracts.V1.TorusLocalTheory.forceClassT

  /-- `03-torus.tex:291-293`: the inserted triple is a classical torus
  solution on `[0,T)`.  Non-vacuity: the existential solution is pinned to
  the record's `velocity` and `pressure`, so it cannot be a junk solution. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ S : ClassicalSolutionT ν a (force ε) place.T,
      S.velocity = velocity ε ∧ S.pressure = pressure ε

  /-- `03-torus.tex:293-294`: T11 uniqueness and continuation identify the
  inserted pair as the maximal periodic solution.  Non-vacuity: this is the
  registered `IsMaximalPeriodicSolution` predicate over the concrete fields. -/
  maximal_solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalPeriodicSolution ν a (force ε) (velocity ε) (pressure ε)

  /-- `03-torus.tex:293-294`: the maximal lifespan is exactly `T`.
  Non-vacuity: equality is in the registered extended-real lifespan, not a
  one-sided inequality. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanT ν a (force ε) = ENNReal.ofReal place.T

  /-- `03-torus.tex:293-294`: the force belongs to the breakdown set at `T`.
  Non-vacuity: `breakdownSetT` simultaneously records force-class membership
  and the exact maximal-lifespan upper bound. -/
  breakdown : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    force ε ∈ breakdownSetT ν a place.T

  /-- `03-torus.tex:293-294`: the inserted speed is unbounded at `T`.
  Non-vacuity: `SpeedUnboundedAt` quantifies every height and every left
  neighborhood and supplies an actual time and spatial witness. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SpeedUnboundedAt place.T (velocity ε)

  /-- `03-torus.tex:294`: the inserted velocity agrees with `v` through
  `T-2ε²`.  Non-vacuity: the equality is pointwise in both time and space. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = v (t, x)

  /-- `03-torus.tex:295`: the velocity perturbation is supported in the
  chosen chart ball at every `t<T`.  Non-vacuity: this constrains the actual
  topological support of `u_ε-v`. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => velocity ε (t, x) - v (t, x)) ⊆
        Metric.ball place.x₀ r

  /-- `03-torus.tex:295`: `u_ε-v` is divergence free, including the initial
  endpoint.  Non-vacuity: the registered spatial divergence is evaluated at
  every presingular time and point. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (fun z => velocity ε z - v z) t x = 0

  /-- `03-torus.tex:332-339`: the first cross transport term vanishes
  pointwise, `(b_ε·∇)U_ε=0`, where `b_ε=v+w_ε`.  Non-vacuity: this is an
  explicit identity for the concrete packet and corrected background. -/
  cross_transport_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (periodizedScaledVelocity P place.x₀ place.T ε) t x
        ((correctedBackground v D.correction ε) (t, x)) = 0

  /-- `03-torus.tex:332-339`: the second cross transport term vanishes
  pointwise, `(U_ε·∇)b_ε=0`.  Non-vacuity: this independently records the
  other transport identity used to make the momentum equation exact. -/
  cross_transport_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (correctedBackground v D.correction ε) t x
        ((periodizedScaledVelocity P place.x₀ place.T ε) (t, x)) = 0

  /-- `03-torus.tex:332-346`: the exact inserted momentum equation, after the
  two cross terms above vanish.  Non-vacuity: this pins the residual at every
  interior spacetime point. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)

  /-- `03-torus.tex:300-301`, `eq:Eclose`: the torus energy rate with the
  exact exponents `ε^{1/2}` and `ε^{3/2}`.  Non-vacuity: the correction's
  slice `MemLp` guards are inherited from `CorrectionAPI`, and the packet
  slice guards are supplied by `ScalingAPI.energySlices_memLp`. -/
  energyRateConst : ℝ
  /-- The energy coefficient is nonnegative, preventing `ofReal` collapse. -/
  energyRateConst_nonneg : 0 ≤ energyRateConst
  /-- Honest Haar-`L²` velocity and gradient slices for the energy norm in
  `eq:Eclose`.  Non-vacuity: this prevents the extended energy expression from
  being finite only because a totalized integral took a junk value. -/
  energyDifference_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    EnergySlicesMemLpT place.T (fun z => velocity ε z - v z)
  /-- `03-torus.tex:300-301`, `eq:Eclose`. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyENormT place.T (fun z => velocity ε z - v z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) *
        ε ^ ((1 : ℝ) / 2) + energyRateConst * ε ^ ((3 : ℝ) / 2))

  /-- Mixed-norm constants for `eq:Fclose`, fixed before `p,q,ε`.
  Non-vacuity: nonnegativity keeps the displayed upper bound meaningful. -/
  mixedRateConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- Positivity guard for the mixed constants. -/
  mixedRateConst_nonneg : ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q →
    0 ≤ mixedRateConst p q
  /-- Honesty and the exact mixed rate `ε^α + ε^{α+1}` from
  `03-torus.tex:302-303`, `eq:Fclose`. -/
  mixedRate : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemMixedLebesgueT q p (fun z => force ε z - g z) ∧
      mixedLebesgueENormT q p (fun z => force ε z - g z) ≤
        ENNReal.ofReal
          (mixedRateConst p q *
            (ε ^ alphaT p q + ε ^ (alphaT p q + 1)))

  /-- Sobolev constants for `eq:Hsclose`, fixed before `s,ε`.
  Non-vacuity: positivity prevents a collapsed totalized bound. -/
  sobolevRateConst : ℝ → ℝ
  /-- The Sobolev coefficient is positive on the displayed range. -/
  sobolevRateConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < sobolevRateConst s
  /-- Honesty and the exact Sobolev rate
  `ε^{α(p,q)+1}` specialized to `L¹_tH^s`, namely
  `ε^{1/2-s}+ε^{3/2-s}`, from `03-torus.tex:304-306`, `eq:Hsclose`. -/
  sobolevRate : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z) ∧
      BlowupDensity.Contracts.V1.TorusLocalTheory.forceSobolevENormT 1 s
        (fun z => force ε z - g z) ≤
        ENNReal.ofReal
          (sobolevRateConst s *
            (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))

  /-- `03-torus.tex:306`: for every negative Sobolev order the force
  difference still tends to zero.  Non-vacuity: this is a genuine right-hand
  limit of the registered force norm, not a finite-order placeholder. -/
  negative_s_convergence : ∀ s : ℝ, s < 0 →
    Tendsto
      (fun ε : ℝ =>
        BlowupDensity.Contracts.V1.TorusLocalTheory.forceSobolevENormT 1 s
          (fun z => force ε z - g z))
      (𝓝[>] 0) (𝓝 0)
  /-- Honest negative-order Sobolev paths used by the last convergence clause.
  Non-vacuity: each totalized negative-order norm has an actual representing
  path for every admissible scale. -/
  negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z)

/-- The paper's existential quantifier order for `thm:insertion`,
`paper/sections/03-torus.tex:287-306`: first positive viscosity, then the
already selected packet/placement/scaling/correction and reference solution,
then one positive threshold `ε₀`, and finally a nonempty API carrying all
clauses for that same data.  The hypotheses before the existential threshold
are exactly the smooth reference assumptions in the theorem statement. -/
def periodicInsertionStatement : Prop :=
  ∀ (ν : ℝ), ∀ hν : 0 < ν,
    ∀ (P : PacketImportAPI ν),
    ∀ (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI),
    ∀ (scaling : ScalingAPI P place),
    ∀ (localTheory : PeriodicLocalTheoryAPI),
    ∀ (continuation : PeriodicContinuationH3API),
    ∀ (calculus : MeanZeroSobolevCalculusAPI),
    ∀ (v : SpaceTimeField) (r δ : ℝ),
      0 < δ →
      ∀ (D : CutoffData),
      ∀ (correction : CorrectionAPI ν place v r δ D),
      ∀ (a : SpatialField) (π : SpaceTimeScalar) (g : SpaceTimeField),
        g ∈ BlowupDensity.Contracts.V1.TorusLocalTheory.forceClassT →
        a ∈ initialClassT →
        ∀ (reference : ClassicalSolutionT ν a g (place.T + δ)),
          reference.velocity = v → reference.pressure = π →
          ∃ ε₀ : ℝ, 0 < ε₀ ∧
            Nonempty
              (PeriodicInsertionAPI ν hν P place scaling localTheory continuation
                calculus v r δ D correction a π g reference ε₀)

end BlowupDensity.T18.DraftA
