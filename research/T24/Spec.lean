import Contracts.V1.TorusData
import Contracts.V1.Packet
import Contracts.V1.HomogeneousNorm
import Contracts.V1.Scaling

/-!
# T24 reconciled specification: further constructions (`sec:variants`)

Statement-only reconciliation of the three "Further constructions" of
`paper/sections/03-torus.tex:667-740`:

* `prop:affine`, `03-torus.tex:668-696` — infinite-dimensional affine variations
  of the localized packet `(U,P,F)` **on whole space** (Theorem 1.1's packet,
  `01-introduction.tex:15-34`), stated over the registered `PacketAPI`;
* `prop:multiple`, `03-torus.tex:697-722` — finitely many prescribed singular
  regions on the torus, superposing T15-rescaled packets;
* `prop:conservative`, `03-torus.tex:723-740` — a conservative torus force from
  rest yields only the zero solution on its classical lifespan.

Everything registered (`Contracts.V1.{Data,Packet,TorusData,Scaling,HomogeneousNorm}`)
is imported, never copied.  The still-unregistered T10 solution-class, T13
localization, T14 packet-import and T15 scaling vocabulary is copied verbatim in
its own namespaces below (the block is identical, byte-for-byte, to
`research/T15/Spec.lean:17-924`; the T13 synchronization header records the
source lines), then the three T24 structures are stated on top of it.

Per the lead's `research/T24/RECONCILIATION.md`: the base draft is B (lane 307),
`prop:affine` is re-based onto whole space (T14 only, terminal time literally
`1`), all geometry is carried as structure parameters rather than data, and the
two false support/zero clauses of draft B are corrected (`zero_from_rest` on
`Ico 0 T` only; supports measured inside `fundamentalCube`).

No declaration constructs an inhabitant.
-/

noncomputable section

/- copied verbatim from research/T10/Spec.lean:255-268,275-359,393-411;
   only the still-unregistered declarations used below -/
namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

/-- `01-introduction.tex:118-140`: `G` is the order-`s` datum trajectory of
the periodic physical field `f` at every nonnegative time. -/
def IsPeriodicSobolevPath (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsPeriodicDatum s (fun x ↦ f (t, x)) (G t)

/-- `01-introduction.tex:118-140` and `03-torus.tex:7`: the physical-field
quantity `‖f‖_{L^q(0,∞;H^s(T³))}`.  It is the infimum over strongly
measurable representing paths, with `⊤` when no such path exists. -/
def forceSobolevENormT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → PeriodicSobolev s //
      IsPeriodicSobolevPath s f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `02-preliminaries.tex:10,23-26` eq:inputspaces:
`C_c∞(T³×(0,∞);R³)` in the periodic-functions-on-`R³` realization.
Only time support is compact in the lift. -/
def MemForceT (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧
    IsPeriodicOn univ f ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ univ

/-- `02-preliminaries.tex:10` eq:inputspaces: the torus force class `F_T`. -/
def forceClassT : Set SpaceTimeField := {f | MemForceT f}

/-! ## 4. Pressure normalization and classical solutions -/

/-- `02-preliminaries.tex:28,84-88`: the normalized spatial mean of a
periodic pressure slice. -/
def pressureMeanT (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  ∫ y : PeriodicTorus, torusLift (fun x ↦ p (t, x)) y ∂periodicTorusMeasure

/-- `02-preliminaries.tex:28,84-88`: the pressure gauge `∫_T³ p(t)=0`,
imposed at every time in `I`. -/
def PressureGaugeT (I : Set ℝ) (p : SpaceTimeScalar) : Prop :=
  ∀ t ∈ I, pressureMeanT p t = 0

/-- `02-preliminaries.tex:84-88` and `03-torus.tex:319`: subtract the
normalized spatial mean from each pressure slice. -/
def normalizePressureT (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p z - pressureMeanT p z.1

/-- `02-preliminaries.tex:28-36,75-115` prop:local: a classical periodic
solution of Navier–Stokes on `[0,T)` at viscosity `ν`, with initial velocity
`a`, prescribed force `f`, periodic velocity and pressure, and the pressure
representative fixed by `∫_T³p=0`.

The Sobolev field has quantifier order `∀ m, ∃ G, ContinuousOn G ... ∧
∀ t, ...`; hence every compact preterminal slice has the paper's smooth
Sobolev regularity without postulating an endpoint value at `T`. -/
structure ClassicalSolutionT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) where
  /-- `02-preliminaries.tex:28-36`: the velocity field. -/
  velocity : SpaceTimeField
  /-- `02-preliminaries.tex:28,84-88`: the scalar pressure, ultimately fixed by
  the zero-mean gauge. -/
  pressure : SpaceTimeScalar
  /-- `02-preliminaries.tex:32-36`: the horizon is a genuine positive
  interval. -/
  horizon_pos : 0 < T
  /-- `02-preliminaries.tex:28-36,105-114`: velocity smoothness on the
  closed-at-zero, open-at-`T` slab. -/
  velocity_smooth :
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `02-preliminaries.tex:28-36,84-103`: pressure smoothness on the same
  slab. -/
  pressure_smooth :
    ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `02-preliminaries.tex:28-29`: `u(0,·)=a`.  Exact quantifier order:
  `∀ x : Space`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `01-introduction.tex:4-7`: `div u=0` on `[0,T)`.  Exact quantifier
  order: `∀ t ∈ Ico 0 T, ∀ x`. -/
  divergence :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- `01-introduction.tex:4-7`: the momentum equation at interior times.
  Exact quantifier order: `∀ t ∈ Ioo 0 T, ∀ x`. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- `02-preliminaries.tex:28-36,105-114`: continuous integer-order Fourier
  data throughout the lifespan.  Exact quantifier order:
  `∀ m : ℕ, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T`. -/
  sobolev : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T,
        IsPeriodicDatum (m : ℝ) (fun x ↦ velocity (t, x)) (G t)
  /-- `02-preliminaries.tex:101-103`: the torus analogue of
  `ClassicalSolutionR.pressure_gradient`, measured on the normalized compact
  torus.  Exact quantifier order: `∀ t ∈ Ico 0 T`. -/
  pressure_gradient : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (torusLift (fun x ↦ pressureGradient pressure t x)) 2 periodicTorusMeasure
  /-- `02-preliminaries.tex:28`: unit spatial periods for velocity.  Exact
  quantifier order is that of `IsPeriodicOn`: `∀ t ∈ Ico 0 T, ∀ x, ∀ i`. -/
  velocity_periodic : IsPeriodicOn (Ico (0 : ℝ) T) velocity
  /-- `02-preliminaries.tex:28,101-103`: unit spatial periods for pressure.
  Exact quantifier order is `∀ t ∈ Ico 0 T, ∀ x, ∀ i`. -/
  pressure_periodic : IsPeriodicOn (Ico (0 : ℝ) T) pressure
  /-- `02-preliminaries.tex:28,84-88`: the paper's unique periodic pressure
  representative.  Exact quantifier order: `∀ t ∈ Ico 0 T`. -/
  pressure_gauge : PressureGaugeT (Ico (0 : ℝ) T) pressure

/-- `01-introduction.tex:143-150` eq:Enorm: the periodic
`L∞(0,T;L²(T³))` extended norm, on the open time interval. -/
def energyEssSupT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup
    (fun t ↦ eLpNorm (torusLift (fun x ↦ z (t, x))) 2 periodicTorusMeasure)
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:143-150` eq:Enorm: the periodic
`L²(0,T;L²(T³))` norm of the full spatial gradient. -/
def energyGradientT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x ↦ spatialGradient z t x)) 2 periodicTorusMeasure) ^
        (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143-150` eq:Enorm and `03-torus.tex:540-561`:
`‖z‖_{E_T}=‖z‖_{L∞_tL²_x}+‖∇z‖_{L²_tL²_x}` on `(0,T)`, with no
endpoint value imposed at `T`. -/
def energyENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  energyEssSupT T z + energyGradientT T z

end BlowupDensity.T10.Draft
/- end verbatim T10 copy -/

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
/- end verbatim T13 copy -/

/- copied verbatim from research/T14/Spec.lean:44-108,120-132 -/
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

/-! ## T24a: infinite-dimensional affine variations (`prop:affine`, whole space)

`prop:affine` is the **whole-space** statement (`03-torus.tex:669-671` fixes the
Theorem 1.1 packet and a cylinder `B₀ ⋐ ℝ³`, terminal time `1`).  It therefore
uses the **registered** `Contracts.V1` packet vocabulary and copies nothing from
T10/T13/T15. -/

namespace BlowupDensity.T24.Affine

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:668-671`: the open spacetime cylinder `Q = B₀ × (τ₀,τ₁)`,
with `B₀` the open coordinate ball of centre `c` and radius `r` and `(τ₀,τ₁)`
the time window. -/
def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

/-- `03-torus.tex:672-673`: the admissible perturbation class
`b ∈ C_c^∞(Q;ℝ³)` with `∇·b = 0` — globally smooth, compactly supported inside
the open cylinder, and pointwise divergence-free. -/
def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

/-- The transport term `(v·∇)w` of `eq:affine` (`03-torus.tex:674-676`),
in the registered spatial Fréchet-derivative token. -/
def crossAdvection (v w : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

/-- `eq:affine`, `03-torus.tex:674`: `Ũ = U + b`. -/
def affineVelocity (U b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ U z + b z

/-- `eq:affine`, `03-torus.tex:674`: `P̃ = P`. -/
def affinePressure (P : SpaceTimeScalar) : SpaceTimeScalar := P

/-- `eq:affine`, `03-torus.tex:674-676`: the six-term corrected force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`, in the registered operator
tokens with the transport terms in the paper's order. -/
def affineForce (ν : ℝ) (U F b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-- `03-torus.tex:677,692-696`: the fixed-support `C^m` seminorm as an `ℝ≥0∞`
supremum `∑_{k≤m} ⨆_{z∈K} ‖D^k f(z)‖ₑ`.  The extended `ℝ≥0∞` codomain is the
same choice as `Contracts/V1/Data.lean:475` `energyENorm`: a real `sSup` of an
unbounded range takes its junk value `0`, which would make the non-isolation
`Tendsto` vacuous, whereas the `⨆` in `ℝ≥0∞` never does. -/
def ckSeminormE (K : Set SpaceTime) (m : ℕ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ⨆ z ∈ K, ‖iteratedFDeriv ℝ k f z‖ₑ

/-- Proposition `prop:affine` (`paper/sections/03-torus.tex:668-696`): the
infinite-dimensional affine family of variations of the registered whole-space
packet `P` (Theorem 1.1, `01-introduction.tex:15-34`) inside the fixed cylinder
`Q = ball c r × (τ₀,τ₁)`.

`Prop`-valued: with the cylinder `(c,r,τ₀,τ₁)` carried as a parameter the record
holds no data and introduces no new constant.  The terminal time is the packet's
singular time `1`; the velocity/pressure/force are the registered whole-space
quantities. -/
structure AffineVariationAPI {ν : ℝ} (P : PacketAPI ν)
    (c : Space) (r τ₀ τ₁ : ℝ) : Prop where
  /-- `03-torus.tex:671`: the localization ball `B₀` has positive radius.
  Non-vacuity: excludes the empty ball, so `AffineAdmissible` is inhabited. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:670`: the time window is strictly interior,
  `0 < τ₀ < τ₁ < 1` — "away from the endpoints".
  Non-vacuity: this concrete strict chain keeps the cylinder off both `t=0`
  and the singular time `t=1`. -/
  window : 0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < 1
  /-- `03-torus.tex:681-683`: for every admissible `b` the corrected force `F̃`
  is smooth on all of spacetime (the correction extends smoothly by zero across
  the singularity at `t=1`).
  Exact quantifier order: `∀ b`, admissibility, then global smoothness.
  Non-vacuity: constrains the explicit `affineForce`, not a free proposition. -/
  force_smooth : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ContDiff ℝ ∞ (affineForce ν P.velocity P.force b)
  /-- `03-torus.tex:681-683`: for every admissible `b`, `F̃ ∈ C_c^∞(ℝ³×(0,∞))`
  — compact spacetime support in strictly positive time.
  Exact quantifier order: `∀ b`, admissibility, then the support predicate.
  Non-vacuity: `CompactPositiveTimeSupport` expands to compact support plus a
  positive-time inclusion for this explicit force. -/
  force_support : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    CompactPositiveTimeSupport (affineForce ν P.velocity P.force b)
  /-- `03-torus.tex:673,679`: `∇·(U+b) = 0` on the presingular slab `[0,1)`.
  Exact quantifier order: `∀ b`, admissibility, `∀ t ∈ Ico 0 1`, `∀ x`.
  Non-vacuity: pins the divergence of the explicit `affineVelocity` to `0`;
  uses `∇·U=0` and `∇·b=0`, hence not a tautology. -/
  divergence_free : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (affineVelocity P.velocity b) t x = 0
  /-- `03-torus.tex:674-676,679`, `eq:affine`:
  `∂ₜŨ + (Ũ·∇)Ũ − νΔŨ + ∇P̃ = F̃` at every interior time `(0,1)`.
  Exact quantifier order: `∀ b`, admissibility, `∀ t ∈ Ioo 0 1`, `∀ x`.
  Non-vacuity: equates the registered residual of the explicit affine fields
  with the explicit `affineForce`; true only because `P` solves the packet
  equation, so a genuine constraint. -/
  momentum : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      navierStokesResidual ν (affineVelocity P.velocity b)
          (affinePressure P.pressure) t x =
        affineForce ν P.velocity P.force b (t, x)
  /-- `03-torus.tex:684-685`: zero initial data `Ũ(0,·) = 0` (`b=0` near `t=0`).
  Exact quantifier order: `∀ b`, admissibility, `∀ x`.
  Non-vacuity: pins the explicit affine velocity at `t=0` to `0`. -/
  zero_initial : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ x : Space, affineVelocity P.velocity b (0, x) = 0
  /-- `03-torus.tex:684-685`: `Ũ = U` on the late interval `t ≥ τ₁` (`b=0` near
  `t=1`), hence the same late singular behaviour.
  Exact quantifier order: `∀ b`, admissibility, `∀ t`, `τ₁ ≤ t`, `∀ x`.
  Non-vacuity: forces the affine velocity to equal `U` past `τ₁`. -/
  late_agreement : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t : ℝ, τ₁ ≤ t → ∀ x : Space,
      affineVelocity P.velocity b (t, x) = P.velocity (t, x)
  /-- `03-torus.tex:686`: the same unbounded-speed limit at `t=1`,
  `limsup_{t↑1} ‖Ũ(t)‖_∞ = ∞`.
  Exact quantifier order: `∀ b`, admissibility, then `SpeedUnboundedAtOne`'s
  `M>0, δ>0` and witnesses.
  Non-vacuity: constrains the actual affine velocity near the singular time. -/
  speed_unbounded : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    SpeedUnboundedAtOne (affineVelocity P.velocity b)
  /-- `03-torus.tex:686-687`: finite energy and dissipation,
  `‖Ũ‖_{E_1} < ∞`.
  Exact quantifier order: `∀ b`, admissibility, then finiteness.
  Non-vacuity: `energyENorm 1` is the registered `energyEssSup + energyGradient`,
  so this single bound asserts both finite energy and finite dissipation. -/
  energy_finite : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    energyENorm 1 (affineVelocity P.velocity b) < ⊤
  /-- `03-torus.tex:688-691`: the family is genuinely infinite-dimensional — a
  countable admissible family that is `ℝ`-linearly independent (disjoint
  spatial supports of divergence-free curls).
  Exact quantifier order: `∃ b : ℕ → …`, then `(∀ n, admissible) ∧
  LinearIndependent`.
  Non-vacuity: asserts a concrete linearly independent sequence inside the
  admissible class, not an abstract "infinite-dimensional" phrase. -/
  infinite_dimensional : ∃ b : ℕ → SpaceTimeField,
    (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
  /-- `03-torus.tex:691`: `b ↦ U + b` is injective on the admissible class, so
  distinct perturbations give distinct velocities.
  Exact quantifier order: `∀ b₁ b₂`, both admissibility proofs, `b₁ ≠ b₂`.
  Non-vacuity: an inequality of explicit affine velocities. -/
  distinct : ∀ b₁ b₂ : SpaceTimeField,
    AffineAdmissible c r τ₀ τ₁ b₁ → AffineAdmissible c r τ₀ τ₁ b₂ →
      b₁ ≠ b₂ →
        affineVelocity P.velocity b₁ ≠ affineVelocity P.velocity b₂
  /-- `03-torus.tex:677,692-696`: non-isolation of the rescaled family — for
  each fixed nonzero admissible `b` and each order `m`, the `C^m` seminorm on
  `tsupport b` of the velocity difference `Ũ_{λb}−U` and of the force
  difference `F̃_{λb}−F` tends to `0` as `λ→0`.
  Exact quantifier order: `∀ b`, admissibility, `b ≠ 0`, `∀ m`, then the two
  `Tendsto … (𝓝 0) (𝓝 0)` limits.
  Non-vacuity: both limits constrain the explicit `ckSeminormE` of the explicit
  differences; convergence to `0` in `ℝ≥0∞` is not vacuous because the seminorm
  is an extended supremum, never the real `sSup` junk value. -/
  nonisolated : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 →
    ∀ m : ℕ,
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineVelocity P.velocity (lam • b) z - P.velocity z))
        (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineForce ν P.velocity P.force (lam • b) z - P.force z))
        (𝓝 0) (𝓝 0)

/-- `03-torus.tex:668-696`: the existence form of `prop:affine`.  For every
positive viscosity, every packet from Theorem 1.1, and every cylinder
`ball c r × (τ₀,τ₁)` with `0 < r` and `0 < τ₀ < τ₁ < 1`, the affine-variation
API is inhabited.  Introducing this definition proves no inhabitant. -/
def affineVariationStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketAPI ν) (c : Space) (r τ₀ τ₁ : ℝ),
    0 < r → 0 < τ₀ → τ₀ < τ₁ → τ₁ < 1 →
      Nonempty (AffineVariationAPI P c r τ₀ τ₁)

end BlowupDensity.T24.Affine

/-! ## T24b: finitely many prescribed singular regions (`prop:multiple`, torus)

`prop:multiple` is a torus statement superposing `N` T15-rescaled packets, so it
consumes the copied T10 solution class, T13 `fundamentalCube`, T14
`PacketImportAPI` and T15 `PlacementData`/`ScalingAPI`.  `ν, T, N` and the
prescribed balls are parameters (the paper universally fixes them). -/

namespace BlowupDensity.T24.Multiple

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open BlowupDensity.T14.Draft
open BlowupDensity.T15.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:710`: the finite superposition `u = ∑_j U_j`. -/
def finiteVelocitySum {N : ℕ} (U : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, U j z

/-- `03-torus.tex:710`: the finite superposition `p = ∑_j P_j`. -/
def finitePressureSum {N : ℕ} (P : Fin N → SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ∑ j : Fin N, P j z

/-- `03-torus.tex:710`: the finite superposition `f = ∑_j F_j`. -/
def finiteForceSum {N : ℕ} (F : Fin N → SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑ j : Fin N, F j z

/-- `03-torus.tex:713-717`: unbounded speed in a fixed spatial ball `B` in every
left neighbourhood of the terminal time `T`, i.e. the pointwise reading of
`limsup_{t↑T} ‖u(t)‖_{L∞(B)} = ∞`. -/
def SpeedUnboundedAtOn (T : ℝ) (B : Set Space) (u : SpaceTimeField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space,
      t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ x ∈ B ∧ M < ‖u (t, x)‖

/-- Proposition `prop:multiple` (`paper/sections/03-torus.tex:697-722`) on the
torus: at fixed `ν>0`, `T>0`, and `N` prescribed disjoint interior balls, a
forced solution from rest whose velocity blows up separately in each ball, with
finite energy and dissipation.

`Type`-valued: the record carries the per-region T15 placement/scaling data and
the selected component solutions.  No new constant is introduced: `M, D` are the
imported packet's `energyBound`/`dissipationBound`.

The paper's bounded-domain / homogeneous-no-slip branch (`03-torus.tex:698,706,720`)
is deliberately omitted: no bounded-domain carrier, restriction norm, or no-slip
class exists anywhere in the current tree, so an honest omission is recorded here
rather than a placeholder field — out of V1 scope. -/
structure MultipleRegionsAPI {ν : ℝ} (P : PacketImportAPI ν) (T : ℝ)
    {N : ℕ} (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ) : Type where
  /-- `03-torus.tex:698`: `T>0`.  Non-vacuity: makes `(0,T)` a genuine
  evolution interval. -/
  T_pos : 0 < T
  /-- `03-torus.tex:697-700`: at least one region.  Non-vacuity: rules out the
  empty family, for which every clause below is vacuous. -/
  N_pos : 0 < N
  /-- `03-torus.tex:697-700`: each prescribed ball `B_j` has positive radius.
  Exact quantifier order: `∀ j`.  Non-vacuity: excludes empty balls. -/
  regionRadius_pos : ∀ j : Fin N, 0 < regionRadius j
  /-- `03-torus.tex:697-699`: each `B_j` is an interior ball,
  `closure B_j ⊆ interior Q` for the fundamental cube `Q`.
  Exact quantifier order: `∀ j`.  Non-vacuity: this concrete containment is the
  separation from other lattice translates used by the single-copy transfer. -/
  region_interior : ∀ j : Fin N,
    closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆ interior fundamentalCube
  /-- `03-torus.tex:698-699`: the prescribed balls are pairwise disjoint.
  Non-vacuity: pairwise `Disjoint` of the explicit balls, the premise that kills
  every cross transport `(U_i·∇)U_j`. -/
  regions_disjoint : Pairwise (fun i j : Fin N ↦
    Disjoint (Metric.ball (regionCenter i) (regionRadius i))
      (Metric.ball (regionCenter j) (regionRadius j)))
  /-- `03-torus.tex:701-706`: one T15 placement record per region, over the one
  shared imported packet.
  Exact quantifier order: a function of `j`.  Non-vacuity: `PlacementData`
  concretely carries `x₀, B, K_*, ε₀` and every smallness condition. -/
  placement : Fin N → PlacementData P.toPacketAPI
  /-- `03-torus.tex:721`: all placements share the common terminal time `T`.
  Exact quantifier order: `∀ j`.  Non-vacuity: equates each `(placement j).T`
  with the fixed `T`. -/
  placement_time : ∀ j : Fin N, (placement j).T = T
  /-- `03-torus.tex:701-705`: the T15 chart ball of region `j` is exactly the
  prescribed ball `B_j`.  This is the link without which none of T15's
  chart-ball conclusions attach to `B_j`.
  Exact quantifier order: `∀ j`.  Non-vacuity: pins both chart centre and
  radius to `regionCenter j` / `regionRadius j`. -/
  placement_chart : ∀ j : Fin N,
    (placement j).chartCenter = regionCenter j ∧
      (placement j).chartRadius = regionRadius j
  /-- `03-torus.tex:701-706`: one T15 scaling API per region, over the shared
  packet and that region's placement.
  Exact quantifier order: `∀ j`.  Non-vacuity: `ScalingAPI` concretely carries
  every rescaled-field identity for region `j`. -/
  scaling : ∀ j : Fin N, ScalingAPI P (placement j)
  /-- `03-torus.tex:701-704`: the chosen scale of region `j`. -/
  ε : Fin N → ℝ
  /-- `03-torus.tex:703-704`: each scale is admissible, `ε_j ∈ (0,ε₀]`.
  Exact quantifier order: `∀ j`.  Non-vacuity: membership in the concrete
  admissible interval (in particular `0 < ε_j`). -/
  eps_admissible : ∀ j : Fin N, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀
  /-- `03-torus.tex:702`: `ε_j² < T`, the paper's displayed smallness clause.
  Exact quantifier order: `∀ j`.  Non-vacuity: a concrete inequality on each
  chosen scale. -/
  eps_time : ∀ j : Fin N, ε j ^ 2 < T
  /-- `03-torus.tex:706-712`: the selected component solution of region `j`,
  from rest, with the explicit periodized rescaled force of that region.
  Exact quantifier order: a function of `j`.  Non-vacuity: an actual
  `ClassicalSolutionT` witness, with all its regularity/PDE/gauge fields. -/
  component : ∀ j : Fin N,
    ClassicalSolutionT ν (0 : SpatialField)
      (periodizedScaledForce P (placement j).x₀ T (ε j)) T
  /-- `03-torus.tex:706-712`: each component is pinned to T15's explicit
  periodized velocity and mean-normalized pressure, not an arbitrary solution.
  Exact quantifier order: `∀ j`, then both field equations.
  Non-vacuity: two equalities of explicit fields, forbidding substitution. -/
  component_pin : ∀ j : Fin N,
    (component j).velocity = periodizedScaledVelocity P (placement j).x₀ T (ε j) ∧
      (component j).pressure = normalizedScaledPressure P (placement j).x₀ T (ε j)
  /-- `03-torus.tex:701-712`: on the fundamental cube the component velocity
  vanishes outside its region `B_j` (the single-copy support, measured on the
  cube because the periodized field is spatially periodic and its `ℝ³`-support
  meets every lattice translate).
  Exact quantifier order: `∀ j`, `∀ t ∈ Ico 0 T`, `∀ x ∈ fundamentalCube`,
  `x ∉ B_j`.  Non-vacuity: pins the velocity to `0` on `Q ∖ B_j`; delivered by
  T15's `velocity_singleCopy` and `eps_space`. -/
  component_support : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      (component j).velocity (t, x) = 0
  /-- `03-torus.tex:701-712`: on the fundamental cube the region-`j` force
  vanishes outside `B_j`, at every real time.
  Exact quantifier order: `∀ j`, `∀ t`, `∀ x ∈ fundamentalCube`, `x ∉ B_j`.
  Non-vacuity: pins the periodized force to `0` on `Q ∖ B_j`; delivered by
  T15's `force_singleCopy` and `eps_space`. -/
  component_force_support : ∀ j : Fin N, ∀ t : ℝ, ∀ x ∈ fundamentalCube,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) →
      periodizedScaledForce P (placement j).x₀ T (ε j) (t, x) = 0
  /-- `03-torus.tex:710`: the assembled velocity `u`. -/
  assembled_velocity : SpaceTimeField
  /-- `03-torus.tex:710`: `u = ∑_j U_j`.
  Non-vacuity: equates `assembled_velocity` with the explicit finite sum of the
  component velocities. -/
  assembled_velocity_formula :
    assembled_velocity = finiteVelocitySum (fun j ↦ (component j).velocity)
  /-- `03-torus.tex:710`: the assembled pressure `p`. -/
  assembled_pressure : SpaceTimeScalar
  /-- `03-torus.tex:710`: `p = ∑_j P_j`.
  Non-vacuity: equates `assembled_pressure` with the explicit finite sum. -/
  assembled_pressure_formula :
    assembled_pressure = finitePressureSum (fun j ↦ (component j).pressure)
  /-- `03-torus.tex:710`: the assembled force `f`. -/
  assembled_force : SpaceTimeField
  /-- `03-torus.tex:710`: `f = ∑_j F_j`.
  Non-vacuity: equates `assembled_force` with the explicit finite sum of the
  periodized rescaled forces. -/
  assembled_force_formula :
    assembled_force =
      finiteForceSum (fun j ↦ periodizedScaledForce P (placement j).x₀ T (ε j))
  /-- `03-torus.tex:711-716`: the assembled triple is itself a classical
  periodic solution from rest at the same `ν` and terminal time `T`.
  Non-vacuity: an actual `ClassicalSolutionT` witness for the summed force. -/
  solution : ClassicalSolutionT ν (0 : SpatialField) assembled_force T
  /-- `03-torus.tex:711-716`: the assembled solution's fields are the assembled
  velocity and pressure.
  Non-vacuity: two equalities pinning the solution to the explicit sums. -/
  solution_pin :
    solution.velocity = assembled_velocity ∧ solution.pressure = assembled_pressure
  /-- `03-torus.tex:711-716`: the assembled force is an admissible torus force.
  Non-vacuity: membership of the explicit sum in the concrete `forceClassT`. -/
  force_mem : assembled_force ∈ forceClassT
  /-- `03-torus.tex:711`: rest, `u(0,·) = 0`.
  Exact quantifier order: `∀ x`.  Non-vacuity: pins the assembled velocity at
  `t=0` to `0`. -/
  rest : ∀ x : Space, assembled_velocity (0, x) = 0
  /-- `03-torus.tex:712-717`: on each region `B_j` the sum agrees with its own
  component, so `B_j` inherits that component's singularity.
  Exact quantifier order: `∀ j`, `∀ t ∈ Ico 0 T`, `∀ x ∈ B_j`.
  Non-vacuity: equates the assembled velocity with `(component j).velocity` on
  `B_j`; follows from the disjoint single-copy supports. -/
  region_agreement : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (regionCenter j) (regionRadius j),
      assembled_velocity (t, x) = (component j).velocity (t, x)
  /-- `03-torus.tex:713-717,722`: the separate blow-up in each region,
  `limsup_{t↑T} ‖u(t)‖_{L∞(B_j)} = ∞`.
  Exact quantifier order: `∀ j`, then `SpeedUnboundedAtOn`'s `M,δ` and witnesses.
  Non-vacuity: the assembled velocity attains arbitrarily large values near `T`
  inside each `B_j`. -/
  region_blowup : ∀ j : Fin N,
    SpeedUnboundedAtOn T (Metric.ball (regionCenter j) (regionRadius j))
      assembled_velocity
  /-- `03-torus.tex:718`: the energy bound `sup_{t<T} ‖u(t)‖₂² ≤ M² Σ_j ε_j`,
  in the registered torus `E_T` spelling `(energyEssSupT T u)² ≤ …`, with
  `M = P.energyBound`.
  Non-vacuity: an `ℝ≥0∞` inequality on the explicit essential-supremum energy,
  inherited from T15's `packetEnergyIdentity` by disjointness. -/
  energy_bound : (energyEssSupT T assembled_velocity) ^ (2 : ℕ) ≤
    ENNReal.ofReal (P.energyBound ^ 2 * ∑ j : Fin N, ε j)
  /-- `03-torus.tex:719`: the dissipation identity
  `∫₀^T ‖∇u(t)‖₂² dt = D² Σ_j ε_j`, an equality (`=`, not `≤`), in the spelling
  `(energyGradientT T u)² = …` with `D = P.dissipationBound`.
  Non-vacuity: an `ℝ≥0∞` equality on the explicit gradient energy, inherited
  from T15's `packetDissipationIdentity` by disjointness. -/
  dissipation_bound : (energyGradientT T assembled_velocity) ^ (2 : ℕ) =
    ENNReal.ofReal (P.dissipationBound ^ 2 * ∑ j : Fin N, ε j)

/-- `03-torus.tex:697-722`: the existence form of `prop:multiple`.  For every
`ν>0`, imported packet, `T>0`, and every finite family of disjoint interior
balls, the multiple-regions API is inhabited.  Introducing this definition
proves no inhabitant. -/
def multipleRegionsStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν) (T : ℝ), 0 < T →
    ∀ (N : ℕ), 0 < N →
      ∀ (regionCenter : Fin N → Space) (regionRadius : Fin N → ℝ),
        (∀ j : Fin N, 0 < regionRadius j) →
        (∀ j : Fin N, closure (Metric.ball (regionCenter j) (regionRadius j)) ⊆
          interior fundamentalCube) →
        Pairwise (fun i j : Fin N ↦
          Disjoint (Metric.ball (regionCenter i) (regionRadius i))
            (Metric.ball (regionCenter j) (regionRadius j))) →
        Nonempty (MultipleRegionsAPI P T regionCenter regionRadius)

end BlowupDensity.T24.Multiple

/-! ## T24c: conservative forcing from rest (`prop:conservative`, torus)

`prop:conservative` is a universal implication on the torus, so it consumes only
the copied T10 solution class.  `Prop`-valued: it chooses no witness. -/

namespace BlowupDensity.T24.Conservative

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-- `03-torus.tex:723-726`: the conservative potential class — a globally
defined smooth scalar `φ` on spacetime, unit-periodic in every spatial
coordinate.  Periodicity excludes the affine (non-periodic) gauges the paper
sets aside. -/
def PeriodicPotentialT (φ : SpaceTimeScalar) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsPeriodicOn univ φ

/-- `03-torus.tex:723-726`: the conservative force `f = -∇φ`, in the registered
pressure-gradient token. -/
def conservativeForceT (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- Proposition `prop:conservative` (`paper/sections/03-torus.tex:723-740`) on
the torus.  `Prop`-valued: two universal implications choosing no witness or
constant.

The paper's bounded-domain branch with homogeneous no-slip (`03-torus.tex:724-725`)
is deliberately omitted: no bounded-domain / no-slip carrier exists in the tree,
so only the torus branch is stated — out of V1 scope. -/
structure ConservativeForcingAPI : Prop where
  /-- `03-torus.tex:729-731`: the displayed pairing `∫_{T³} f·u = -∫∇φ·u = 0`
  at every time of the classical lifespan, for every smooth periodic `φ` and
  every solution `S` from rest with force `-∇φ`.
  Exact quantifier order: `∀ ν`, `∀ T`, `0<T`, `∀ φ`, `PeriodicPotentialT φ`,
  `∀ S`, `∀ t ∈ Ico 0 T`.
  Non-vacuity: constrains the Haar integral of the explicit inner product
  `⟪-∇φ(t), u(t)⟫` to be `0`; it holds only through incompressibility and
  periodicity of `u`, hence a genuine integration-by-parts claim, not `True`. -/
  potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0
  /-- `03-torus.tex:723-728,732-737`: from rest, a conservative torus force
  yields only the zero solution on its classical lifespan — `u ≡ 0` on `[0,T)`
  (corrected from a global `u = 0`, which is false off the slab that
  `ClassicalSolutionT` constrains).
  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, `∀ φ`,
  `PeriodicPotentialT φ`, `∀ S`, `∀ t ∈ Ico 0 T`, `∀ x`.
  Non-vacuity: pins the velocity of every such solution to `0` on the whole
  lifespan; it follows from `potential_pairing` and the classical energy
  identity, so it constrains real solution data. -/
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0

/-- `03-torus.tex:723-740`: the statement form of `prop:conservative` (already a
`Prop`; introducing this alias asserts nothing). -/
def conservativeForcingStatement : Prop := ConservativeForcingAPI

end BlowupDensity.T24.Conservative
