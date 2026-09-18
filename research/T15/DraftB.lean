import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti
import Contracts.V1.HomogeneousNorm
import Contracts.V1.Packet
import Contracts.V1.Scaling

/-!
# T15 double-blind draft B: scaling at fixed viscosity on the unit torus

This statement-only draft specifies `prop:scaling`,
`paper/sections/03-torus.tex:101-159`.  It keeps the physical `(P)`
representation chosen in `collaboration/SECTION3_PLAN.md` §1: fields live on
`R^3`, and a lattice sum gives their unit-periodic realization.  The support
geometry below makes that sum a single copy in the fixed fundamental cube.

The temporary T10, T14, and T13 declarations are copied below because files in
`research/` are not Lake modules.  Delete the copies once their contracts are
registered.  No declaration imports an implementation candidate from
`NSFormalization.Paper1`.
-/

noncomputable section

/- copied from research/T10/Spec.lean:46-405 (selected declarations); delete
once T01.torus_data is registered -/
namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the frequency lattice of the unit
three-torus. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: Mathlib's unit additive three-torus. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: normalized Haar measure on the unit torus. -/
abbrev periodicTorusMeasure : Measure PeriodicTorus := volume

/-- `03-torus.tex:2-4` and the (P) representation fixed in
`collaboration/SECTION3_PLAN.md` §1: invariance under every positive unit
coordinate shift. Quantification over all `x` also supplies negative shifts. -/
def IsPeriodicSpatial {E : Type*} [Add E] (z : Space → E) : Prop :=
  ∀ x : Space, ∀ i : Fin 3, z (x + coordinateVector i) = z x

/-- `02-preliminaries.tex:28`: spatial periodicity on a specified set of times,
with time as the first spacetime coordinate. -/
def IsPeriodicOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t ∈ I, ∀ x : Space, ∀ i : Fin 3,
    z (t, x + coordinateVector i) = z (t, x)

/-- `03-torus.tex:2-4`, `01-introduction.tex:89`, and `TorusCube.lean:25-26`: canonical realization
of the (P) field on Mathlib's unit torus, using representatives in `(0,1]^3`.
This is the local `NSFormalization.Paper1.torusLift` definition restated
verbatim, with its one-line `toSpace` map expanded. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f ((EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) z).val))

/-- `03-torus.tex:2-4` and `01-introduction.tex:89`: the coefficient
`ẑ(k) = ∫_T³ z(x) exp(-2π i k·x) dx`.  This is exactly the local
`NSFormalization.Paper1.periodicFourierCoeff`, restated so the eventual
contract needs no local implementation import. -/
def periodicFourierCoeff (f : Space → ℂ) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-84`: the squared Bessel weight
`1 + 4π²|k|²` in the unit-period convention. -/
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `03-torus.tex:2-4`: scalar complete `ℓ²(Z³;ℂ)` coefficient data. -/
abbrev PeriodicScalarData := lp (fun _ : PeriodicFrequency ↦ ℂ) 2

/-- `03-torus.tex:2-4` and `01-introduction.tex:103`: three scalar coefficient sequences with the
Euclidean (`PiLp 2`) product norm. -/
abbrev PeriodicVectorData := WithLp 2 (Fin 3 → PeriodicScalarData)

/-- `02-preliminaries.tex:72-73`: the conjugate-reflection real subspace of
three-component complex Fourier data. -/
def realPeriodicSubmodule : Submodule ℝ PeriodicVectorData where
  carrier := {A | ∀ i : Fin 3, ∀ k : PeriodicFrequency, A i (-k) = star (A i k)}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i k
    change A i (-k) + B i (-k) = star (A i k + B i k)
    rw [hA i k, hB i k]
    exact (star_add _ _).symm
  smul_mem' := by
    intro r A hA i k
    change (r : ℂ) * A i (-k) = star ((r : ℂ) * A i k)
    rw [hA i k]
    simp

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the complete real three-vector Sobolev datum
at order `s`.  An element is the *weighted* sequence
`(1+4π²|k|²)^(s/2) ẑ(k)` in `ℓ²`; `s` is a phantom index recording
the realization represented by that sequence. -/
abbrev PeriodicSobolev (_s : ℝ) := realPeriodicSubmodule

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: `A` is the order-`s` weighted Fourier datum
of the real physical field `z`.  The exact quantifier order is component first,
then lattice frequency.

Lead amendment (2026-09-17, `RECONCILIATION.md` §5): the datum requires the
lifted field to be Haar-integrable.  Without it the Bochner integral defining
`periodicFourierCoeff` is the junk value `0` for every non-integrable periodic
`z`, so `A = 0` would be a datum of e.g. the periodization of `x ↦ 1/x₁` and
`periodicSobolevENorm` would be `0` instead of `⊤` there. -/
def IsPeriodicDatum (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (periodicFrequencyWeight k) ^ (s / 2) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the total `H^s(T³)` extended norm of a
physical field, defined as the infimum of the norms of all representing data.
The empty infimum is `⊤`. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicDatum s z A}, ‖A.1‖ₑ

/-- `03-torus.tex:395-401`: the normalized spatial mean of a real vector
field on the unit torus. -/
def meanT (z : SpatialField) : Space :=
  ∫ y : PeriodicTorus, torusLift z y ∂periodicTorusMeasure

/-- `03-torus.tex:395-401`: `z - ∫_T³ z`, the mean-free part of a periodic
field. -/
def meanZeroPartT (z : SpatialField) : SpatialField := fun x ↦ z x - meanT z

/-- `03-torus.tex:395-411`: a physical field has zero normalized torus mean. -/
def IsMeanZeroT (z : SpatialField) : Prop := meanT z = 0

/-- `01-introduction.tex:105-107`: the squared angular frequency
`|2πk|² = 4π²|k|²` in the unit-period convention. -/
def periodicAngularFrequencySq (k : PeriodicFrequency) : ℝ :=
  4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `01-introduction.tex:105-107`: the homogeneous multiplier
`|2πk|^s = (4π²|k|²)^(s/2)`.  The omitted zero mode is represented by zero,
so every homogeneous datum has `A(0)=0`. -/
def homogeneousDatumWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else Real.rpow (periodicAngularFrequencySq k) (s / 2)

/-- `01-introduction.tex:105-109`: `A` is the order-`s` homogeneous datum of a
mean-zero real periodic field.  Exact quantifier order: periodicity,
Haar integrability of the lift (lead amendment, `RECONCILIATION.md` §5: the
same junk-value reason as `IsPeriodicDatum`; it also makes `IsMeanZeroT` an
honest Haar-integral statement), zero mean, then
`∀ i : Fin 3, ∀ k : PeriodicFrequency`.  The zero-frequency equation forces
`A_i(0)=0`, as the manuscript's homogeneous convention requires. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Ḣ^s(T³)` extended norm of a mean-zero physical field.  It is the infimum over
homogeneous real data and is `⊤` when no datum exists. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

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

end BlowupDensity.T10.Draft
/- end copied T10 declarations -/

/- copied from research/T14/Spec.lean:39-108,120-132 (selected declarations);
delete once T14 is registered -/
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
/- end copied T14 declarations -/

/- copied from research/T13/Spec.lean:157-312; namespace spelling follows the
T15 lane brief (`T13.Draft`); delete once T13 is registered -/
namespace BlowupDensity.T13.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Fixed chart, support, and periodization -/

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

end BlowupDensity.T13.Draft
/- end copied T13 declarations -/

namespace BlowupDensity.T15.DraftB

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open BlowupDensity.T14.Draft
open BlowupDensity.T13.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## 1. Explicit placement, rescaling, and lattice periodization -/

/-- `03-torus.tex:106`: the shifted packet time `t_ε = T - ε²`. -/
def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

/-- `03-torus.tex:112-114`, the velocity
`U_ε(x,t)=ε⁻¹U((x-x₀)/ε,(t-t_ε)/ε²)`, with time first in
`SpaceTime` and with T14's smooth negative-time zero extension.  The inverse
powers are literal `Real.rpow`-free field powers, matching `I03.scaling`'s
`scaledPacket`. -/
def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.velocity
    ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:115-116`, the pressure
`P_ε(x,t)=ε⁻²P((x-x₀)/ε,(t-t_ε)/ε²)`, using T14's smooth
negative-time zero extension.  This is the torus draft's explicit counterpart
of `I03.scaling`'s `scaledPressure`. -/
def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 * zeroPastField P.pressure
    ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:117-118`, the force
`F_ε(x,t)=ε⁻³F((x-x₀)/ε,(t-t_ε)/ε²)`.  `PacketAPI.force` is
already the globally smooth zero extension, so no `zeroPastField` wrapper is
inserted.  This is the explicit counterpart of `I03.scaling`'s `scaledForce`. -/
def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.force
    ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:120`: the unit-lattice sum of the placed whole-space
velocity.  The summability and single-copy clauses in `ScalingAPI` rule out the
totalized-`tsum` junk value and identify this sum with its zero-lattice summand
on the fundamental cube. -/
def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledVelocity P x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: the unit-lattice sum of the placed whole-space
pressure before choosing its mean-zero representative. -/
def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure P x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: the unit-lattice sum of the placed whole-space force. -/
def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeField :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledForce P x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:123`: the pressure representative obtained by subtracting,
at each time, the normalized Haar mean of the raw periodization. -/
def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space)
    (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

/-- `03-torus.tex:131`: `α(p,q)=-3+3/p+2/q`, with `ENNReal.toReal ⊤=0`
implementing the zero reciprocal at either essential-supremum endpoint.  This
is the same formula as `Contracts.V1.alpha` in `I03.scaling`. -/
def scalingExponent (p q : ℝ≥0∞) : ℝ :=
  -3 + 3 / p.toReal + 2 / q.toReal

/-! ## 2. Honest mixed and Sobolev path membership -/

/-- `03-torus.tex:129-132`: `G` is the torus `L^p`-slice path of the periodic
physical field `f`.  This is the torus analogue of
`Contracts.V1.Data.IsLebesgueSlicePath`, with equality almost everywhere for
normalized Haar measure. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField)
    (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-132`: the torus mixed norm
`‖f‖_{L^q(0,∞;L^p(T³))}`, in exactly the measurable-`Lp`-path spelling of
`Contracts.V1.Data.mixedLebesgueENorm`.  It is `⊤` if no measurable path
represents the physical field. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- Concrete membership in the whole-space mixed Bochner class used on the
right side of `eq:packetFscale`, `03-torus.tex:129-132`.  Requiring a `MemLp`
representing path makes both strong measurability and finiteness explicit. -/
def MemMixedLebesgueR (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p (volume : Measure Space),
    IsLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- Concrete membership in the periodic mixed Bochner class used on the left
side of `eq:packetFscale`, `03-torus.tex:129-132`.  It excludes an equality
whose two sides are merely `⊤`. -/
def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- Honest membership in T10's periodic Sobolev Bochner class,
`03-torus.tex:134-138`: a representing Fourier-data path is exhibited and is
`MemLp`, rather than merely strongly measurable. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- Integrability attached to the two energy identities of
`eq:packetEscale`, `03-torus.tex:125-128`.  Every velocity and full-gradient
slice is an honest Haar `L²` function.  The time finiteness is then fixed by the
two finite equalities in `ScalingAPI`. -/
def EnergySlicesMemLpT (T : ℝ) (u : SpaceTimeField) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ u (t, x))) 2 periodicTorusMeasure) ∧
    ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ spatialGradient u t x)) 2 periodicTorusMeasure

/-! ## 3. Scaling API -/

/-- Proposition 3.3, `prop:scaling`, for one T14 packet and one sufficiently
small common scale family.  This is deliberately `Type`-valued: the fixed
geometry, `ε₀`, and the function `s ↦ C_s` are data selected before any scale
`ε`, matching the house style of the Section 4 quantitative APIs.

The solution field uses `ClassicalSolutionT` rather than only a pointwise PDE:
it packages the same-viscosity equation, incompressibility, zero initial data,
periodicity, regularity, and the pressure gauge in the exact shape consumed by
T18.  The raw placement and the normalized pressure remain explicit defs above.
-/
structure ScalingAPI (ν : ℝ) (P : PacketImportAPI ν) where
  /-- `03-torus.tex:22-98,150-158`: the already reconciled localization API.
  In particular, `localization.localization` is the uniform interior-ball
  estimate used for `eq:packetHs`; this record does not restate or re-prove it.

  Exact quantifier order: the T13 witness is selected before every geometric
  datum and scale in this T15 record.
  Non-vacuity: this is the concrete six-field T13 API, not an arbitrary
  proposition parameter. -/
  localization : LocalizationAPI

  /-- `03-torus.tex:101-102`: the compact set `K_*` containing both the packet
  carrier and the spatial projection of `supp F`.

  Exact quantifier order: this set is selected before its compactness and the
  two inclusions below, and before every scale.
  Non-vacuity: the two inclusion fields below tie this set to the fixed packet. -/
  supportCarrier : Set Space

  /-- `03-torus.tex:101`: `K_*` is compact.

  Exact quantifier order: compactness constrains the already selected
  `supportCarrier`.
  Non-vacuity: together with the support inclusions, this is the actual compact
  carrier used to choose a single uniform support radius. -/
  supportCarrier_compact : IsCompact supportCarrier

  /-- `03-torus.tex:101`: the packet velocity/pressure carrier `K` lies in
  `K_*`.

  Exact quantifier order: the fixed packet `P` precedes the selected
  `supportCarrier` and this inclusion.
  Non-vacuity: this is inclusion of the concrete `P.carrier`. -/
  packetCarrier_subset : P.carrier ⊆ supportCarrier

  /-- `03-torus.tex:101-102`: the spatial projection of the topological support
  of the packet force lies in `K_*`.  Exact quantifier order: first the
  spacetime support point `z`, then membership.

  Non-vacuity: the premise names `tsupport P.force`, not an unrelated support
  witness. -/
  forceProjection_subset : ∀ z ∈ tsupport P.force, z.2 ∈ supportCarrier

  /-- `03-torus.tex:101-105`: a positive radius `R_*` controlling `K_*` around
  the origin before placement.

  Exact quantifier order: `R_*` is selected after `K_*` and before every `ε`.
  Non-vacuity: `supportRadius_subset` uses this same radius. -/
  supportRadius : ℝ

  /-- `03-torus.tex:101-105`: `R_*>0`.

  Exact quantifier order: positivity constrains the already selected radius.
  Non-vacuity: it excludes the empty/zero-radius support bound. -/
  supportRadius_pos : 0 < supportRadius

  /-- `03-torus.tex:101-105`: `K_* ⊆ B(0,R_*)`.

  Exact quantifier order: the selected set and radius precede this inclusion.
  Non-vacuity: the set is the packet-tied `supportCarrier`, so this cannot be
  discharged by choosing an unrelated bounded set. -/
  supportRadius_subset : supportCarrier ⊆ Metric.ball (0 : Space) supportRadius

  /-- `03-torus.tex:102-105`: the placement point `x₀`, chosen as the center
  of a smaller localization ball inside the fixed coordinate cube.

  Exact quantifier order: `x₀` is selected before the chart radius and `ε`.
  Non-vacuity: `chartBall_subset` ties it to a genuine interior coordinate
  ball and all explicit scaled fields use this same point. -/
  x₀ : Space

  /-- `03-torus.tex:102-105`: radius of the fixed localization ball centered at
  `x₀`; it is selected before `ε`.

  Exact quantifier order: the center precedes this radius, which precedes `ε`.
  Non-vacuity: the next two fields force it positive and geometrically inside
  the fundamental cube. -/
  chartRadius : ℝ

  /-- `03-torus.tex:102-105`: the chart ball has positive radius.

  Exact quantifier order: positivity constrains the already selected radius.
  Non-vacuity: it excludes a degenerate localization ball. -/
  chartRadius_pos : 0 < chartRadius

  /-- `03-torus.tex:102-105` with `lem:localization`: the closed chart ball is
  contained in the interior of the fixed fundamental cube.

  Exact quantifier order: `x₀` and `chartRadius` are fixed before this inclusion
  and before every scale.
  Non-vacuity: this is the precise hypothesis accepted by
  `LocalizationAPI.localization`, `endpoint_zero`, and `endpoint_one`. -/
  chartBall_subset :
    closure (Metric.ball x₀ chartRadius) ⊆ interior fundamentalCube

  /-- `03-torus.tex:103-106`: the prescribed singular time `T`.

  Exact quantifier order: `T` is fixed before `ε₀` and every scale.
  Non-vacuity: `time_pos`, `eps_time`, the solution horizon, and the blow-up
  predicate all constrain this same time. -/
  T : ℝ

  /-- `03-torus.tex:103-106`: `T>0`; the stronger scale-dependent inequality
  is `eps_time` below.

  Exact quantifier order: positivity constrains the already fixed `T`.
  Non-vacuity: it makes `(0,T)` a genuine solution interval. -/
  time_pos : 0 < T

  /-- `03-torus.tex:103`: one positive threshold for every sufficiently small
  scale in this same family.

  Exact quantifier order: `ε₀` is selected before all universally quantified
  scales.
  Non-vacuity: `eps_pos` makes its admissible interval nonempty. -/
  ε₀ : ℝ

  /-- `03-torus.tex:103`: `ε₀>0`.

  Exact quantifier order: positivity constrains the already selected threshold.
  Non-vacuity: it prevents all scale-indexed conclusions from being vacuous. -/
  eps_pos : 0 < ε₀

  /-- `03-torus.tex:103,150-158`: harmless normalization `ε₀≤1`, used by the
  uniform endpoint estimates feeding `eq:packetHs`.

  Exact quantifier order: this constrains the common threshold before `ε`.
  Non-vacuity: it is a real restriction on the same positive threshold, not a
  separately chosen endpoint-bound scale. -/
  eps_le_one : ε₀ ≤ 1

  /-- `03-torus.tex:104-106`: exact quantifier order
  `∀ ε ∈ (0,ε₀]`, then `2ε²<T`.  It implies `t_ε>0`, so the full
  source-time support is seen by the positive-time norms.

  Non-vacuity: `eps_pos` makes the quantified scale interval nonempty. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T

  /-- `03-torus.tex:104-105,120`: the support-radius smallness
  `ε R_* < r`.  Together with `supportRadius_subset` and `chartBall_subset`,
  this gives `x₀+εK_*⊆B(x₀,r)` and is exactly the hypothesis making the
  lattice sum a single copy in one period cell.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`, after all geometry is fixed.
  Non-vacuity: every symbol is fixed data of this same record and the scale
  interval is nonempty. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * supportRadius < chartRadius

  /-- `03-torus.tex:120`: the velocity lattice series is summable at every
  presingular spacetime point and every admissible scale.

  Exact quantifier order: `∀ ε`, scale membership, `∀ t<T`, `∀ x`.
  Non-vacuity: this prevents `tsum` totalization from silently returning zero. -/
  velocityPeriodization_summable : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, t < T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledVelocity P x₀ T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: the pressure lattice series is summable on the same
  presingular slab.

  Exact quantifier order matches `velocityPeriodization_summable`.
  Non-vacuity: this validates the raw periodized pressure before normalization. -/
  pressurePeriodization_summable : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, t < T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledPressure P x₀ T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: the force lattice series is summable for all real
  times, because the force is the global smooth zero extension.

  Exact quantifier order: `∀ ε`, scale membership, `∀ t`, `∀ x`.
  Non-vacuity: this validates the periodized force on the entire time axis used
  by `(0,∞)` norms. -/
  forcePeriodization_summable : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledForce P x₀ T ε (t, x - latticeVector n))

  /-- `03-torus.tex:120`: on the fixed cube the velocity periodization equals
  the single zero-lattice copy.

  Exact quantifier order: `∀ ε`, admissibility, `∀ t<T`, `∀ x∈Q`.
  Non-vacuity: the conclusion is pointwise equality of the explicit fields;
  it is the concrete consequence of `eps_space`, not a support slogan. -/
  velocity_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, t < T → ∀ x ∈ fundamentalCube,
      periodizedScaledVelocity P x₀ T ε (t, x) = scaledVelocity P x₀ T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed cube the raw pressure periodization
  equals the single zero-lattice copy.

  Exact quantifier order matches `velocity_singleCopy`.
  Non-vacuity: the equality concerns the explicit raw pressure before its
  spatially constant gauge adjustment. -/
  pressure_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, t < T → ∀ x ∈ fundamentalCube,
      periodizedScaledPressure P x₀ T ε (t, x) = scaledPressure P x₀ T ε (t, x)

  /-- `03-torus.tex:120`: on the fixed cube the force periodization equals the
  single zero-lattice copy at every time.

  Exact quantifier order: `∀ ε`, admissibility, `∀ t`, `∀ x∈Q`.
  Non-vacuity: this is the equality that transfers whole-space mixed norms to
  their torus counterparts. -/
  force_singleCopy : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, ∀ x ∈ fundamentalCube,
      periodizedScaledForce P x₀ T ε (t, x) = scaledForce P x₀ T ε (t, x)

  /-- `03-torus.tex:108-120,123`: every periodized rescaled force is a smooth,
  unit-periodic field with compact time support contained in `(0,∞)`, i.e. it
  belongs to T10's manuscript force class.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: `MemForceT` expands to concrete smoothness, periodicity, and one
  compact positive-time support witness for the explicit force; it is also the
  input-class fact T18 needs after insertion. -/
  periodizedForce_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    MemForceT (periodizedScaledForce P x₀ T ε)

  /-- `03-torus.tex:122-123,141`: for every admissible scale, the periodized
  fields solve Navier–Stokes at the unchanged viscosity `ν` on `[0,T)`, are
  divergence free and periodic, and start from zero.  The pressure is the
  explicit `normalizedScaledPressure`, so the `ClassicalSolutionT` witness also
  records its zero-mean gauge.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`, followed by a full solution whose
  initial datum is the literal zero field.

  Non-vacuity: both carried fields are equated to the explicit rescale-and-sum
  definitions, and `ClassicalSolutionT.momentum` is the concrete pointwise PDE,
  not an unspecified solution predicate. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ S : ClassicalSolutionT ν (0 : SpatialField)
        (periodizedScaledForce P x₀ T ε) T,
      S.velocity = periodizedScaledVelocity P x₀ T ε ∧
        S.pressure = normalizedScaledPressure P x₀ T ε

  /-- `03-torus.tex:123`: the raw pressure slices are integrable before their
  spatial mean is subtracted.

  Exact quantifier order: `∀ ε`, admissibility, `∀ t∈[0,T)`.
  Non-vacuity: this rules out the Bochner integral's nonintegrable junk value in
  `pressureMeanT`. -/
  pressureSlice_integrable : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T,
      Integrable
        (torusLift (fun x ↦ periodizedScaledPressure P x₀ T ε (t, x)))
        periodicTorusMeasure

  /-- `03-torus.tex:123`: the pressure adjustment is spatially constant and
  enforces `∫_T³ p_ε(t)=0`.  The displayed pointwise equality makes the
  adjustment explicit; the second conjunct is T10's gauge predicate.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`, then the pointwise formula at
  every `t∈[0,T)` and `x`, together with one gauge assertion on `[0,T)`.

  Non-vacuity: the subtracted constant is the concrete Haar integral
  `pressureMeanT` of the raw periodization, whose honesty is supplied by
  `pressureSlice_integrable`. -/
  pressureNormalization : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      normalizedScaledPressure P x₀ T ε (t, x) =
        periodizedScaledPressure P x₀ T ε (t, x) -
          pressureMeanT (periodizedScaledPressure P x₀ T ε) t) ∧
      PressureGaugeT (Ico (0 : ℝ) T) (normalizedScaledPressure P x₀ T ε)

  /-- `03-torus.tex:123,142-143`: the periodized velocity has unbounded speed
  in every left neighborhood of `T`.  This is exactly the Section 4
  `I03.scaling` predicate: `∀ K>0, ∀ δ>0, ∃ t,x` with
  `t∈(0,T)`, `T-δ<t`, and `K<‖U_ε(t,x)‖`.

  Exact quantifier order: scale first, then the displayed predicate's
  `K`, positivity, `δ`, positivity, `t`, and `x`.

  Non-vacuity: this constrains the explicit periodized velocity and approaches
  the actual time `T`; it is stronger than mere unboundedness somewhere in
  `(0,T)`. -/
  unboundedSpeed : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SpeedUnboundedAt T (periodizedScaledVelocity P x₀ T ε)

  /-- `03-torus.tex:125-128`: honest spatial `L²` membership for the velocity
  and gradient slices appearing in both identities of `eq:packetEscale`.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: the predicate contains two concrete `MemLp` families for the
  explicit periodized velocity. -/
  energySlices_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    EnergySlicesMemLpT T (periodizedScaledVelocity P x₀ T ε)

  /-- `03-torus.tex:125-126`, first equality of `eq:packetEscale`:
  `‖U_ε‖_{L∞(0,T;L²(T³))}=ε^{1/2}M`, using T10's physical
  `energyEssSupT` and T14's inherited `M=P.energyBound`.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: this is an equality in `ℝ≥0∞`; `energySlices_memLp` supplies
  honest slices, and the finite right side rules out an infinite time norm. -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyEssSupT T (periodizedScaledVelocity P x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound)

  /-- `03-torus.tex:127-128`, second equality of `eq:packetEscale`:
  `‖∇U_ε‖_{L²(0,T;L²(T³))}=ε^{1/2}D`, using T10's
  `energyGradientT` and T14's inherited `D=P.dissipationBound`.

  Exact quantifier order: `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: this is a second independent equality, not the sum `E_T`;
  `energySlices_memLp` makes every spatial norm honest. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyGradientT T (periodizedScaledVelocity P x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound)

  /-- `03-torus.tex:129-132`: both fields in `eq:packetFscale` have honest
  mixed Bochner representatives for every `1≤p,q≤∞` and every admissible
  scale.  The source uses Section 4's `Data.IsLebesgueSlicePath`; the torus side
  uses `IsPeriodicLebesgueSlicePath` above.

  Exact quantifier order: `∀ p q`, the typeclass `1≤p`, the proof `1≤q`,
  then `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: `MemLp`, rather than mere measurability, excludes `⊤=⊤`. -/
  mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    MemMixedLebesgueR q p P.force ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        MemMixedLebesgueT q p (periodizedScaledForce P x₀ T ε)

  /-- `03-torus.tex:129-132`, equation `eq:packetFscale`:
  `‖F_ε‖_{L^q(0,∞;L^p(T³))}=ε^{α(p,q)}‖F‖_{L^q(0,∞;L^p(R³))}`
  for every `1≤p,q≤∞`.  The left norm is the T10-style torus norm
  `mixedLebesgueENormT`; the right norm is Section 4's registered
  `Data.mixedLebesgueENorm`; `scalingExponent` is the explicit `α(p,q)`.

  Exact quantifier order: `∀ p q`, `1≤p` as a `Fact`, `1≤q`, then
  `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: `mixed_memLp` provides finite representing paths on both sides,
  including the essential-supremum endpoints. -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      mixedLebesgueENormT q p (periodizedScaledForce P x₀ T ε) =
        ENNReal.ofReal (ε ^ scalingExponent p q) * mixedLebesgueENorm q p P.force

  /-- `03-torus.tex:134-136`: the constants `C_s` are data selected before
  every scale `ε`, as the paper's notation requires.  This field is why the API
  is Type-valued rather than a Prop-valued structure with a separately nested
  existential.

  Exact quantifier order: the full function `s ↦ C_s` is selected before the
  universal `s` and `ε` in the following fields.
  Non-vacuity: `sobolevConst_nonneg` and `packetSobolevBound` constrain this
  concrete function on the full interval `[0,1]`. -/
  sobolevConst : ℝ → ℝ

  /-- `03-torus.tex:134-136`: `C_s≥0` for every `0≤s≤1`.

  Exact quantifier order: `∀ s`, followed by the two endpoint inequalities.
  Non-vacuity: a negative constant could make the ENNReal upper bound collapse
  to zero, so its sign is recorded explicitly. -/
  sobolevConst_nonneg : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ sobolevConst s

  /-- `03-torus.tex:134-158`: the periodized force has an honest
  `L¹(0,∞;H^s(T³))` Fourier-data path for every `0≤s≤1` and admissible
  scale.

  Exact quantifier order: `∀ s`, its range proofs, then `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: the exhibited `MemLp` path uses T10's amended
  `IsPeriodicDatum`, including its Haar-integrability conjunct. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (periodizedScaledForce P x₀ T ε)

  /-- `03-torus.tex:134-158`, equation `eq:packetHs`:
  `‖F_ε‖_{L¹(0,∞;H^s(T³))}≤C_s(ε^{1/2}+ε^{1/2-s})`
  for `0≤s≤1`.  For `0<s<1` this is the direct consumer of
  `localization.localization`; the endpoint cases use
  `localization.endpoint_zero` and `localization.endpoint_one`.

  Exact quantifier order fixes `s` and `C_s` before `ε`:
  `∀ s`, range proofs, then `∀ ε ∈ (0,ε₀]`.
  Non-vacuity: `forceSobolev_memLp` supplies a finite Bochner path, and
  `sobolevConst_nonneg` makes the displayed finite upper bound meaningful. -/
  packetSobolevBound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce P x₀ T ε) ≤
        ENNReal.ofReal (sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)))

/-! ## 4. Existential and derived statement forms -/

/-- The proposition-level T15 goal for a selected T14 packet family and a
selected T13 localization witness, `03-torus.tex:101-159`.  The equality pins
the inhabitant to the caller's localization API; introducing this definition
asserts no inhabitant. -/
def scalingStatement : Prop :=
  ∀ (𝔉 : PacketImportFamily) (L : LocalizationAPI) (ν : ℝ) (hν : 0 < ν),
    ∃ A : ScalingAPI ν (𝔉.select ν hν), A.localization = L

/-- Derived, not assumed: the "In particular" clause of `prop:scaling`,
`03-torus.tex:138,158`.  It includes every negative order as well as
`0≤s<1/2`, and uses the right-neighborhood filter `ε↓0+`.  This concrete
proposition is intentionally not a field of `ScalingAPI`: it is to be proved
from `packetSobolevBound`, T10's monotonicity from `H⁰` to negative orders, and
the scalar real-power limit (candidate
`Paper1.ScalingLimits.sobolev_error_tendsto_zero` supplies the proof pattern,
but its first exponent is the later insertion rate and needs a T15 companion). -/
def SubcriticalForceConvergence {ν : ℝ} {P : PacketImportAPI ν}
    (A : ScalingAPI ν P) : Prop :=
  ∀ s : ℝ, s < (1 : ℝ) / 2 →
    Tendsto (fun ε : ℝ ↦
      forceSobolevENormT 1 s (periodizedScaledForce P A.x₀ A.T ε))
      (nhdsWithin 0 (Ioi 0)) (nhds 0)

end BlowupDensity.T15.DraftB
