import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.MaximalPartial
import Contracts.V1.InsertionFamily
import Contracts.V1.Correction
import Contracts.V1.Scaling
import Contracts.V1.HomogeneousNorm
import Contracts.V2.InsertionLifespan
import Contracts.V1.Data

-- copied verbatim from research/T18/Spec.lean blocks: 52-201, 290-820,
-- 821-1264, 1265-1603, and 1604-1989 (the registered T14 packet-import
-- contract is imported above rather than copied).

/-!
# T18 reconciled specification: exact local insertion on `T³` (`thm:insertion`)

Statement-only reconciled spec of Theorem `thm:insertion`,
`paper/sections/03-torus.tex:287-346` (proof `:312-346`).  No proofs; one
`Type`-valued structure `PeriodicInsertionAPI` whose fields are the clauses of
the theorem, plus `periodicInsertionStatement : Prop` in the paper's quantifier
order.

This finalizes the two blind drafts (lane 356 draft A / lane 357 draft B) per
`research/T18/RECONCILIATION.md`.  Base is draft B (field layout, names, order,
`periodicSet` support, `blowup_limsup`, explicit kinematic clauses, `ε₀`-as-field
and inline-`reference` binding); four structural corrections are imported from
draft A: the packet/scaling threading (`P : PacketImportAPI`, `place`,
`scaling : ScalingAPI P place`), the `MemMixedLebesgueT` mixed-norm honesty
guard, and the `negative_s_memLp` guard on the `s<0` tail.

The unregistered T13/T14/T15/T16/T17 vocabulary the statement is written in is
copied verbatim below in its historical namespaces, delimited with provenance
headers (identical to draft A's copied blocks, minus draft A's T12 block, which
the reconciliation drops).  Everything registered
(`ClassicalSolutionT`, `forceClassT`, `initialClassT`, `maximalLifespanT`,
`IsMaximalPeriodicSolution`, `normalizePressureT`, `energyENormT`,
`forceSobolevENormT`, `SpeedUnboundedAt`, `navierStokesResidual`,
`BlowupDensity.Contracts.V1.alpha`, `MaximalPartial.{limsupLeft,speedENorm}`)
is imported and used by name, never copied; the copied `T15.Draft` block carries
the `example … := rfl` drift checks against the registered `scaledPacket` /
`scaledPressure` / `scaledForce` / `alpha` spellings.
-/

noncomputable section

open BlowupDensity.Contracts.V1.TorusLocalTheory

/- Compatibility namespace retained because the verbatim upstream blocks open
   it; all T10 declarations themselves come from the registered contracts. -/
namespace BlowupDensity.T10.Draft
end BlowupDensity.T10.Draft

/- copied verbatim from research/T13/Spec.lean:168-205,213-312;
   dependencies now resolve through registered Contracts.V1.TorusData -/
-- copied verbatim from research/T18/Spec.lean:52-201
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
-- copied verbatim from research/T18/Spec.lean:290-820
namespace BlowupDensity.T15.Draft

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
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
-- copied verbatim from research/T18/Spec.lean:821-1264
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
-- copied verbatim from research/T18/Spec.lean:1265-1603
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

/-!
## Drift checks against registered spellings

The copied `T15.Draft` block already pins `scaledPacket`/`scaledPressure`/
`scaledForce` to the registered `Contracts.V1` names.  The reconciled statement
below writes `α(p,q)` through the registered `Contracts.V1.alpha`; the copied
`alphaT` (used inside the `CorrectionAPI` block) is definitionally equal to it.
-/


-- copied verbatim from research/T18/Spec.lean:1604-1989
namespace BlowupDensity.T18.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T15.Draft
open BlowupDensity.T16.Draft
open BlowupDensity.T17.Spec
open scoped ContDiff ENNReal BigOperators Topology

/-- Drift check `03-torus.tex:130-131`: the copied `T15.Draft` exponent is
definitionally the registered `Contracts.V1.alpha` the statement is written in;
`check rfl`. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.T15.Draft.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-- Drift check `03-torus.tex:129-133`: the `MemMixedLebesgueT`-guarded
`mixedLebesgueENormT` (from `T15.Draft`) is definitionally the `T15.Spec` mixed
norm the copied `CorrectionAPI` block is written in; `check rfl`. -/
example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    BlowupDensity.T15.Draft.mixedLebesgueENormT q p f
      = BlowupDensity.T15.Spec.mixedLebesgueENormT q p f := rfl

/-- **Theorem `thm:insertion` (exact local insertion on `T³`),
`paper/sections/03-torus.tex:287-311`, proof `:312-346`, for one `ε`-family.**

Parameters (the objects the proof is *given*, none of them an inhabited
registered contract, `:287-289,312-314`): the viscosity `ν`; the fixed
energy-enhanced whole-space packet `P` (`prop:scaling` rescales it, and `M,D`
are its `energyBound`/`dissipationBound`); the placement `place` of
`lem:localization`/`prop:scaling`; the torus scaling record `scaling`
(`prop:scaling`, threaded because the torus T15 chain is not yet a registered
contract — it delivers the periodized packet and its energy/mixed/Sobolev
scaling identities); the initial velocity `a` and reference force `g`; the
coordinate-ball radius `r` and regularity margin `δ`; the cutoff data `D` of
`lem:potential`; the reference solution `reference` regular through `place.T+δ`;
and the `lem:correction` record `correction` (`w_ε`, `H_ε`, and every bound of
`eq:wE`, `eq:Hmixed`, `eq:HHs`).  T11 local theory / continuation and the T12
calculus are **not** threaded: the lifespan argument consumes the registered,
inhabited `torusLocalTheoryAPI` / `torusContinuationH3API`, and `H²↪L∞` is a
Mathlib fact.  This mirrors R42's `InsertionFamilyAPI (ν) (P)`
(`Contracts/V1/InsertionFamily.lean`) whose one `scaling` field bundles the
ambient data; here that bundle is split across `place`, `scaling` and
`correction`.

Fields are the clauses of the theorem plus the paper hypotheses not forced by
the parameter types; every scale-dependent field is guarded by `ε ∈ Ioc 0 ε₀`,
and every totalized Bochner norm carries the integrability/class guard
(`MemMixedLebesgueT` / `MemForceSobolevT`) that makes it honest.  Differences
from the `R42`/`R42.v2` template are marked `TORUS:` and tabulated in
`research/T18/COMPARISON.md`. -/
structure PeriodicInsertionAPI (ν : ℝ) (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction :
      BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D) :
    Type where
  -- ### Paper hypotheses not already forced by the parameter types
  /-- `03-torus.tex:288`: `δ > 0`, so the reference is regular strictly past `T`.
  Quantifier order: none.  Non-vacuity: a strict inequality on the real margin
  used in `reference`'s horizon `place.T + δ`. -/
  delta_pos : 0 < δ
  /-- `03-torus.tex:289`: `g ∈ 𝓕`, the reference force is a torus force.
  Quantifier order: none.  Non-vacuity: `forceClassT` membership is the smooth
  compact-in-`(0,∞)` class, not a trivial set. -/
  reference_force_mem : g ∈ forceClassT
  /-- `03-torus.tex:289`: `v(0)=a ∈ 𝓧`, the initial velocity is a smooth
  divergence-free torus field.  Quantifier order: none.  Non-vacuity:
  `initialClassT` fixes smoothness, periodicity and solenoidality. -/
  initial_mem : a ∈ initialClassT

  -- ### The single scale threshold `03-torus.tex:290` "For all sufficiently small ε>0"
  /-- `03-torus.tex:290`: the family threshold `ε₀`.
  Non-vacuity: real data used by every clause below through `Ioc 0 ε₀`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:290`: `ε₀ > 0`.  Non-vacuity: `(0,ε₀]` is nonempty. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:290,103`: the inserted family shrinks the scaling threshold,
  so every `prop:scaling` bound (quantified over `Ioc 0 place.ε₀`) holds on
  `(0,ε₀]`.  Quantifier order: none.  Non-vacuity: a genuine `≤` between the two
  thresholds. -/
  eps_le_scaling : ε₀ ≤ place.ε₀
  /-- `03-torus.tex:290,312`: the inserted family is also a sub-family of the
  correction family, so every `lem:correction` bound holds on `(0,ε₀]`.
  Quantifier order: none.  Non-vacuity: a genuine `≤` between the two
  thresholds. -/
  eps_le_cutoff : ε₀ ≤ D.ε₀

  -- ### The inserted triple and the three displays `eq:insertion` `03-torus.tex:314`
  /-- `03-torus.tex:314`: `ε ↦ u_ε`, the inserted velocity. -/
  velocity : ℝ → VelocityField
  /-- `03-torus.tex:314,318-320`: `ε ↦ p_ε`, the inserted pressure. -/
  pressure : ℝ → SpaceTimeScalar
  /-- `03-torus.tex:314`: `ε ↦ g_ε`, the inserted force. -/
  force : ℝ → VelocityField
  /-- `03-torus.tex:314` `eq:insertion`, first display: `u_ε = v + w_ε + U_ε`,
  with `v = reference.velocity`, `w_ε = D.correction ε` (`lem:potential`), and
  `U_ε = periodizedScaledVelocity P x₀ T ε` the periodized rescaled packet
  (`prop:scaling`).  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise
  field equation fixing `velocity` on all spacetime, not an existential shadow. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = reference.velocity z + D.correction ε z +
      periodizedScaledVelocity P place.x₀ place.T ε z
  /-- `03-torus.tex:314,318-320` `eq:insertion`, second display: `p_ε = π + P_ε`
  normalized by subtracting its torus mean ("subtract its spatial mean to
  normalize `p_ε`", `:318-320`), where `π = reference.pressure` and
  `P_ε = periodizedScaledPressure P x₀ T ε` is the scaling record's periodized
  raw packet pressure.  TORUS: the `∫_{T³}p=0` gauge (`normalizePressureT`) is
  imposed; the `R42` twin keeps the compact gauge `π + P_ε`
  (`InsertionFamily.lean:183`).  Because `reference` carries `pressure_gauge`
  (`π` mean-zero), `normalize(π + P_ε) = π + normalize(P_ε)`.
  Quantifier order: `∀ ε`.  Non-vacuity: fixes `pressure ε` as a concrete
  normalized field. -/
  pressure_formula : ∀ ε : ℝ,
    pressure ε = normalizePressureT
      (fun z => reference.pressure z +
        periodizedScaledPressure P place.x₀ place.T ε z)
  /-- `03-torus.tex:314` `eq:insertion`, third display: `g_ε = g + H_ε + F_ε`,
  with `H_ε = correctionForce ν v D ε` (`lem:correction`, `eq:H`) and
  `F_ε = periodizedScaledForce P x₀ T ε` the periodized rescaled packet force
  (`prop:scaling`).  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise
  field equation. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ν reference.velocity D ε z +
      periodizedScaledForce P place.x₀ place.T ε z

  -- ### Class memberships `03-torus.tex:289,338-341`
  /-- `03-torus.tex:289,338-341`: `g_ε ∈ 𝓕`.  "Their time supports remain
  compact subsets of `(0,∞)` … Therefore `g_ε ∈ 𝓕`."
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: membership in the smooth
  compact torus force class for the actual inserted force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, force ε ∈ forceClassT
  /-- `03-torus.tex:338-341`: the force perturbation `g_ε - g = H_ε + F_ε` is
  itself a torus force (compact time support in `(0,∞)`, smooth across `T`).
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `forceClassT` membership of
  the actual difference field. -/
  forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (fun z => force ε z - g z) ∈ forceClassT

  -- ### A classical torus trajectory on `[0,T)` `03-torus.tex:329-345`
  /-- `03-torus.tex:337`: `u_ε` is smooth on `[0,T) × R³`, one-sided at `t = 0`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `ContDiffOn` on the
  closed-at-zero, open-at-`T` slab of the actual `velocity ε`. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (velocity ε) (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))
  /-- `03-torus.tex:337`: `p_ε` is smooth on `[0,T) × R³`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `ContDiffOn` of the actual
  `pressure ε`. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (pressure ε) (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))
  /-- `03-torus.tex:333-334`: `u_ε(·,0) = a`, "the initial datum … [is]
  unchanged".  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ x`.  Non-vacuity: pointwise
  equality of physical vectors. -/
  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x : Space, velocity ε (0, x) = a x
  /-- `03-torus.tex:332-334`: `div u_ε = 0` on `[0,T)`, including `t = 0`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the
  registered physical divergence vanishes pointwise. -/
  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (velocity ε) t x = 0
  /-- `03-torus.tex:329-331`: the momentum equation `eq:NS` holds exactly for
  `(u_ε, p_ε, g_ε)` at interior times, "the equation is exact on `[0,T)`".
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ioo 0 T, ∀ x`.  Non-vacuity: the NS
  residual equals the inserted force pointwise, at the reference's own `ν`. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)
  /-- `03-torus.tex:294` clause (ii): `u_ε = v` for `0 ≤ t ≤ T - 2ε²`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t, 0 ≤ t, t ≤ T - 2ε², ∀ x`.
  Non-vacuity: pointwise equality on the entire quiet initial slab. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = reference.velocity (t, x)
  /-- `03-torus.tex:2-4,337`: `u_ε` has unit spatial periods on `[0,T)`.
  Quantifier order: that of `IsPeriodicOn`.  Non-vacuity: the actual periodicity
  used for the torus solution and its lifted norms. -/
  velocity_periodic : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsPeriodicOn (Ico (0 : ℝ) place.T) (velocity ε)

  -- ### The bundled classical solution, maximal identification and lifespan `03-torus.tex:338-345`
  /-- `03-torus.tex:338,344-345`: for each `ε` the inserted pair `(u_ε, p_ε)` is
  a torus classical solution on the full horizon `[0,T)` (carrying `sobolev`,
  the pressure gauge, and `∇p_ε ∈ L²`).  Mirrors `InsertionLifespanV2API.solution`
  (`Contracts/V2/InsertionLifespan.lean`).  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`,
  then `∃ w`.  Non-vacuity: the witness is a full `ClassicalSolutionT` with
  velocity and pressure equal to the inserted fields. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionT ν a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε
  /-- `03-torus.tex:342-344`: "Uniqueness in Proposition `prop:local` identifies
  the constructed velocity with the maximal solution."  The inserted pair *is*
  the maximal periodic solution of `(ν, a, g_ε)`, in the registered
  `IsMaximalPeriodicSolution` vocabulary.  TORUS: uses `TorusLocalTheory`'s
  torus maximal-solution predicate, not `R³`'s `IsMaximalSolution`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the actual inserted fields
  are the maximal solution, not merely one solution. -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalPeriodicSolution ν a (force ε) (velocity ε) (pressure ε)
  /-- `03-torus.tex:291,344-345` clause (i): `T_max^ν(a, g_ε) = T`, "its lifespan
  is exactly `T`".  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an
  equality in `ℝ≥0∞` of the registered maximal lifespan with `ofReal T`, not a
  one-sided bound. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanT ν a (force ε) = ENNReal.ofReal place.T
  /-- `03-torus.tex:291-292` clause (i): `limsup_{t↑T} ‖u_ε(t)‖_∞ = ∞`, in the
  pointwise `SpeedUnboundedAt` form the packet/rescaling produce.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: at every level `M` and every
  left neighbourhood of `T`, a presingular time and point exceed `M`. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε)
  /-- `03-torus.tex:291-292` clause (i): the essential-supremum form of the same
  display, `limsup_{t↑T} ‖u_ε(t)‖_{L^∞} = ⊤`, in the frozen
  `Contracts.V1.MaximalPartial` vocabulary (`limsupLeft`/`speedENorm`).  Mirrors
  `InsertionLifespanV2API.blowup_limsup`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.
  Non-vacuity: the left `limsup` of the concrete `L^∞` slice norm is exactly
  `⊤`. -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft place.T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => velocity ε (t, x))) = ⊤

  -- ### The two vanishing cross-transport terms `03-torus.tex:322-328` (proof of `eq:insertion`)
  /-- `03-torus.tex:322-328`: the first cross-advection term `(b_ε·∇)U_ε` is
  identically zero, where `b_ε = v + w_ε` (`correctedBackground`) is the
  corrected background and `U_ε = periodizedScaledVelocity P x₀ T ε` the
  periodized packet.  TORUS: the periodic form of the whole-space cancellation
  used in Theorem 4.2's proof.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀,
  ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the directional (Fréchet) derivative of the
  actual packet in the actual background direction vanishes pointwise. -/
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative
          (periodizedScaledVelocity P place.x₀ place.T ε) t x
          (correctedBackground reference.velocity D.correction ε (t, x)) = 0
  /-- `03-torus.tex:322-328`: the second cross-advection term `(U_ε·∇)b_ε` is
  identically zero.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.
  Non-vacuity: the directional derivative of the actual background in the actual
  packet direction vanishes pointwise, so that (with the previous field) the
  momentum equation is exact. -/
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative
          (correctedBackground reference.velocity D.correction ε) t x
          (periodizedScaledVelocity P place.x₀ place.T ε (t, x)) = 0

  -- ### Localization of the velocity difference `03-torus.tex:293-295` clause (iii)
  /-- `03-torus.tex:295`: `u_ε - v` is divergence free at every `t < T`,
  including `t = 0`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.
  Non-vacuity: the physical divergence of the actual difference vanishes. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (fun z => velocity ε z - reference.velocity z) t x = 0
  /-- `03-torus.tex:293-295`: the fixed radius scale `ρ` giving the `O(ε)`
  support diameter.  Non-vacuity: `diffSupportRadius_pos` forces it positive. -/
  diffSupportRadius : ℝ
  /-- `03-torus.tex:293-295`: `ρ > 0`.  Non-vacuity: excludes a degenerate ball. -/
  diffSupportRadius_pos : 0 < diffSupportRadius
  /-- `03-torus.tex:293-295` clause (iii): for every `t < T` the (torus-lifted)
  support of `u_ε - v` lies in the integer translates of the ball of radius
  `ε · ρ` about `x₀` — a set of diameter `O(ε)`.  TORUS: a periodic (single-copy)
  support, via `periodicSet`, rather than the whole-space single ball of `R42`
  (a periodic difference is never contained in one bounded ball).
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T`.  Non-vacuity: an actual
  `tsupport ⊆ periodicSet (ball …)` inclusion. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => velocity ε (t, x) - reference.velocity (t, x)) ⊆
        periodicSet (Metric.ball place.x₀ (ε * diffSupportRadius))
  /-- `03-torus.tex:293-295` clause (iii), "inside the chosen ball": the
  `O(ε)`-ball lies in the placement chart ball `B`.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an actual metric-ball inclusion in `B`. -/
  diffSupport_in_chart : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Metric.ball place.x₀ (ε * diffSupportRadius) ⊆
      Metric.ball place.chartCenter place.chartRadius

  -- ### The three closeness rates `03-torus.tex:296-306` clause (iv)
  /-- `03-torus.tex:300-302` `eq:Eclose`: `‖u_ε - v‖_{E_T} ≤ (M+D)ε^{1/2} +
  Cε^{3/2}`, with `M = P.energyBound`, `D = P.dissipationBound` (`lem:packetenergy`,
  carried by the energy-enhanced `P`) and `C = correction.energyConst` (`eq:wE`).
  The norm is the registered torus `energyENormT` (`essSup + lintegral`, so no
  representative infimum and no `MemLp` guard is needed).  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an `ℝ≥0∞` inequality on the actual energy norm
  of the actual difference. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyENormT place.T (fun z => velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correction.energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:303-304` `eq:Fclose`: the mixed-norm constant `C_{p,q}`, real
  data fixed before `ε`.  Non-vacuity: `forceDiffMixedConst_nonneg` prevents a
  negative witness erased by `ENNReal.ofReal`. -/
  forceDiffMixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:303-304`: `C_{p,q} ≥ 0` on `1 ≤ p, q`.  Quantifier order:
  `∀ p q, 1 ≤ p, 1 ≤ q`.  Non-vacuity: on the exact range of the bound. -/
  forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ forceDiffMixedConst p q
  /-- `03-torus.tex:303-304`: honest torus mixed Bochner path of `g_ε - g`,
  `MemMixedLebesgueT q p` — an `L^q(0,∞)` time-path of `L^p(T³)` slices.  TORUS:
  the per-slice `MemLp` guard of draft B does not exclude the
  `mixedLebesgueENormT = ⨅ = ⊤` trap; the `∃ time-path` guard does.
  Quantifier order: `∀ p q [Fact (1≤p)], 1 ≤ q, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity:
  the actual difference has a strongly measurable finite-`L^q` mixed path. -/
  forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemMixedLebesgueT q p (fun z => force ε z - g z)
  /-- `03-torus.tex:303-304` `eq:Fclose`: `‖g_ε - g‖_{L^q_tL^p_x} ≤
  C_{p,q}(ε^{α(p,q)} + ε^{α(p,q)+1})`, `α(p,q) = -3+3/p+2/q` (registered
  `Contracts.V1.alpha`).  The `ε^{α}` term is `F_ε` (`eq:packetFscale`), the
  `ε^{α+1}` term is `H_ε` (`eq:Hmixed`); force norms over `(0,∞)`.  Quantifier
  order: `∀ p q [Fact (1≤p)], 1 ≤ q, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the previous
  field guards honesty; the norm is the copied `mixedLebesgueENormT`. -/
  forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      mixedLebesgueENormT q p (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffMixedConst p q *
          (ε ^ (BlowupDensity.Contracts.V1.alpha p q) +
            ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1)))
  /-- `03-torus.tex:305-306` `eq:Hsclose`: the Sobolev constant `C_s`, real data
  fixed before `ε`.  Non-vacuity: `forceDiffSobolevConst_pos` forces it positive
  on the used range. -/
  forceDiffSobolevConst : ℝ → ℝ
  /-- `03-torus.tex:305-306`: `C_s > 0` on `0 ≤ s < 1/2`.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2`.  TORUS: the range stops at `1/2` (`eq:Hsclose`), not at
  `1` (`eq:HHs`).  Non-vacuity: a strict positivity on the exact used range. -/
  forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < forceDiffSobolevConst s
  /-- `03-torus.tex:305-306`: honest `L¹_tH^s_x` Fourier-data path of `g_ε - g`,
  making the Bochner infimum in `forceSobolevENormT` honest.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the actual difference has
  a strongly-measurable `H^s` representing path. -/
  forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z)
  /-- `03-torus.tex:305-306` `eq:Hsclose`: `‖g_ε - g‖_{L¹_tH^s_x} ≤
  C_s(ε^{1/2-s} + ε^{3/2-s})` for `0 ≤ s < 1/2`.  The `ε^{1/2-s}` term is `F_ε`
  (`eq:packetHs`), the `ε^{3/2-s}` term is `H_ε` (`eq:HHs`); the lower-order
  `ε^{1/2}, ε^{3/2}` terms are absorbed since `0 ≤ s`, `0 < ε ≤ 1`.  Force norm
  over `(0,∞)` via the registered `forceSobolevENormT`.  Quantifier order:
  `∀ s, 0 ≤ s, s < 1/2, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the previous field guards
  honesty. -/
  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      forceSobolevENormT 1 s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))
  /-- `03-torus.tex:309-310`: "For `s < 0`, the force difference also tends to
  zero in `L¹_tH^s_x`."  Quantifier order: `∀ s, s < 0`, then the `Tendsto`.
  Non-vacuity: convergence of the registered `forceSobolevENormT 1 s` of the
  actual difference to `0` as `ε ↓ 0`. -/
  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  /-- `03-torus.tex:309-310`: honest negative-order `L¹_tH^s_x` paths for the
  `s<0` tail.  TORUS: convergence of an `⨅`-norm to `0` needs the norm eventually
  `< ⊤`; this `MemForceSobolevT 1 s` guard makes the limit non-vacuous.
  Quantifier order: `∀ s, s < 0, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: each totalized
  negative-order norm has an actual representing path. -/
  negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemForceSobolevT 1 s (fun z => force ε z - g z)

/-- **The existential form of `thm:insertion`,
`paper/sections/03-torus.tex:287-311`.**  Paper quantifier order (`:287-290`):
for every viscosity `ν > 0`, every energy-enhanced whole-space packet `P`,
placement, torus scaling record, initial datum `a`, reference force `g`, radii
`r`, margin `δ`, cutoff data `D`, reference solution regular through `T+δ`, and
correction record, with `δ > 0`, `g ∈ 𝓕`, `a ∈ 𝓧`, there is an inserted family:
`Nonempty` of the API, which carries the threshold `ε₀` as a field.  Introducing
this definition asserts nothing. -/
def periodicInsertionStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction :
      BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D),
    0 < δ → g ∈ forceClassT → a ∈ initialClassT →
      Nonempty (PeriodicInsertionAPI ν P place scaling a g r δ D reference correction)

end BlowupDensity.T18.Spec


-- copied verbatim from research/T22/Spec.lean:1-169
/-!
# T22 reconciled specification: bounded-domain restriction and zero extension

This is the statement-only reconciliation selected by
`research/T22/RECONCILIATION.md` for `paper/sections/03-torus.tex:600-630`,
especially `eq:restriction-norm` at lines 603-605 and `eq:zero-extension` at
lines 610-614.  It keeps Draft B's distributional quotient definition and its
three-field propositional API, with Draft A's citation detail folded into the
documentation.

## Vocabulary choice

The whole-space carrier, angular realization, physical-field bridge, and norm
are reused directly from the registered `Contracts.V1.Data` vocabulary:
`SpatialField`, `RealVectorSobolev`, `angularRealization`, `FourierData`, and
`sobolevENorm`.  No definition is copied from `research/T10/Spec.lean`.
That file is a standalone research specification and cannot be imported as a
module; more importantly, the binding ruling in `research/T22/RECONCILIATION.md`
§3 says that T22's two displays are entirely on `R^3` and `Omega` and require
no periodic T10 object.  The later T23 consumer, rather than this norm layer,
is where the registered version of T10's periodic vocabulary will meet these
definitions.

All definitions introduced here still need registration.  No inhabitant of
`BoundedDomainNormAPI` is asserted, and no bounded zero-extension operator on
arbitrary `H^s(Omega)` is encoded.
-/

noncomputable section

namespace BlowupDensity.T22.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## Bounded-domain distributional vocabulary -/

/-- `03-torus.tex:601-604`: compactly supported smooth tests inside `Omega`,
represented as Schwartz functions on `R^3`.

This definition needs registration. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/-- `03-torus.tex:601-606`: coordinates of a distribution restricted to
`Omega`.  Only functionals admitting a Sobolev extension have finite norm
below; the ambient type itself is deliberately total.

This definition needs registration. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/-- `03-torus.tex:601-604`: distributional restriction of a registered
whole-space datum, including at negative orders.

This definition needs registration. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/-- `03-torus.tex:603-606`, `eq:restriction-norm`: the quotient extended norm,
literally the infimum over all distributional `H^s(R^3)` extensions.  An empty
extension family has value `top`, so the definition remains fail-safe at every
real order, including negative orders.

This definition needs registration. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/-- `03-torus.tex:608-615`: a locally smooth physical field restricted to
`Omega`, paired only against compactly supported interior tests.  Values
outside `Omega` do not contribute.

This definition needs registration. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/-- `03-torus.tex:610-615`: literal extension by zero of the values on
`Omega`.  Values supplied by the ambient representative outside `Omega` are
ignored.

This definition needs registration. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/-- `03-torus.tex:616-624`: `B` is the product of a whole-space Sobolev datum
`A` by the fixed real cutoff `chi`, expressed through the transpose action on
Schwartz tests.  No conjugation is inserted.

For the smooth compact cutoffs quantified in `cutoffMultiplier`,
`SchwartzMap.smulLeftCLM` is ordinary pointwise multiplication.  This graph
definition needs registration. -/
def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

/-! ## Reconciled target API -/

/-- The three bounded-domain norm facts selected by
`research/T22/RECONCILIATION.md` for `03-torus.tex:600-630`.

The quotient-norm identity is the definition `domainSobolevENorm`, rather than
a redundant API field.  `Omega` is any open set; boundedness and boundary
regularity are not used by these local statements. -/
structure BoundedDomainNormAPI : Prop where
  /-- `03-torus.tex:606-607`: at order zero the restriction quotient norm is
  the usual vector `L^2(Omega)` norm.  Local smoothness makes the displayed
  physical pairing meaningful; either side is allowed to be infinite.

  Exact quantifier order: `forall Omega`, openness, `forall z`, then
  smoothness on `Omega`.

  Non-vacuity: this equates the independently defined distributional infimum
  with the concrete restricted-measure `eLpNorm`; it is not an unfolding of
  `domainSobolevENorm`. -/
  orderZero : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
    ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) =
      eLpNorm z 2 (volume.restrict Ω)

  /-- `03-torus.tex:616-624`: multiplication by a fixed compactly supported
  smooth cutoff is bounded on `H^s(R^3)` for every real `s`.  The finite
  positive constant depends only on `s` and `chi`, and is chosen before `A`.

  Exact quantifier order: `forall s chi`, regularity of `chi`, `exists C > 0`,
  `forall A`, then `exists B` realizing the cutoff product.

  Non-vacuity: the conclusion produces an actual datum `B`, pins its
  distributional graph by `IsCutoffDatum`, and bounds its concrete extended
  norm uniformly over all input data. -/
  cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ

  /-- `03-torus.tex:608-626`, `eq:zero-extension`: for a fixed compact
  `K` contained in an open `Omega`, every real Sobolev order has one positive
  constant giving the displayed two-sided comparison for all smooth fields
  whose zero extension is supported in `K`.

  Exact quantifier order: `forall Omega K`, the geometric hypotheses,
  `forall s`, `exists C > 0`, and only then `forall z`.  Thus `C` is uniform
  over smaller supports, time slices, and shrinking `epsilon`-families that
  stay inside the same `K`, as required at `03-torus.tex:626-629`.

  Non-vacuity: the conclusion is the full chain between the domain quotient
  norm and the registered whole-space norm of the literal zero extension.
  Its interior-support hypothesis deliberately prevents this field from
  asserting a bounded zero-extension operator on arbitrary domain data. -/
  zeroExtensionComparison :
      ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
        ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
          ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
          domainSobolevENorm Ω s (restrictField Ω z) ≤
              sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
              ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)

end BlowupDensity.T22.Draft


namespace BlowupDensity.T23.Draft
open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.T22.Draft
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:632-634`: concrete regular-level-set encoding of a smooth
domain.  Non-vacuity: it carries a `C∞` defining function and nonzero boundary
derivative, rather than an unconstrained proposition. -/
def IsRegularLevelDomain (Ω : Set Space) : Prop :=
  ∃ φ : Space → ℝ, ContDiff ℝ ∞ φ ∧ Ω = {x | φ x < 0} ∧
    ∀ x ∈ frontier Ω, fderiv ℝ φ x ≠ 0

/-- `03-torus.tex:632-634`: coordinate-box domain.  Non-vacuity: the stored
lower and upper corners have strict coordinate separation. -/
def IsBoxDomain (Ω : Set Space) : Prop :=
  ∃ lo hi : Fin 3 → ℝ, (∀ i, lo i < hi i) ∧
    Ω = {x : Space | ∀ i : Fin 3, lo i < x i ∧ x i < hi i}

/-- `03-torus.tex:632-634`: the paper's disjunctive domain class. -/
def IsBoundedBoxOrSmoothDomain (Ω : Set Space) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ (IsBoxDomain Ω ∨ IsRegularLevelDomain Ω)

/-- `03-torus.tex:635-639`: neighborhood-based closed-slab smoothness. -/
def SmoothOnClosedDomainSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set Space) (I : Set ℝ)
    (z : SpaceTime → E) : Prop :=
  ∃ U : Set SpaceTime, IsOpen U ∧ I ×ˢ closure Ω ⊆ U ∧ ContDiffOn ℝ ∞ z U

/-- `03-torus.tex:635-637`: compact temporal support in positive time. -/
def CompactPositiveTimeSupportOnDomain (_Ω : Set Space) (g : SpaceTimeField) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport g ⊆ K ×ˢ univ

/-- `03-torus.tex:635-637`: bounded-domain force class. -/
def DomainForceClass (Ω : Set Space) : Set SpaceTimeField :=
  {g | (∀ S : ℝ, 0 < S → SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) S) g) ∧
      CompactPositiveTimeSupportOnDomain Ω g}

/-- `03-torus.tex:637-638`: spatial mean used for pressure normalization. -/
def domainMean (Ω : Set Space) (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  ∫ x in Ω, p (t, x)

/-- `03-torus.tex:643-646`: a quotient-domain Sobolev representing path. -/
def IsDomainSobolevPath (Ω : Set Space) (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    restrictDatum Ω s (G t) = restrictField Ω (fun x ↦ f (t, x))

/-- `03-torus.tex:643-646`: the ENNReal quotient-domain force norm. -/
def domainForceSobolevENorm (Ω : Set Space) (q : ℝ≥0∞) (s : ℝ)
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsDomainSobolevPath Ω s f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `03-torus.tex:643-646`: finite measurable-path guard for that norm. -/
def MemDomainForceSobolev (Ω : Set Space) (q : ℝ≥0∞) (s : ℝ)
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → RealVectorSobolev s,
    IsDomainSobolevPath Ω s f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:660-662`: finite whole-space guard for zero extensions. -/
def MemWholeSpaceSobolev (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → RealVectorSobolev s,
    IsSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:640-642`: the domain `E_T` energy norm. -/
def domainEnergyENorm (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t ↦ eLpNorm (fun x : Space ↦ z (t, x)) 2
      (volume.restrict Ω)) (volume.restrict (Ioo (0 : ℝ) T)) +
    (∫⁻ t in Ioo (0 : ℝ) T, (∑ i : Fin 3,
      eLpNorm (fun x : Space ↦
        fderiv ℝ (fun y : Space ↦ z (t, y)) x (coordinateVector i)) 2
          (volume.restrict Ω)) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `03-torus.tex:640-642`: slice-wise `MemLp` guard for the energy norm. -/
def DomainEnergySlicesMemLp (Ω : Set Space) (T : ℝ) (u : SpaceTimeField) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (fun x : Space ↦ u (t, x)) 2 (volume.restrict Ω)) ∧
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
      MemLp (fun x : Space ↦
        fderiv ℝ (fun y : Space ↦ u (t, y)) x (coordinateVector i))
        2 (volume.restrict Ω)

/-- `03-torus.tex:635-651`: concrete bounded-domain no-slip solution predicate. -/
def IsBoundedClassicalSolution (Ω : Set Space) (ν : ℝ) (a : SpatialField)
    (g : SpaceTimeField) (T : ℝ) (u : SpaceTimeField)
    (p : SpaceTimeScalar) : Prop :=
  0 < T ∧
    SmoothOnClosedDomainSlab Ω (Ico (0 : ℝ) T) u ∧
    SmoothOnClosedDomainSlab Ω (Ico (0 : ℝ) T) p ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω, spatialDivergence u t x = 0) ∧
    (∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
      navierStokesResidual ν u p t x = g (t, x)) ∧
    (∀ x ∈ Ω, u (0, x) = a x) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, u (t, x) = 0) ∧
    (∀ t ∈ Ico (0 : ℝ) T, domainMean Ω p t = 0) ∧
    DomainEnergySlicesMemLp Ω T u

/-- `03-torus.tex:647-651`: ENNReal supremum of bounded solution horizons. -/
def boundedMaximalLifespan (Ω : Set Space) (ν : ℝ) (a : SpatialField)
    (g : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty
      {up : SpaceTimeField × SpaceTimeScalar //
        IsBoundedClassicalSolution Ω ν a g S up.1 up.2}, ENNReal.ofReal S

/-- `03-torus.tex:647-651`: maximal bounded pair below that supremum. -/
def IsMaximalBoundedSolution (Ω : Set Space) (ν : ℝ) (a : SpatialField)
    (g u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < boundedMaximalLifespan Ω ν a g ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < boundedMaximalLifespan Ω ν a g →
      IsBoundedClassicalSolution Ω ν a g S u p

/-- `03-torus.tex:647-651`: pointwise domain blow-up at `T`. -/
def DomainSpeedUnboundedAt (Ω : Set Space) (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x ∈ Ω, t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ M < ‖u (t, x)‖

/-- `03-torus.tex:647-651`: essential-supremum speed on Ω. -/
def domainSpeedENorm (Ω : Set Space) (u : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  essSup (fun x : Space => ENNReal.ofReal ‖u (t, x)‖)
    (volume.restrict Ω)

/-- `03-torus.tex:647-651`: left limsup of the domain speed norm. -/
def DomainSpeedLimsup (Ω : Set Space) (T : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft T
    (fun t ↦ domainSpeedENorm Ω u t)

/-- `03-torus.tex:643-646`: restricted `L^p` slice path. -/
def IsDomainLebesgueSlicePath (Ω : Set Space) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p (volume.restrict Ω)) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : Space → Space) =ᵐ[volume.restrict Ω] fun x ↦ f (t, x)

/-- `03-torus.tex:643-646`: restricted mixed norm, retained for future mixed
estimates even though the corollary's displayed convergence is Sobolev. -/
def domainMixedLebesgueENorm (Ω : Set Space) (q p : ℝ≥0∞)
    [Fact (1 ≤ p)] (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p (volume.restrict Ω) //
      IsDomainLebesgueSlicePath Ω p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-! `03-torus.tex:632-667`: `BoundaryInsertionAPI` is Type-valued because it
carries the actual domain, epsilon-indexed fields, collar, support radius, and
finite constants.  Every other declaration below is a concrete Prop or norm
definition, never a free proposition parameter.  The paper order is retained:
domain and reference hypotheses first, then one positive epsilon threshold,
then the three insertion displays, the classical/no-slip conclusions, the
support and energy clauses, and finally the domain/zero-extension convergence
and uniqueness clauses.  Every norm is ENNReal-valued; its adjacent MemLp or
class field is the non-vacuity guard against totalized junk values. -/
structure BoundaryInsertionAPI (ν : ℝ) (Ω : Set Space)
    (a : SpatialField) (g : SpaceTimeField) (T δ : ℝ)
    (v : SpaceTimeField) (π : SpaceTimeScalar) : Type where
  /-- `03-torus.tex:632-634`: Ω is a bounded box or bounded smooth domain. -/
  domain_shape : IsBoundedBoxOrSmoothDomain Ω
  /-- `03-torus.tex:632-634`: viscosity is positive. -/
  viscosity_pos : 0 < ν
  /-- `03-torus.tex:632-634`: the target time is positive. -/
  time_pos : 0 < T
  /-- `03-torus.tex:633-634`: the compatible reference margin is positive. -/
  delta_pos : 0 < δ
  /-- `03-torus.tex:635-637`: the reference force is smooth with compact
  temporal support in `(0,∞)`. -/
  reference_force_mem : g ∈ DomainForceClass Ω
  /-- `03-torus.tex:635-636`: the reference initial velocity is `a` in Ω. -/
  initial_datum : ∀ x ∈ Ω, v (0, x) = a x
  /-- `03-torus.tex:635-639`: reference velocity smoothness on the closed slab. -/
  reference_velocity_smooth :
    SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) (T + δ)) v
  /-- `03-torus.tex:635-639`: reference pressure smoothness on the closed slab. -/
  reference_pressure_smooth :
    SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) (T + δ)) π
  /-- `03-torus.tex:635-639`: force smoothness on every finite closed slab. -/
  reference_force_smooth :
    ∀ S : ℝ, 0 < S →
      SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) S) g
  /-- `03-torus.tex:635-637`: incompressibility holds in Ω through `T+δ`. -/
  reference_divergence :
    ∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ Ω,
      spatialDivergence v t x = 0
  /-- `03-torus.tex:635-637`: the reference momentum equation holds in Ω. -/
  reference_momentum :
    ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Ω,
      navierStokesResidual ν v π t x = g (t, x)
  /-- `03-torus.tex:635-637`: reference no-slip boundary values. -/
  reference_no_slip :
    ∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ frontier Ω, v (t, x) = 0
  /-- `03-torus.tex:637-638`: optional zero spatial mean pressure gauge. -/
  reference_pressure_gauge :
    ∀ t ∈ Icc (0 : ℝ) (T + δ), domainMean Ω π t = 0
  /-- `03-torus.tex:639-641`: one fixed compact interior support region. -/
  interior_region : Set Space
  /-- `03-torus.tex:639-641`: the support region is compact. -/
  interior_region_compact : IsCompact interior_region
  /-- `03-torus.tex:639-641`: the support region lies strictly inside Ω. -/
  interior_region_subset : interior_region ⊆ interior Ω
  /-- `03-torus.tex:642-644`: a fixed collar used to record preservation. -/
  collar : Set Space
  /-- `03-torus.tex:642-644`: the collar is open. -/
  collar_open : IsOpen collar
  /-- `03-torus.tex:642-644`: the collar contains the boundary. -/
  collar_covers_boundary : frontier Ω ⊆ collar
  /-- `03-torus.tex:642-644`: inserted support and collar are disjoint. -/
  collar_disjoint_interior : Disjoint collar interior_region
  /-- `03-torus.tex:642-643`: one threshold for all sufficiently small scales. -/
  ε₀ : ℝ
  /-- `03-torus.tex:642-643`: the threshold is positive. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:644`: the inserted velocity family. -/
  velocity : ℝ → SpaceTimeField
  /-- `03-torus.tex:644`: the inserted pressure family. -/
  pressure : ℝ → SpaceTimeScalar
  /-- `03-torus.tex:644`: the inserted force family. -/
  force : ℝ → SpaceTimeField
  /-- `03-torus.tex:644-646`: the local correction family. -/
  backgroundCorrection : ℝ → SpaceTimeField
  /-- `03-torus.tex:644-646`: the localized packet velocity family. -/
  packetVelocity : ℝ → SpaceTimeField
  /-- `03-torus.tex:644-646`: the packet pressure family. -/
  packetPressure : ℝ → SpaceTimeScalar
  /-- `03-torus.tex:644-646`: the packet force family. -/
  packetForce : ℝ → SpaceTimeField
  /-- `03-torus.tex:644-646`: the correction force family. -/
  correctionForce : ℝ → SpaceTimeField
  /-- `03-torus.tex:644`: `u_ε=v+w_ε+U_ε`. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = v z + backgroundCorrection ε z + packetVelocity ε z
  /-- `03-torus.tex:644`: `p_ε=π+P_ε`, with the chosen gauge represented by
  `reference_pressure_gauge`. -/
  pressure_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    pressure ε z = π z + packetPressure ε z
  /-- `03-torus.tex:644`: `g_ε=g+H_ε+F_ε`. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ε z + packetForce ε z
  /-- `03-torus.tex:647-648`: every inserted force is in the domain force class. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, force ε ∈ DomainForceClass Ω
  /-- `03-torus.tex:647-648`: every force difference is a smooth positive-time
  compactly supported domain force. -/
  forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (fun z ↦ force ε z - g z) ∈ DomainForceClass Ω
  /-- `03-torus.tex:647-649`: velocity smoothness on the presingular slab. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SmoothOnClosedDomainSlab Ω (Ico (0 : ℝ) T) (velocity ε)
  /-- `03-torus.tex:647-649`: pressure smoothness on the presingular slab. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SmoothOnClosedDomainSlab Ω (Ico (0 : ℝ) T) (pressure ε)
  /-- `03-torus.tex:647-649`: initial velocity is unchanged in Ω. -/
  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x ∈ Ω, velocity ε (0, x) = a x
  /-- `03-torus.tex:647-650`: inserted velocity is incompressible in Ω. -/
  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω,
      spatialDivergence (velocity ε) t x = 0
  /-- `03-torus.tex:647-650`: the bounded-domain momentum equation. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)
  /-- `03-torus.tex:647-651`: the quiet initial history is unchanged. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ T - 2 * ε ^ 2 → ∀ x ∈ Ω, velocity ε (t, x) = v (t, x)
  /-- `03-torus.tex:647-651`: no-slip values hold on the boundary. -/
  no_slip : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, velocity ε (t, x) = 0
  /-- `03-torus.tex:642-644`: the reference is preserved in one fixed collar. -/
  boundary_collar_preserved : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ collar,
      velocity ε (t, x) = v (t, x)
  /-- `03-torus.tex:637-638`: inserted pressure keeps the zero-mean gauge. -/
  pressure_gauge : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, domainMean Ω (pressure ε) t = 0
  /-- `03-torus.tex:647-650`: the named fields form a bounded classical solution. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsBoundedClassicalSolution Ω ν a (force ε) T (velocity ε) (pressure ε)
  /-- `03-torus.tex:666-667`: no-slip uniqueness for two bounded classical
  solutions with the same data and force. -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalBoundedSolution Ω ν a (force ε) (velocity ε) (pressure ε)
  /-- `03-torus.tex:666-667`: the constructed lifespan is exactly `T`. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    boundedMaximalLifespan Ω ν a (force ε) = ENNReal.ofReal T
  /-- `03-torus.tex:647-651`: speed is unbounded in every left neighborhood of T. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    DomainSpeedUnboundedAt Ω T (velocity ε)
  /-- `03-torus.tex:647-651`: the essential-supremum limsup is infinite. -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    DomainSpeedLimsup Ω T (velocity ε) = ⊤
  /-- `03-torus.tex:653-655`: background advection of the packet vanishes. -/
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (packetVelocity ε) t x
        (v (t, x) + backgroundCorrection ε (t, x)) = 0
  /-- `03-torus.tex:653-655`: packet advection of the corrected background vanishes. -/
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (fun z ↦ v z + backgroundCorrection ε z) t x
        (packetVelocity ε (t, x)) = 0
  /-- `03-torus.tex:653-654`: the velocity difference is divergence free. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω,
      spatialDivergence (fun z ↦ velocity ε z - v z) t x = 0
  /-- `03-torus.tex:653-655`: the fixed O(ε) support radius. -/
  difference_support_radius : ℝ
  /-- `03-torus.tex:653-655`: the support radius is positive. -/
  difference_support_radius_pos : 0 < difference_support_radius
  /-- `03-torus.tex:653-655`: the velocity difference is supported in the
  shrinking interior ball. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x : Space => velocity ε (t, x) - v (t, x)) ⊆
        Metric.ball (0 : Space) (ε * difference_support_radius)
  /-- `03-torus.tex:653-655`: every shrinking ball remains in the fixed interior. -/
  difference_support_interior : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Metric.ball (0 : Space) (ε * difference_support_radius) ⊆ interior_region
  /-- `03-torus.tex:656`: domain L2 and gradient slices are honest MemLp data. -/
  energy_slices_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    DomainEnergySlicesMemLp Ω T (fun z ↦ velocity ε z - v z)
  /-- `03-torus.tex:656`: the packet energy constant. -/
  energyBound : ℝ
  /-- `03-torus.tex:656`: the packet dissipation constant. -/
  dissipationBound : ℝ
  /-- `03-torus.tex:656`: the correction energy constant. -/
  correctionEnergyConst : ℝ
  /-- `03-torus.tex:656`: constants are nonnegative before `ENNReal.ofReal`. -/
  energy_constants_nonneg : 0 ≤ energyBound ∧ 0 ≤ dissipationBound ∧
    0 ≤ correctionEnergyConst
  /-- `03-torus.tex:656`: the domain energy estimate. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainEnergyENorm Ω T (fun z ↦ velocity ε z - v z) ≤
      ENNReal.ofReal ((energyBound + dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correctionEnergyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:657-660`: honest domain `L1_t H^s_x` paths for `0≤s<1/2`. -/
  forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemDomainForceSobolev Ω 1 s (fun z ↦ force ε z - g z)
  /-- `03-torus.tex:657-660`: the subcritical domain Sobolev rate. -/
  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω 1 s (fun z ↦ force ε z - g z) ≤
        ENNReal.ofReal (correctionEnergyConst *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))
  /-- `03-torus.tex:660-661`: subcritical convergence for every `s<1/2`. -/
  forceDifference_sobolev_tendsto : ∀ s : ℝ, s < 1 / 2 →
    Tendsto
      (fun ε : ℝ ↦ domainForceSobolevENorm Ω 1 s
        (fun z ↦ force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  /-- `03-torus.tex:660-661`: honest negative-order domain paths. -/
  forceDifference_negativeSobolev_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      MemDomainForceSobolev Ω 1 s (fun z ↦ force ε z - g z)
  /-- `03-torus.tex:660-661`: negative-order force convergence. -/
  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto
      (fun ε : ℝ ↦ domainForceSobolevENorm Ω 1 s
        (fun z ↦ force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  /-- `03-torus.tex:660-662`: every order has a scale-independent domain versus
  zero-extension comparison constant. -/
  zeroExtension_comparison : ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω 1 s (fun z ↦ force ε z - g z) ≤
        forceSobolevENorm 1 s
          (fun z ↦ BlowupDensity.T22.Draft.zeroExtension Ω
            (fun x ↦ force ε (z.1, x) - g (z.1, x)) z.2) ∧
      forceSobolevENorm 1 s
          (fun z ↦ BlowupDensity.T22.Draft.zeroExtension Ω
            (fun x ↦ force ε (z.1, x) - g (z.1, x)) z.2) ≤
        ENNReal.ofReal C * domainForceSobolevENorm Ω 1 s
          (fun z ↦ force ε z - g z)
  /-- `03-torus.tex:660-662`: the zero-extended paths are honest before their
  whole-space norm is used. -/
  zeroExtension_sobolev_memLp : ∀ s : ℝ, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    MemWholeSpaceSobolev 1 s
      (fun z ↦ BlowupDensity.T22.Draft.zeroExtension Ω
        (fun x ↦ force ε (z.1, x) - g (z.1, x)) z.2)
  /-- `03-torus.tex:666-667`: classical no-slip uniqueness identifies both
  velocity and the zero-mean pressure on the common slab. -/
  noSlip_uniqueness :
    ∀ (h : SpaceTimeField) (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
      h ∈ DomainForceClass Ω →
      IsBoundedClassicalSolution Ω ν a h T u₁ p₁ →
      IsBoundedClassicalSolution Ω ν a h T u₂ p₂ →
      ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω,
        u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)

/-! `03-torus.tex:632-667`: existential statement in the paper's quantifier
order.  Ω and its geometric hypothesis come first; then ν, the initial and
reference fields, the positive extension margin and all reference equations;
the conclusion is `Nonempty (BoundaryInsertionAPI ...)`.  This Prop is
statement-only: it introduces no witness. -/
def boundaryInsertionStatement : Prop :=
  ∀ (Ω : Set Space), IsBoundedBoxOrSmoothDomain Ω →
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField) (g : SpaceTimeField)
        (T δ : ℝ) (v : SpaceTimeField) (π : SpaceTimeScalar),
        0 < T →
        0 < δ →
        (∀ S : ℝ, 0 < S → SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) S) g) →
        CompactPositiveTimeSupportOnDomain Ω g →
        SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) (T + δ)) v →
        SmoothOnClosedDomainSlab Ω (Icc (0 : ℝ) (T + δ)) π →
        (∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ Ω,
          spatialDivergence v t x = 0) →
        (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Ω,
          navierStokesResidual ν v π t x = g (t, x)) →
        (∀ x ∈ Ω, v (0, x) = a x) →
        (∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ frontier Ω, v (t, x) = 0) →
        (∀ t ∈ Icc (0 : ℝ) (T + δ), domainMean Ω π t = 0) →
        Nonempty (BoundaryInsertionAPI ν Ω a g T δ v π)

end BlowupDensity.T23.Draft
