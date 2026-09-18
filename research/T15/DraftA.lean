import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti
import Contracts.V1.HomogeneousNorm
import Contracts.V1.Packet
import Contracts.V1.Scaling

/-!
# T15 blind specification draft A: scaling at fixed viscosity on the torus

This statement-only draft specifies `prop:scaling` from
`paper/sections/03-torus.tex:101-159`.  Physical torus fields remain functions
on `R^3` with unit spatial periods.  The whole-space packet is first rescaled
by the literal formulas of `eq:scaling`, then periodized by a lattice sum, and
the pressure is normalized by subtracting its spatial mean.

The momentum clause is pointwise rather than an existential
`ClassicalSolutionT`: this pins the equation to the explicit periodized fields
and mirrors the registered `I03.scaling` clauses.  Smoothness, periodicity,
zero initial data, and pressure gauge are retained as separate concrete
fields, so the pointwise choice does not weaken the classical content used by
T18.

All displayed norms are `R>=0 infinity`-valued.  In particular, the torus
mixed norm below uses the same measurable-Bochner-path design as Section 4,
but its spatial `Lp` carrier is `UnitAddTorus (Fin 3)`, not `R^3`.
-/

noncomputable section

/- copied from research/T10/Spec.lean:40-211; delete once registered -/
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
then lattice frequency. -/
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
mean-zero real periodic field.  Exact quantifier order: periodicity, zero mean,
then `∀ i : Fin 3, ∀ k : PeriodicFrequency`.  The zero-frequency equation forces
`A_i(0)=0`, as the manuscript's homogeneous convention requires. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Hdot^s(T³)` extended norm of a mean-zero physical field.  It is the infimum over
homogeneous real data and is `⊤` when no datum exists. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/- copied from research/T10/Spec.lean:252-300; delete once registered -/

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

/- copied from research/T10/Spec.lean:390-407; delete once registered -/

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

/- copied from research/T13/Spec.lean:159-314; delete once registered -/
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

/-- `03-torus.tex:80-89`: the nonzero-lattice tail used in the proof of the
localization estimate.  Its bounds are proof lemmas, not API fields. -/
def latticeTail (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : {n : PeriodicFrequency // n ≠ 0},
    fractionalRadialKernel s (h + latticeVector n.1)

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

/- copied from research/T14/Spec.lean:39-108; delete once registered -/
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

All inherited `M`, `D`, quiet-interval, and negative-time-extension clauses are
already concrete fields of `PacketAPI`; T14 adds only the two relations in
`eq:packetenergy`. -/
structure PacketImportAPI (ν : ℝ) extends PacketAPI ν where
  /-- The full `eq:packetenergy` predicate for the inherited packet, not for a
  separately chosen witness; its zero extensions are used at
  `paper/sections/03-torus.tex:108-123,141`.

  Non-vacuity: the field constrains `toPacketAPI` through two explicit numerical
  relations and cannot be filled by choosing an unrelated packet. -/
  energy : PacketEnergyAPI toPacketAPI

end BlowupDensity.T14.Draft
/- end copied T14 declarations -/

namespace BlowupDensity.T15.DraftA

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Draft
open BlowupDensity.T14.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## 1. Literal scaling and lattice periodization -/

/-- `03-torus.tex:106,112-118`: the shifted source time is
`t_ε = T - ε²`. -/
def packetTimeShift (T ε : ℝ) : ℝ := T - ε ^ 2

/-- `03-torus.tex:112-118`: the spacetime point
`((t-t_ε)/ε²,(x-x₀)/ε)` at which the source packet is evaluated. -/
def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε ^ 2)⁻¹ * (z.1 - packetTimeShift T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:110-114`, the first formula of `eq:scaling`:
`U_ε(t,x)=ε⁻¹ U((t-t_ε)/ε²,(x-x₀)/ε)`, using T14's smooth
negative-time zero extension. -/
def scaledVelocity {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ ε⁻¹ • zeroPastField P.toPacketAPI.velocity (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:110-116`, the second formula of `eq:scaling`:
`P_ε(t,x)=ε⁻² P((t-t_ε)/ε²,(x-x₀)/ε)`, using T14's smooth
negative-time zero extension. -/
def scaledPressure {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ (ε⁻¹) ^ 2 *
    zeroPastField P.toPacketAPI.pressure (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-109,117-118`, the third formula of `eq:scaling`:
`F_ε(t,x)=ε⁻³ F((t-t_ε)/ε²,(x-x₀)/ε)`.  T14's packet force
is already its globally smooth zero extension, so no second wrapper is used. -/
def scaledForce {ν : ℝ} (P : PacketImportAPI ν) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ (ε⁻¹) ^ 3 • P.toPacketAPI.force (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:120`: spatial lattice-sum periodization of a vector-valued
spacetime field.  Time is not periodized. -/
def periodizeVelocity (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ∑' n : PeriodicFrequency, u (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: spatial lattice-sum periodization of a scalar pressure.
Time is not periodized. -/
def periodizePressure (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency, p (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:112-120`: the unit-periodic rescaled velocity. -/
def periodizedScaledVelocity {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  periodizeVelocity (scaledVelocity P x₀ T ε)

/-- `03-torus.tex:114-120`: the unit-periodic rescaled pressure before its
spatially constant normalization. -/
def periodizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) : SpaceTimeScalar :=
  periodizePressure (scaledPressure P x₀ T ε)

/-- `03-torus.tex:117-120`: the unit-periodic rescaled force. -/
def periodizedScaledForce {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  periodizeVelocity (scaledForce P x₀ T ε)

/-- `03-torus.tex:123`: the pressure representative obtained by the spatially
constant adjustment that enforces zero torus mean. -/
def normalizedScaledPressure {ν : ℝ} (P : PacketImportAPI ν)
    (x₀ : Space) (T ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure P x₀ T ε)

/-! ## 2. Honest mixed norms -/

/-- `03-torus.tex:129-132`, in the measurable-path spelling of
`Contracts.V1.Data.IsLebesgueSlicePath`: `G(t)` represents the `L^p(T³)`
slice of a periodic physical field at every nonnegative time. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-132`: the torus quantity
`‖f‖_{L^q(0,∞;L^p(T³))}`.  Like the registered Section 4 norm, it is an
infimum over strongly measurable Bochner representatives and is `⊤` when no
such representative exists. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- A non-junk-value witness for the preceding torus mixed norm: a genuine
Bochner `L^q` path represents the field. -/
def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- A non-junk-value witness for the registered whole-space mixed norm. -/
def MemMixedLebesgueR (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p (volume : Measure Space),
    IsLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- A non-junk-value witness for T10's periodic Sobolev time norm. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:131`: `α(p,q)=-3+3/p+2/q`.  `ENNReal.toReal` realizes
the endpoint convention `1/∞=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-! ## 3. Placement data fixed before the scale -/

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

/-! ## 4. Proposition 3.3 API -/

/-- Draft-A contract for every clause of `prop:scaling`,
`paper/sections/03-torus.tex:122-138`, for the one packet, placement, and T13
localization API supplied as parameters.

The fields below always quantify over the same `ε ∈ (0, place.ε₀]`.
The explicit `MemLp` witnesses prevent the totalized Bochner norms from hiding
missing measurability or integrability.  No declaration here supplies an
inhabitant of this structure. -/
structure ScalingAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.toPacketAPI)
    (localizationAPI : LocalizationAPI) where
  /-- `03-torus.tex:101-120`: on the fundamental cube, the lattice-sum
  periodization of `U_ε` is exactly its zero-lattice copy.

  Exact quantifier order: `ε`, admissibility, `t<T`, then `x` in the cube.
  Non-vacuity: the equality is between the concrete lattice sum and the
  literal rescaling; `place.eps_space` and `place.chartBall_in_cube` make all
  nonzero lattice terms vanish. -/
  velocity_single_copy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledVelocity P place.x₀ place.T ε (t, x) =
        scaledVelocity P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:101-120`: on the fundamental cube, the unnormalized
  periodized `P_ε` is exactly its zero-lattice copy.

  Exact quantifier order: `ε`, admissibility, `t<T`, then `x` in the cube.
  Non-vacuity: this is a concrete equality before the later spatially
  constant gauge adjustment. -/
  pressure_single_copy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledPressure P place.x₀ place.T ε (t, x) =
        scaledPressure P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:101-120`: on the fundamental cube, the periodized
  `F_ε` is exactly its zero-lattice copy at every positive time.

  Exact quantifier order: `ε`, admissibility, `t>0`, then `x` in the cube.
  Non-vacuity: `place.force_projection_subset` ties this equality to the
  spatial support of the selected packet force. -/
  force_single_copy : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, 0 < t → ∀ x ∈ fundamentalCube,
      periodizedScaledForce P place.x₀ place.T ε (t, x) =
        scaledForce P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:120-123,141`: the periodized rescaled velocity is smooth
  on the classical half-open slab.

  Exact quantifier order: every admissible `ε` has one concrete smooth
  field.  Non-vacuity: the field is the explicit lattice sum above, not an
  existentially chosen replacement. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ContDiffOn ℝ ∞ (periodizedScaledVelocity P place.x₀ place.T ε)
      (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))

  /-- `03-torus.tex:120-123,141`: the mean-normalized periodized pressure is
  smooth on the same slab.

  Exact quantifier order: `ε` precedes smoothness.  Non-vacuity: this
  constrains the explicit normalized pressure used in `momentum`. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ContDiffOn ℝ ∞ (normalizedScaledPressure P place.x₀ place.T ε)
      (Ico (0 : ℝ) place.T ×ˢ (univ : Set Space))

  /-- `03-torus.tex:108-120`: every periodized rescaled force lies in T10's
  smooth, unit-periodic, compact-positive-time force class.

  Exact quantifier order: for every admissible `ε` the fixed concrete
  force satisfies `MemForceT`.  Non-vacuity: this supplies smoothness,
  periodicity, and a compact time-support witness and is later consumed by
  T18. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    MemForceT (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:120-123`: the concrete velocity has unit spatial periods
  throughout `[0,T)`.

  Exact quantifier order is T10's `IsPeriodicOn`.  Non-vacuity: the interval
  is nonempty by `place.time_pos`. -/
  velocity_periodic : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    IsPeriodicOn (Ico (0 : ℝ) place.T)
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:120-123`: the normalized pressure has unit spatial
  periods throughout `[0,T)`.

  Exact quantifier order is T10's `IsPeriodicOn`.  Non-vacuity: the field is
  the same normalized pressure appearing in the equation. -/
  pressure_periodic : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    IsPeriodicOn (Ico (0 : ℝ) place.T)
      (normalizedScaledPressure P place.x₀ place.T ε)

  /-- `03-torus.tex:123`: the periodized scaled velocity starts from zero.

  Exact quantifier order: `ε`, admissibility, then every spatial point.
  Non-vacuity: this fixes the initial datum of the explicit velocity; it is
  forced by `place.eps_time` and T14's negative-time zero extension. -/
  zero_initial : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ x : Space,
    periodizedScaledVelocity P place.x₀ place.T ε (0, x) = 0

  /-- `03-torus.tex:123,141`: incompressibility is preserved by scaling and
  periodization.

  Exact quantifier order: `ε`, admissibility, `t∈[0,T)`, then `x`.
  Non-vacuity: the divergence is the concrete Fréchet-derivative expression
  used by the registered packet contract. -/
  divergence : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      BlowupDensity.Contracts.V1.spatialDivergence
        (periodizedScaledVelocity P place.x₀ place.T ε) t x = 0

  /-- `03-torus.tex:122-123,141`: the periodized fields solve the momentum
  equation at the unchanged viscosity `ν`.

  Exact quantifier order: `ε`, admissibility, `t∈(0,T)`, then `x`.
  Non-vacuity: all three fields are explicit definitions from the same packet
  and scale, so no solution can be substituted independently. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      BlowupDensity.Contracts.V1.navierStokesResidual ν
          (periodizedScaledVelocity P place.x₀ place.T ε)
          (normalizedScaledPressure P place.x₀ place.T ε) t x =
        periodizedScaledForce P place.x₀ place.T ε (t, x)

  /-- `03-torus.tex:123,142-143`: speed is unbounded in every left
  neighborhood of `T`.

  Exact quantifier order, inherited from registered `I03.scaling`: for every
  `M>0` and every `δ>0`, there are `t∈(0,T)` and `x` with `T-δ<t` and
  `M<‖U_ε(t,x)‖`.  Non-vacuity: it constrains the explicit periodized
  velocity, and is stronger than merely being unbounded somewhere before T. -/
  speed_unbounded : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    BlowupDensity.Contracts.V1.SpeedUnboundedAt place.T
      (periodizedScaledVelocity P place.x₀ place.T ε)

  /-- `03-torus.tex:123`: normalization changes the periodized pressure by a
  spatially constant function of time.

  Exact quantifier order: `ε`, admissibility, `t∈[0,T)`, then `x,y`.
  Non-vacuity: this compares the two explicit pressures pointwise rather than
  postulating an unrelated gauge-equivalent representative. -/
  pressure_adjustment_constant : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x y : Space,
      normalizedScaledPressure P place.x₀ place.T ε (t, x) -
          periodizedScaledPressure P place.x₀ place.T ε (t, x) =
        normalizedScaledPressure P place.x₀ place.T ε (t, y) -
          periodizedScaledPressure P place.x₀ place.T ε (t, y)

  /-- `03-torus.tex:123`: the adjusted pressure has zero spatial mean.

  Exact quantifier order is T10's `PressureGaugeT` on `[0,T)`.
  Non-vacuity: the gauge is imposed on the same pressure used by `momentum`. -/
  pressure_gauge : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    PressureGaugeT (Ico (0 : ℝ) place.T)
      (normalizedScaledPressure P place.x₀ place.T ε)

  /-- `03-torus.tex:125-128,145-146`: both energy quantities are finite.

  Exact quantifier order: for every admissible `ε`, finiteness of the
  `L∞_tL²_x` term and then the `L²_tL²_x` gradient term.  Non-vacuity: this
  prevents totalized integrals from masking failed integrability before the
  two exact identities below are used. -/
  energy_finite : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T (periodizedScaledVelocity P place.x₀ place.T ε) < ⊤ ∧
      energyGradientT place.T
        (periodizedScaledVelocity P place.x₀ place.T ε) < ⊤

  /-- `03-torus.tex:125-126`, the first equality of `eq:packetEscale`:
  `‖U_ε‖_{L∞(0,T;L²(T³))}=ε^{1/2}M`.

  Exact quantifier order: every admissible `ε`.  Non-vacuity: T10's
  concrete energy norm is equated to T14's exact packet constant `M`, not an
  arbitrary upper bound. -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyEssSupT place.T (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.toPacketAPI.energyBound)

  /-- `03-torus.tex:127-128,145-146`, the second equality of
  `eq:packetEscale`: `‖∇U_ε‖_{L²(0,T;L²(T³))}=ε^{1/2}D`.

  Exact quantifier order: every admissible `ε`.  Non-vacuity: T10's
  concrete gradient norm is equated to T14's exact dissipation constant `D`. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    energyGradientT place.T (periodizedScaledVelocity P place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.toPacketAPI.dissipationBound)

  /-- `03-torus.tex:129-132,148-149`: honest Bochner representatives exist
  for both sides of every mixed-norm identity.

  Exact quantifier order: `p,q`, the endpoint-compatible assumptions
  `1≤p,1≤q`, then the source witness and every admissible `ε` witness.
  Non-vacuity: `MemLp` supplies strong measurability and finite norm, including
  the essential-supremum endpoints. -/
  mixed_mem : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    MemMixedLebesgueR q p P.toPacketAPI.force ∧
      ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
        MemMixedLebesgueT q p
          (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:129-132`, `eq:packetFscale`:
  `‖F_ε‖_{L^q_tL^p_x}=ε^{α(p,q)}‖F‖_{L^q_tL^p_x}` for all
  `1≤p,q≤∞`, with `α(p,q)=-3+3/p+2/q` given by `alphaT`.

  Exact quantifier order mirrors registered `I03.scaling`: `p,q`, the two
  lower-bound hypotheses, then every admissible `ε`.  Non-vacuity:
  `mixed_mem` makes both measurable-path norms honest; the left norm is on the
  torus and the right norm is the registered whole-space norm. -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      mixedLebesgueENormT q p
          (periodizedScaledForce P place.x₀ place.T ε) =
        ENNReal.ofReal (ε ^ alphaT p q) *
          mixedLebesgueENorm q p P.toPacketAPI.force

  /-- `03-torus.tex:133-136`: the constants `C_s`, selected after `s` and all
  fixed packet/chart data but before `ε`.

  Exact quantifier order is encoded by this data field `s ↦ C_s`, outside
  `packetSobolevBound`'s scale quantifier.  Non-vacuity: positivity is imposed
  by the following field. -/
  sobolevConst : ℝ → ℝ

  /-- `03-torus.tex:133-136`: `C_s>0` for `0≤s≤1`.

  Exact quantifier order: `s`, then its two range assumptions.
  Non-vacuity: a negative constant cannot make the norm bound vacuous. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s

  /-- `03-torus.tex:133-158`: the periodic rescaled force has an honest
  `L¹_tH^s_x` Bochner representative at every order `0≤s≤1`.

  Exact quantifier order: `s`, its range, `ε`, admissibility.
  Non-vacuity: this `MemLp` witness prevents T10's totalized infimum from
  recording a finite-looking value without a measurable Sobolev path. -/
  sobolev_mem : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s
        (periodizedScaledForce P place.x₀ place.T ε)

  /-- `03-torus.tex:133-136,150-158`, `eq:packetHs`:
  `‖F_ε‖_{L¹(0,∞;H^s(T³))}≤C_s(ε^{1/2}+ε^{1/2-s})` for
  `0≤s≤1`.

  Exact quantifier order: `s`, its range, then every admissible `ε`; hence
  `C_s` is uniform in the scale.  Non-vacuity: `sobolev_mem` supplies the
  honest Bochner path, and the carried `localizationAPI.localization` is the
  uniform estimate used to transfer the whole-space homogeneous scaling to
  the torus rather than an unproved replacement localization statement. -/
  packetSobolevBound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s
          (periodizedScaledForce P place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)))

/-! ## 5. Separate derived conclusion -/

/-- `03-torus.tex:138,158`: the separately named conclusion to be derived
from `ScalingAPI.packetSobolevBound` for `0≤s<1/2`, and from the monotonicity
`‖z‖_{H^s}≤‖z‖_2` for negative `s`.  It is deliberately a proposition over
an existing API, not an additional field: the paper says "in particular", so
the registered implementation should prove it rather than assume it.

Exact quantifier order: every real `s<1/2`, then convergence as positive
`ε→0`.  The positive-side filter ensures the expression is only sampled at
scales used by the construction. -/
def ForceConvergesBelowCritical {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.toPacketAPI) (localizationAPI : LocalizationAPI)
    (_A : ScalingAPI P place localizationAPI) : Prop :=
  ∀ s : ℝ, s < (1 : ℝ) / 2 →
    Tendsto
      (fun ε : ℝ ↦ forceSobolevENormT 1 s
        (periodizedScaledForce P place.x₀ place.T ε))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)

end BlowupDensity.T15.DraftA
