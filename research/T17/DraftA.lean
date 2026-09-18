import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti
import Contracts.V1.HomogeneousNorm
import Contracts.V1.Correction
import Contracts.V2.Correction

/-!
# T17 blind draft A: bounds for the periodic background correction

Statement-only draft for Lemma `lem:correction`
(`paper/sections/03-torus.tex:218-285`).  The temporary declarations copied
below keep this research file independent of unregistered research modules.
No declaration from `research/T15/` is used.
-/

noncomputable section

-- copied from research/T10/Spec.lean:46-411 (selected declarations); delete once registered
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

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the `H^s(T³)` norm of a coefficient datum,
with squared component norms summed as prescribed in the paper. -/
def periodicSobolevDataNorm (s : ℝ) (A : PeriodicSobolev s) : ℝ := ‖A‖

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

-- copied from research/T13/Spec.lean:157-313; delete once registered
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

-- copied from research/T16/Spec.lean:43-319; delete once registered
namespace BlowupDensity.T16.Draft

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
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

end BlowupDensity.T16.Draft

namespace BlowupDensity.T17.DraftA

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Draft
open BlowupDensity.T16.Draft
open scoped ContDiff ENNReal Topology

/-! ## The exact rescaled profiles used in the proof -/

/-- The fixed rescaled cylinder supporting the cutoff profile,
`paper/sections/03-torus.tex:245-260`.

This is the literal product of the two cutoff supports, rather than an
unspecified compact cylinder.  `LocalPotentialAPI.theta_compactSupport` and
`eta_compactSupport` make it compact, and its inclusions in
`(-2,2) × ball 0 D.thetaRadius` fix its size independently of `epsilon`. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  tsupport D.η ×ˢ tsupport D.θ

/-- `V_epsilon(z,sigma)=v(x0+epsilon z,T+epsilon^2 sigma)`,
`paper/sections/03-torus.tex:262-271`. -/
def rescaledReferenceProfile (v : SpaceTimeField) (x0 : Space) (T epsilon : ℝ) :
    SpaceTimeField :=
  fun z => v (T + epsilon ^ 2 * z.1, x0 + epsilon • z.2)

/-- The rescaled radial-potential profile `mathcal A_epsilon` of
`paper/sections/03-torus.tex:245-253`, expressed through the potential already
chosen by T16.  Only positive `epsilon` is used below. -/
def rescaledPotentialProfile (D : CutoffData) (x0 : Space) (T epsilon : ℝ) :
    SpaceTimeField :=
  fun z => epsilon⁻¹ • D.potential (T + epsilon ^ 2 * z.1, x0 + epsilon • z.2)

/-- `W_epsilon(z,sigma)=w_epsilon(x0+epsilon z,T+epsilon^2 sigma)`,
the uniformly smooth correction profile of
`paper/sections/03-torus.tex:256-260`.

This is the single-chart profile, written by the displayed cutoff--curl
formula.  It is deliberately not obtained by rescaling the globally periodic
`D.correction`, which would produce infinitely many lattice copies in the
Euclidean `z` variable.  T16's `correction_formula` identifies the two on the
active coordinate chart. -/
def rescaledCorrectionProfile (D : CutoffData) (x0 : Space) (T epsilon : ℝ) :
    SpaceTimeField :=
  fun z => -curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotentialProfile D x0 T epsilon (z.1, y)) z.2

/-- The correction force `H_epsilon` from `eq:H`, with exactly the signs and
advection order of `paper/sections/03-torus.tex:219-223`.

The third summand is `(v . grad) w_epsilon`, the fourth is
`(w_epsilon . grad) v`, and `advection w_epsilon` is
`(w_epsilon . grad) w_epsilon`.  Thus this definition is tied to T16's chosen
`D.correction`; no existentially unrelated force can satisfy the API. -/
def correctionForce (nu : ℝ) (v : SpaceTimeField) (D : CutoffData)
    (epsilon : ℝ) : SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction epsilon) z.1 z.2 -
      nu • spatialLaplacian (D.correction epsilon) z.1 z.2 +
      spatialDerivative (D.correction epsilon) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction epsilon z) +
      advection (D.correction epsilon) z.1 z.2

/-- The bracketed rescaled force in the proof of `eq:derivativebounds`,
`paper/sections/03-torus.tex:262-273`.

The fourth term deliberately differentiates the physical reference at the
physical point: it is the displayed
`epsilon^2 (W_epsilon . grad_x) v(x0+epsilon z,T+epsilon^2 sigma)` term. -/
def rescaledForceBracket (nu : ℝ) (v : SpaceTimeField) (D : CutoffData)
    (x0 : Space) (T epsilon : ℝ) : SpaceTimeField :=
  let V := rescaledReferenceProfile v x0 T epsilon
  let W := rescaledCorrectionProfile D x0 T epsilon
  fun z =>
    temporalDerivative W z.1 z.2 - nu • spatialLaplacian W z.1 z.2 +
      epsilon • spatialDerivative W z.1 z.2 (V z) +
      epsilon ^ 2 • spatialDerivative v
        (T + epsilon ^ 2 * z.1) (x0 + epsilon • z.2) (W z) +
      epsilon • advection W z.1 z.2

/-- Uniform `C-infinity` control of a scale-indexed profile on the literal
fixed cylinder from `paper/sections/03-torus.tex:245-260`.

For every full Frechet derivative order one bound is chosen before `epsilon`,
the point in the cylinder, and all unit directions.  Taking the operator norm
of `iteratedFDeriv` is precisely uniform boundedness of every derivative of
that order and is stronger than listing coordinate multi-indices separately. -/
def UniformlySmoothOnFixedCylinder (D : CutoffData) (epsilon0 : ℝ)
    (F : ℝ → SpaceTimeField) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ epsilon ∈ Ioc (0 : ℝ) epsilon0, ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (F epsilon) z‖ ≤ C

/-- The exact fixed-cylinder facts used in the proof of Lemma
`lem:correction`, `paper/sections/03-torus.tex:245-273`.

This predicate replaces any dependency on the concurrently drafted T15.  Its
fields concern only the rescaled reference, potential, T16 correction, and the
explicit force above.  The force identity is the displayed rescaling formula,
including all three powers of `epsilon`; the two support fields state that the
profiles really live on the named fixed cylinder rather than merely enjoying
local estimates there. -/
structure UniformProfileHypotheses (nu : ℝ) (v : SpaceTimeField)
    (x0 : Space) (T : ℝ) (D : CutoffData) : Prop where
  /-- The rescaled reference fields are uniformly smooth on the fixed
  cylinder; `paper/sections/03-torus.tex:252-254,263`. -/
  reference_uniform :
    UniformlySmoothOnFixedCylinder D D.ε₀
      (rescaledReferenceProfile v x0 T)
  /-- Every fixed-order derivative of `mathcal A_epsilon` is bounded uniformly
  in the scale; `paper/sections/03-torus.tex:247-254`. -/
  potential_uniform :
    UniformlySmoothOnFixedCylinder D D.ε₀
      (rescaledPotentialProfile D x0 T)
  /-- The exact correction profiles are supported in the one fixed cylinder;
  `paper/sections/03-torus.tex:256-260`. -/
  correction_support : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile D x0 T epsilon) ⊆ fixedProfileCylinder D
  /-- The family `W_epsilon` is uniformly smooth there;
  `paper/sections/03-torus.tex:256-260`. -/
  correction_uniform :
    UniformlySmoothOnFixedCylinder D D.ε₀
      (rescaledCorrectionProfile D x0 T)
  /-- The physical force is `epsilon^-2` times the exact bracket in
  `paper/sections/03-torus.tex:266-271`. -/
  force_rescaling : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
    correctionForce nu v D epsilon
        (T + epsilon ^ 2 * z.1, x0 + epsilon • z.2) =
      (epsilon⁻¹) ^ 2 • rescaledForceBracket nu v D x0 T epsilon z
  /-- The bracketed force profile is supported in the same fixed cylinder;
  `paper/sections/03-torus.tex:262-273`. -/
  force_support : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceBracket nu v D x0 T epsilon) ⊆ fixedProfileCylinder D
  /-- The bracket and all of its spatial derivatives are uniformly bounded;
  we record the stronger full-derivative statement used by the endpoint norm
  estimates, `paper/sections/03-torus.tex:262-284`. -/
  force_uniform :
    UniformlySmoothOnFixedCylinder D D.ε₀
      (rescaledForceBracket nu v D x0 T)

/-! ## Periodic mixed Lebesgue norm -/

/-- A path of honest periodic `L^p` representatives for a physical periodic
field.  This is the torus analogue of
`Contracts.V1.Data.IsLebesgueSlicePath`; `paper/sections/01-introduction.tex:134`. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField)
    (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x => f (t, x))

/-- The fail-safe periodic quantity
`L^q(0,infinity;L^p(T^3))` in `eq:Hmixed`,
`paper/sections/03-torus.tex:235-237`.

The infimum is over strongly measurable `Lp` paths.  If no honest path exists
the value is `top`, so a finite upper bound cannot exploit a lower-integral or
measurability junk value. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- The exponent in the first expression of `eq:Hmixed`, with the convention
`1/infinity=0` supplied by `ENNReal.toReal`;
`paper/sections/03-torus.tex:235-237`. -/
def correctionForceExponent (p q : ℝ≥0∞) : ℝ :=
  -2 + 3 / p.toReal + 2 / q.toReal

/-! ## Lemma `lem:correction` -/

/-- Type-valued statement of every clause of Lemma `lem:correction`,
`paper/sections/03-torus.tex:218-285`, for T16's one chosen correction family.

The record is intentionally `Type`-valued: the uniform constants are data
selected before `epsilon`, following the A03/A05/I02 house style, so a consumer
cannot choose a new constant at each scale.  `profiles` is the exact proof
hypothesis from lines 245-273.  The proof parameters make the T16 and T13
dependencies, periodic reference, and single-copy chart geometry explicit
without restating those upstream APIs.

All norm bounds use `ENNReal`, hence an infinite norm cannot satisfy a finite
right-hand side.  The `MemLp` and datum-path fields additionally expose the
honest representatives used by the energy, mixed, and Sobolev norms. -/
structure CorrectionAPI (nu : ℝ) (v U : SpaceTimeField) (K : Set Space)
    (x0 : Space) (r T delta : ℝ) (D : CutoffData)
    (_potential : LocalPotentialAPI v U K x0 r T delta D)
    (_referencePeriodic : IsPeriodicOn univ v)
    (_radiusPos : 0 < r)
    (_chart : closure (Metric.ball x0 r) ⊆ interior fundamentalCube)
    (_localization : LocalizationAPI) where
  /-- The global viscosity is positive; `paper/sections/01-introduction.tex:3`
  and `03-torus.tex:221`. -/
  viscosity_pos : 0 < nu
  /-- Harmless normalization of "sufficiently small": all constants below
  are uniform for `0 < epsilon <= D.epsilon0 <= 1`;
  `paper/sections/03-torus.tex:242`. -/
  eps_le_one : D.ε₀ ≤ 1
  /-- The uniformly smooth profiles on the literal fixed cylinder, exactly as
  used in `paper/sections/03-torus.tex:245-273`.

  Non-vacuity: all profiles are the concrete definitions above, tied to `v`
  and `D.correction`, and the predicate quantifies every derivative order. -/
  profiles : UniformProfileHypotheses nu v x0 T D

  /-- `H_epsilon` is smooth across `T` and after its zero extension;
  `paper/sections/03-torus.tex:225,284`.

  Non-vacuity: global `C-infinity` regularity is asserted for the explicit
  `correctionForce`, so in particular there is no seam at `T`. -/
  force_smooth : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce nu v D epsilon)
  /-- The correction force is periodic in space;
  `paper/sections/03-torus.tex:212,219-225`.

  Non-vacuity: this constrains the same physical lift used in every norm. -/
  force_periodic : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce nu v D epsilon)
  /-- The zero extension vanishes outside the temporal cutoff and outside the
  periodic lift of the scaled spatial cutoff;
  `paper/sections/03-torus.tex:225`.

  Non-vacuity: because a nonzero value belongs to `tsupport`, this inclusion
  is the literal extension-by-zero assertion. -/
  force_support : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce nu v D epsilon) ⊆
      Ioo (T - 2 * epsilon ^ 2) (T + 2 * epsilon ^ 2) ×ˢ
        periodicSet (Metric.ball x0 (epsilon * D.θRadius))
  /-- The constant in "spatial support has volume `O(epsilon^3)`";
  `paper/sections/03-torus.tex:225`. -/
  spatialVolumeConst : ℝ
  /-- Positivity prevents a negative big-O witness. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- At every time, the Haar volume of the support on the unit torus is
  `O(epsilon^3)`; `paper/sections/03-torus.tex:225`.

  Non-vacuity: Euclidean support of a periodic lift is infinite, so the support
  is correctly measured after `torusLift`, using normalized Haar measure. -/
  force_spatial_volume : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    periodicTorusMeasure
        (tsupport (torusLift (fun x => correctionForce nu v D epsilon (t, x)))) ≤
      ENNReal.ofReal (spatialVolumeConst * epsilon ^ 3)
  /-- The temporal support has length at most `4 epsilon^2`, hence
  `O(epsilon^2)`; `paper/sections/03-torus.tex:225`.

  Non-vacuity: this measures the projection of the concrete spacetime
  `tsupport`, not an arbitrary containing interval. -/
  force_time_length : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    volume (Prod.fst '' tsupport (correctionForce nu v D epsilon)) ≤
      ENNReal.ofReal (4 * epsilon ^ 2)

  /-- The constants `C_{beta,j}` in the first half of
  `eq:derivativebounds`; `paper/sections/03-torus.tex:226-228`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- The derivative constants are nonnegative. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `|partial_t^j partial_x^beta w_epsilon| <=
  C_{beta,j} epsilon^(-2j-|beta|)`;
  `paper/sections/03-torus.tex:226-228`.

  The statement allows arbitrary unit spatial directions; coordinate
  directions recover every multi-index `beta` with `m=|beta|`.
  Non-vacuity: the field is T16's concrete `D.correction epsilon`, and one
  constant controls all points and admissible scales. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction epsilon) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (epsilon⁻¹) ^ (2 * j + m)

  /-- The constants `C_beta` in the force half of
  `eq:derivativebounds`; `paper/sections/03-torus.tex:229-230`. -/
  forceDerivConst : ℕ → ℝ
  /-- The force derivative constants are nonnegative. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `|partial_x^beta H_epsilon| <=
  C_beta epsilon^(-2-|beta|)`;
  `paper/sections/03-torus.tex:229-230`.

  Non-vacuity: `m=0` is the actual amplitude bound used for `eq:Hmixed`; all
  larger `m` constrain the explicit force's spatial derivatives. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce nu v D epsilon) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (epsilon⁻¹) ^ (2 + m)

  /-- The `C` in `eq:wE`, `paper/sections/03-torus.tex:233-234`. -/
  energyConst : ℝ
  /-- The energy constant is nonnegative. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- Every correction slice is an honest periodic `L2` function, as required
  by the first summand of `E_T`.

  Non-vacuity: this rules out relying on a lower-integral value for a
  nonmeasurable slice. -/
  correction_slice_memLp : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction epsilon (t, x))) 2 periodicTorusMeasure
  /-- The same honest `L2` condition for the full spatial gradient in the
  second summand of `E_T`. -/
  correction_gradient_memLp : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction epsilon) t x))
      2 periodicTorusMeasure
  /-- `||w_epsilon||_{E_T} <= C epsilon^(3/2)`, `eq:wE`;
  `paper/sections/03-torus.tex:233-234,275-280`.

  Non-vacuity: `energyENormT` is `ENNReal`-valued and the right side is finite,
  so an infinite energy cannot satisfy this field. -/
  correction_energy_bound : ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT T (D.correction epsilon) ≤
      ENNReal.ofReal (energyConst * epsilon ^ ((3 : ℝ) / 2))

  /-- The constants `C_{p,q}` of `eq:Hmixed`, chosen before `epsilon`;
  `paper/sections/03-torus.tex:235-237,242`. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- The mixed-norm constants are nonnegative throughout the paper's range. -/
  mixedConst_nonneg : ∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst p q
  /-- Every force slice is an honest periodic `L^p` function, including
  `p=infinity`; `paper/sections/03-torus.tex:235-237,281-282`.

  Non-vacuity: this is the explicit `MemLp` premise behind the inner norm. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce nu v D epsilon (t, x)))
        p periodicTorusMeasure
  /-- The two exponents displayed as equal in `eq:Hmixed` really agree;
  `paper/sections/03-torus.tex:235-237`.

  Non-vacuity: this pins the explicit `-2+3/p+2/q` rate to the already
  registered Section 4 convention `alpha(p,q)+1`, including both endpoints. -/
  force_exponent_identity : ∀ p q : ℝ≥0∞,
    correctionForceExponent p q = alpha p q + 1
  /-- `||H_epsilon||_{L^q_t L^p_x} <=
  C_{p,q} epsilon^(-2+3/p+2/q)`, and hence the equal
  `C_{p,q} epsilon^(alpha(p,q)+1)` rate, `eq:Hmixed`;
  `paper/sections/03-torus.tex:235-237,281-282`.

  Quantifying `p,q` in `ENNReal` includes `infinity`; the two `Fact` premises
  are exactly `1 <= p,q`, while the upper inequalities are automatic.
  Non-vacuity: `mixedLebesgueENormT` is an infimum over honest strongly
  measurable `Lp` paths and is `top` if none exists. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce nu v D epsilon) ≤
        ENNReal.ofReal
          (mixedConst p q * epsilon ^ correctionForceExponent p q)

  /-- The constants `C_s` in `eq:HHs`, selected before `epsilon`;
  `paper/sections/03-torus.tex:238-240,242`. -/
  sobolevConst : ℝ → ℝ
  /-- The Sobolev constants are nonnegative for `0 <= s <= 1`. -/
  sobolevConst_nonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ sobolevConst s
  /-- An honest strongly measurable periodic Sobolev datum path represents
  `H_epsilon` for every order used in `eq:HHs`.

  Non-vacuity: this exposes the witness over which `forceSobolevENormT` takes
  its infimum, including T10's Haar-integrability conjunct on every slice. -/
  force_sobolev_path : ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
      ∃ G : ℝ → PeriodicSobolev s,
        IsPeriodicSobolevPath s (correctionForce nu v D epsilon) G ∧
          AEStronglyMeasurable G forceTimeMeasure
  /-- `||H_epsilon||_{L^1_t H^s_x} <=
  C_s (epsilon^(3/2)+epsilon^(3/2-s))` for `0 <= s <= 1`, `eq:HHs`;
  `paper/sections/03-torus.tex:238-240,284`.

  Non-vacuity: the norm is T10's fail-safe Fourier-datum norm, and the T13
  localization certificate is an explicit structure parameter.  Thus this
  field cannot silently use a whole-space norm or omit the endpoint transfer. -/
  force_sobolev_bound : ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ epsilon ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce nu v D epsilon) ≤
        ENNReal.ofReal
          (sobolevConst s *
            (epsilon ^ ((3 : ℝ) / 2) + epsilon ^ ((3 : ℝ) / 2 - s)))

end BlowupDensity.T17.DraftA
