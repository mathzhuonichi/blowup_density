import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T13 reconciled specification: uniform localization of fractional norms

This statement-only file specifies `lem:localization` from
`paper/sections/03-torus.tex:22-98`.  Physical fields are real vector fields on
`Space = ℝ³`; the torus is represented by unit-periodic fields and T10's real
Fourier-data norms.

Files below `research/` are not Lean modules, so this file cannot import
`research/T10/Spec.lean`.  It instead imports the same public modules and copies
only the T10 declarations needed by T13, unchanged and in T10's namespace.
This temporary copy is explicitly delimited below.
-/

noncomputable section

/- copied verbatim from research/T10/Spec.lean:46-203 (selected declarations);
must stay identical until T01.torus_data is registered -/
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
  IsPeriodicSpatial z ∧
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
  IsPeriodicSpatial z ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Ḣ^s(T³)` extended norm of a mean-zero physical field.  It is the infimum over
homogeneous real data and is `⊤` when no datum exists. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

end BlowupDensity.T10.Draft
/- end verbatim T10 copy -/

namespace BlowupDensity.T13.Spec

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

end BlowupDensity.T13.Spec
