import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Contract: the periodic data layer on the unit three-torus

This contract registers the T10 data layer used by the first Section 3
contract.  Physical fields are unit-periodic functions on `R^3`, while
Sobolev data are weighted Fourier coefficients indexed by `Z^3`.  The ten
fields of `TorusDataAPI` are the proved datum uniqueness/reality, Parseval,
quotient-lift, mean decomposition, zero-mode, and Leray facts selected in
`research/T10/RECONCILIATION.md`.

Only definitions through `IsPeriodicReweight`, together with `IsPeriodicOn`,
are registered here.  The solution-class layer (`IsPeriodicSobolevPath`, force
norms and classes, pressure gauge, `ClassicalSolutionT`, lifespan, breakdown,
density, and energy norms) is deliberately deferred to the T11 registration;
its structures require the fieldwise conversions mandated by the contract
structure exception.

The torus lift, Fourier coefficient, torus/frequency types, and Haar measure
are restated here because `NSFormalization.Paper1.TorusCube` is not a permitted
contract import.  `Bindings.TorusData` checks every restatement against the
canonical T10 implementation by definitional equality.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TorusData

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

/-! ## 1. Physical and coefficient conventions -/

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
`NSFormalization.Paper1.periodicFourierCoeff`, restated so the contract needs
no local implementation import. -/
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
`z`. -/
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

/-! ## 2. Means, the zero mode, and homogeneous periodic data -/

/-- `03-torus.tex:395-401`: the normalized spatial mean of a real vector
field on the unit torus. -/
def meanT (z : SpatialField) : Space :=
  ∫ y : PeriodicTorus, torusLift z y ∂periodicTorusMeasure

/-- `03-torus.tex:395-401`: the spatially constant part of a periodic field. -/
def constantPartT (z : SpatialField) : SpatialField := fun _ ↦ meanT z

/-- `03-torus.tex:395-401`: `z - ∫_T³ z`, the mean-free part of a periodic
field. -/
def meanZeroPartT (z : SpatialField) : SpatialField := fun x ↦ z x - meanT z

/-- `03-torus.tex:395-401`: the canonical constant/mean-free decomposition,
recorded as the ordered pair `(x ↦ meanT z, x ↦ z x - meanT z)`. -/
def meanDecompositionT (z : SpatialField) : SpatialField × SpatialField :=
  (constantPartT z, meanZeroPartT z)

/-- `01-introduction.tex:105-108` and `03-torus.tex:395-411`: the mean-zero
closed coefficient subspace, characterized exactly by vanishing at `k = 0`.
The weight at zero is one, so this condition is independent of `s`. -/
def meanZeroPeriodicSobolev (s : ℝ) : Submodule ℝ (PeriodicSobolev s) where
  carrier := {A | ∀ i : Fin 3, A.1 i 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB i
    change A.1 i 0 + B.1 i 0 = 0
    rw [hA i, hB i, add_zero]
  smul_mem' := by
    intro r A hA i
    change (r : ℂ) * A.1 i 0 = 0
    rw [hA i, mul_zero]

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
Haar integrability of the lift (lead amendment, `RECONCILIATION.md` §5), zero
mean, then `∀ i : Fin 3, ∀ k : PeriodicFrequency`. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Ḣ^s(T³)` extended norm of a mean-zero physical field. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/-- `02-preliminaries.tex:76-80`: the unit-period derivative symbol
`2π i k_j`. -/
def periodicDerivativeSymbol (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (2 * Real.pi * Complex.I) * (k j : ℂ)

/-- `02-preliminaries.tex:76-80`: coefficient-side solenoidality. -/
def IsSolenoidalPeriodicDatum {s : ℝ} (A : PeriodicSobolev s) : Prop :=
  ∀ k : PeriodicFrequency,
    ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k = 0

/-- `02-preliminaries.tex:76-80`: the periodic Leray projector applied to a
weighted datum. -/
def periodicLeray (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then A.1 i k
  else
    A.1 i k -
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * A.1 j k

/-- `02-preliminaries.tex:76-80`: `B` is the same-order real Sobolev datum
obtained from `A` by the periodic Leray projector. -/
def IsPeriodicLerayDatum {s : ℝ} (A B : PeriodicSobolev s) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k = periodicLeray s A i k

/-- `01-introduction.tex:83-84` and `02-preliminaries.tex:79-80`: `B` is the
same Fourier datum as `A`, transported from order `s` to order `t`. -/
def IsPeriodicReweight (s t : ℝ) (A : PeriodicSobolev s)
    (B : PeriodicSobolev t) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    B.1 i k = (periodicFrequencyWeight k) ^ ((t - s) / 2) • A.1 i k

/-! ## 3. Reconciled consumer-facing facts -/

/-- Basic proved facts of the periodic data layer selected by
`research/T10/RECONCILIATION.md`.  Every field is a concrete mathematical
statement over the definitions above; there is no unspecified proposition
parameter and no placeholder field. -/
structure TorusDataAPI : Prop where
  /-- `01-introduction.tex:83-103`: weighted Fourier data representing one
  physical periodic field are unique.

  Exact quantifier order: `∀ s, ∀ z, ∀ A, ∀ B`, followed by the two datum
  hypotheses.

  Non-vacuity: the conclusion is equality in the complete real coefficient
  carrier, not equality of an auxiliary proposition or an existential shadow. -/
  datum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : PeriodicSobolev s),
      IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B

  /-- `02-preliminaries.tex:72-73`: an `IsPeriodicDatum` has the manuscript's
  conjugate-reflection symmetry.

  Exact quantifier order: `∀ s, ∀ z, ∀ A`, datum membership, then
  `∀ i : Fin 3, ∀ k : PeriodicFrequency`.

  Non-vacuity: this exposes an equality of actual complex Fourier
  coefficients at `k` and `-k`; it is the public fact that the datum lands in
  the real closed submodule. -/
  datum_real :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i (-k) = star (A.1 i k)

  /-- `01-introduction.tex:83-103`: vector Parseval in the forward direction.

  Exact quantifier order: `∀ z, ∀ A`, followed by the order-zero datum
  hypothesis, then physical `L²` membership of the lift (lead amendment,
  `RECONCILIATION.md` §5: the datum alone only gives `L¹`, and the identity
  is the paper's `L²` Parseval).

  Non-vacuity: it equates the extended norm of a concrete coefficient datum
  with the physical Haar `L²(T³)` norm, including the normalization constant. -/
  parseval_forward :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure

  /-- `01-introduction.tex:83-103`: vector Parseval in the reverse direction.

  Exact quantifier order: `∀ z`, physical periodicity, then physical `L²`
  membership, then `∃ A`.

  Non-vacuity: the conclusion supplies an inhabitant of the real complete
  coefficient carrier whose coefficients are pinned by `IsPeriodicDatum`. -/
  parseval_backward :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      MemLp (torusLift z) 2 periodicTorusMeasure →
        ∃ A : PeriodicSobolev 0, IsPeriodicDatum 0 z A

  /-- `03-torus.tex:2-4` and the physical representation (P): lifting to the
  quotient torus is injective on unit-periodic physical vector fields.

  Exact quantifier order: `∀ z, ∀ w`, the two periodicity hypotheses, then
  equality of their torus lifts.

  Non-vacuity: the conclusion is pointwise equality of the original physical
  fields, so no information is lost by the chosen `(0,1]³` representative. -/
  torusLift_injective :
    ∀ z w : SpatialField, IsPeriodicSpatial z → IsPeriodicSpatial w →
      torusLift z = torusLift w → z = w

  /-- `03-torus.tex:2-4` and the physical representation (P): every torus
  vector field has a unit-periodic physical representative.

  Exact quantifier order: `∀ Z : PeriodicTorus → Space`, then `∃ z` carrying
  periodicity and exact lift equality.

  Non-vacuity: the witness is a physical `Space → Space` field, and its lift
  must equal the caller's entire torus function. -/
  torusLift_surjective :
    ∀ Z : PeriodicTorus → Space,
      ∃ z : SpatialField, IsPeriodicSpatial z ∧ torusLift z = Z

  /-- `03-torus.tex:395-411`: the normalized mean gives the literal
  constant/mean-zero decomposition.

  Exact quantifier order: `∀ z`, periodicity, Haar integrability, then the
  reconstruction identity and zero-mean conclusion.

  Non-vacuity: the field is reconstructed pointwise for every `x`, and the
  second conjunct is the actual Haar-integral equation `meanT = 0`. -/
  mean_decomposition :
    ∀ z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (∀ x : Space, constantPartT z x + meanZeroPartT z x = z x) ∧
          IsMeanZeroT (meanZeroPartT z)

  /-- `01-introduction.tex:105-109` and `03-torus.tex:395-411`: removing the
  mean removes exactly the zero Fourier mode at every Sobolev order.

  Exact quantifier order: `∀ s, ∀ z, ∀ A`, the datum hypothesis, then `∃ B`
  with both its physical realization and zero-mode membership.

  Non-vacuity: the existential datum represents the concrete field
  `meanZeroPartT z` and belongs to the concrete submodule
  `meanZeroPeriodicSobolev s`. -/
  meanZero_datum :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s

  /-- `02-preliminaries.tex:76-80`: the coefficient formula defines the
  periodic Leray projection, which is a contraction and has solenoidal range.

  Exact quantifier order: `∀ s, ∀ A`, then `∃ B`; the returned datum carries
  the graph equation, norm bound, and solenoidality together.

  Non-vacuity: `B` is an element of the same complete real Hilbert carrier as
  `A`, not merely a coefficient function outside `ℓ²`. -/
  leray_exists_contraction :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B

  /-- `02-preliminaries.tex:76-80`: the periodic Leray map is idempotent.

  Exact quantifier order: `∀ s, ∀ A, ∀ B, ∀ C`, followed by the graph
  equations `B=P A` and `C=P B`.

  Non-vacuity: the conclusion identifies two concrete same-order data, and so
  states projector idempotence rather than only coefficientwise solenoidality. -/
  leray_projector :
    ∀ (s : ℝ) (A B C : PeriodicSobolev s),
      IsPeriodicLerayDatum A B → IsPeriodicLerayDatum B C → C = B

end BlowupDensity.Contracts.V1.TorusData
