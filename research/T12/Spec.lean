import Contracts.V1.Data
import Contracts.V1.GradientL6
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T12 reconciled specification: mean-zero periodic Sobolev calculus

This statement-only file specifies the torus halves of `lem:calculus` and
`lem:critical-embeddings` from
`paper/sections/appendix-a-local-theory.tex:7-27`,
`paper/sections/appendix-b-embeddings.tex:8-38,85-110`, and their uses at
`paper/sections/03-torus.tex:467-503`.

Files below `research/` are not Lean modules, so this file cannot import
`research/T10/Spec.lean`.  As required by the T13 copy policy, it imports the
same public modules and copies only the amended T10 declarations needed here,
unchanged and in T10's namespace.  T12's scalar datum is the exact scalar mirror
of that vector datum.  All norms are `ℝ≥0∞`-valued and no inequality passes
through `.toReal`.
-/

noncomputable section

/- copied verbatim from research/T10/Spec.lean:46-212 (selected declarations,
including lead amendment 1 at lines 125-144 and 194-212);
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

end BlowupDensity.T10.Draft
/- end verbatim T10 copy -/

namespace BlowupDensity.T12.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
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
