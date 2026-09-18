import Contracts.V1.TorusData
import Contracts.V1.GradientL6
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Contract: the mean-zero periodic Sobolev calculus of T12

This contract registers the reconciled T12 statement
(`research/T12/Spec.lean:281-478`) of the torus halves of `lem:calculus` and
`lem:critical-embeddings`
(`paper/sections/appendix-a-local-theory.tex:7-27`,
`paper/sections/appendix-b-embeddings.tex:8-38,85-110`) together with the
mean-zero order-two comparison used at `paper/sections/03-torus.tex:467-503`.

The periodic data layer is the already registered `T01.torus_data` vocabulary
and is imported rather than copied.  Only the declarations the Spec itself
writes out are restated here, token-for-token; each one is guarded by a `rfl`
bridge in `Bindings/MeanZeroCalculus.lean`.  The three derivative spellings are
in addition checked below to be definitionally the registered `A05.gradient_l6`
ones, exactly as `research/T12/Spec.lean:534-546` does.

All norms are `ℝ≥0∞`-valued; no inequality passes through `.toReal`.
-/

noncomputable section
namespace BlowupDensity.Contracts.V1.MeanZeroCalculus
open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators
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


/-- `research/T12/Spec.lean` statement form: the reconciled T12 API is
inhabited. -/
def meanZeroCalculusStatement : Prop := Nonempty MeanZeroSobolevCalculusAPI

end BlowupDensity.Contracts.V1.MeanZeroCalculus
