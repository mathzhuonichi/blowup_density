import NSFormalization.Paper1.TorusCube

/-!
# T12 draft A: mean-zero periodic Sobolev calculus

Double-blind statement draft for node T12.  The physical layer consists of
unit-periodic fields on `R³`; the analytic layer consists of weighted
`lp (Fin 3 → ℤ) 2` Fourier data, as required by
`collaboration/SECTION3_PLAN.md` §1.

Everything before `MeanZeroSobolevCalculusAPI` is a local specification copy.
It **needs registration and alignment with T10**.  In particular, a reconciled
contract should import T10's canonical names and retain `rfl` bridges for every
definition copied here.

The norms are `ℝ≥0∞`-valued and never pass through `ENNReal.toReal`.  An absent
Sobolev datum or Fourier-multiplier representative therefore gives `⊤`, so none
of the displayed bounds can become true by discarding an infinite quantity.
-/

noncomputable section

namespace BlowupDensity.Research.T12.DraftA

open MeasureTheory
open NSFormalization.Paper1 (periodicFourierCoeff periodicTorusMeasure torusLift)
open scoped ContDiff ENNReal

/-! ## T10-facing local definitions (needs registration / T10 alignment) -/

/-- `01-introduction.tex:9-10`: physical space is `R³`, while periodicity is a
property of fields on it.  Needs registration / T10 alignment. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- `01-introduction.tex:9-10`: the unit three-torus used only for integration
of physical periodic fields.  Needs registration / T10 alignment. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

/-- `01-introduction.tex:83-89`: Fourier frequencies on the unit torus.
Needs registration / T10 alignment. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- A real scalar field on the physical `R³` layer. -/
abbrev ScalarField := Space → ℝ

/-- A real three-vector field on the physical `R³` layer. -/
abbrev SpatialField := Space → Space

/-- `01-introduction.tex:10`: unit periodicity in each coordinate, kept as a
property of an `R³` field rather than changing its carrier to a quotient.
Needs registration / T10 alignment. -/
def IsUnitPeriodic {E : Type*} (f : Space → E) : Prop :=
  ∀ (j : Fin 3) (x : Space),
    f (x + EuclideanSpace.single j 1) = f x

/-- `01-introduction.tex:83-84`: `|k|²` for `k ∈ Z³`. -/
def frequencySq (k : PeriodicFrequency) : ℝ :=
  ∑ j : Fin 3, (k j : ℝ) ^ 2

/-- `01-introduction.tex:83-84`: `4π²|k|² = |2πk|²`. -/
def angularFrequencySq (k : PeriodicFrequency) : ℝ :=
  4 * Real.pi ^ 2 * frequencySq k

/-- `01-introduction.tex:83-84`: the square-root Sobolev weight
`(1 + 4π²|k|²)^(s/2)` multiplying a coefficient before its `lp 2` norm is
taken.  Needs registration / T10 alignment. -/
def inhomogeneousDatumWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  Real.rpow (1 + angularFrequencySq k) (s / 2)

/-- `01-introduction.tex:105-107`: the homogeneous datum weight
`|2πk|^s = (4π²|k|²)^(s/2)`, with the omitted zero mode represented by zero.
Needs registration / T10 alignment. -/
def homogeneousDatumWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else Real.rpow (angularFrequencySq k) (s / 2)

/-- `01-introduction.tex:89`: the unit-torus Fourier coefficient of a real
physical scalar field.  Needs registration / T10 alignment. -/
def scalarFourierCoeff (f : ScalarField) (k : PeriodicFrequency) : ℂ :=
  periodicFourierCoeff (fun x => (f x : ℂ)) k

/-- `01-introduction.tex:89,103`: the `i`-th component Fourier coefficient of a
real physical vector field.  Needs registration / T10 alignment. -/
def vectorFourierCoeff (v : SpatialField) (i : Fin 3)
    (k : PeriodicFrequency) : ℂ :=
  periodicFourierCoeff (fun x => (v x i : ℂ)) k

/-- `SECTION3_PLAN.md` §1: the scalar coefficient side is literally
`lp (Fin 3 → ℤ) 2`.  A datum below stores the *weighted* coefficients here.
Needs registration / T10 alignment. -/
abbrev PeriodicCoefficientLp := lp (fun _ : PeriodicFrequency => ℂ) 2

/-- `01-introduction.tex:103`: three scalar `lp 2` data assembled with the
Euclidean `PiLp 2` norm.  Needs registration / T10 alignment. -/
abbrev PeriodicVectorDatum := PiLp 2 (fun _ : Fin 3 => PeriodicCoefficientLp)

/-- `01-introduction.tex:83-97`: `A` is the order-`s` inhomogeneous Fourier
datum of the physical scalar field `f`.  This is the periodic counterpart of
`Contracts.V1.TameProduct.IsScalarSobolevDatum`.
Needs registration / T10 alignment. -/
def IsPeriodicScalarSobolevDatum (s : ℝ) (f : ScalarField)
    (A : PeriodicCoefficientLp) : Prop :=
  ∀ k : PeriodicFrequency,
    A k = (inhomogeneousDatumWeight s k : ℂ) * scalarFourierCoeff f k

/-- `01-introduction.tex:83-103`: vector version of the weighted periodic
Sobolev datum.  Needs registration / T10 alignment. -/
def IsPeriodicSobolevDatum (s : ℝ) (v : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    A i k = (inhomogeneousDatumWeight s k : ℂ) * vectorFourierCoeff v i k

/-- `01-introduction.tex:83-97`, `‖f‖_{H^s(T³)}` for a physical scalar field,
totalized to `⊤` when no weighted `lp 2` datum exists.
Needs registration / T10 alignment. -/
def periodicScalarSobolevENorm (s : ℝ) (f : ScalarField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicCoefficientLp // IsPeriodicScalarSobolevDatum s f A}, ‖A.1‖ₑ

/-- `01-introduction.tex:83-103`, `‖v‖_{H^s(T³)}` for a physical vector field,
with squared component norms summed by `PiLp 2`.
Needs registration / T10 alignment. -/
def periodicSobolevENorm (s : ℝ) (v : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicSobolevDatum s v A}, ‖A.1‖ₑ

/-- `01-introduction.tex:105-107`: homogeneous weighted datum of a mean-zero
periodic vector field.  The zero coefficient is deliberately omitted by
`homogeneousDatumWeight`; mean zero is a separate predicate below.
Needs registration / T10 alignment. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (v : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    A i k = (homogeneousDatumWeight s k : ℂ) * vectorFourierCoeff v i k

/-- `01-introduction.tex:105-109`, `‖v‖_{Ḣ^s(T³)}` as a weighted `lp 2` norm,
totalized to `⊤`.  Needs registration / T10 alignment. -/
def periodicHomogeneousENorm (s : ℝ) (v : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicHomogeneousDatum s v A}, ‖A.1‖ₑ

/-- `01-introduction.tex:106-107` and `appendix-b-embeddings.tex:20-22`:
mean zero means exactly that every component's `k = 0` coefficient vanishes.
Needs registration / T10 alignment. -/
def IsMeanZero (v : SpatialField) : Prop :=
  ∀ i : Fin 3, vectorFourierCoeff v i 0 = 0

/-- A genuine scalar `L²(T³)` representative on the physical periodic layer.
The `L²` condition prevents totalized Fourier integrals from manufacturing a
spurious zero datum.  Needs registration / T10 alignment. -/
def MemPeriodicScalar (f : ScalarField) : Prop :=
  IsUnitPeriodic f ∧ MemLp (torusLift f) 2 periodicTorusMeasure

/-- A genuine vector `L²(T³)` representative on the physical periodic layer.
For the positive homogeneous orders in T12, the paper's spectral gap supplies
this `L²` representative from the homogeneous datum.
Needs registration / T10 alignment. -/
def MemPeriodicVector (v : SpatialField) : Prop :=
  IsUnitPeriodic v ∧ MemLp (torusLift v) 2 periodicTorusMeasure

/-- The scalar `H^m(T³)` class on which `eq:Rproduct` is stated.
Needs registration / T10 alignment. -/
def MemPeriodicHmScalar (m : ℕ) (f : ScalarField) : Prop :=
  MemPeriodicScalar f ∧ periodicScalarSobolevENorm (m : ℝ) f ≠ ⊤

/-- The vector `H^m(T³)` class used by the bounded-representative clause.
Needs registration / T10 alignment. -/
def MemPeriodicHmVector (m : ℕ) (v : SpatialField) : Prop :=
  MemPeriodicVector v ∧ periodicSobolevENorm (m : ℝ) v ≠ ⊤

/-- `01-introduction.tex:104`: the physical scalar `L^p(T³)` norm.
Needs registration / T10 alignment. -/
def torusScalarENorm (p : ℝ≥0∞) (f : ScalarField) : ℝ≥0∞ :=
  eLpNorm (torusLift f) p periodicTorusMeasure

/-- `01-introduction.tex:103-104`: the physical vector `L^p(T³)` norm.
Needs registration / T10 alignment. -/
def torusVectorENorm (p : ℝ≥0∞) (v : SpatialField) : ℝ≥0∞ :=
  eLpNorm (torusLift v) p periodicTorusMeasure

/-! The next three realization predicates spell weak derivatives, `Λ`, and
`Δ` by their unit-torus Fourier multipliers.  They therefore apply to the
periodic distributions of `appendix-b-embeddings.tex:20-27`, rather than only
to classically differentiable fields. -/

/-- Fourier realization of the three weak coordinate derivatives of `v`.
`D j` has multiplier `2π i k_j`.  Needs registration / T10 alignment. -/
def IsPeriodicGradient (v : SpatialField) (D : Fin 3 → SpatialField) : Prop :=
  ∀ j : Fin 3,
    MemPeriodicVector (D j) ∧
      ∀ (i : Fin 3) (k : PeriodicFrequency),
        vectorFourierCoeff (D j) i k =
          (((2 * Real.pi * (k j : ℝ) : ℝ) : ℂ) * Complex.I) *
            vectorFourierCoeff v i k

/-- The Frobenius `L^p` norm of a gradient represented by its three columns.
The infimum is independent of the representative because integrable periodic
fields with identical Fourier coefficients agree almost everywhere.
Needs registration / T10 alignment. -/
def periodicGradientENorm (p : ℝ≥0∞) (v : SpatialField) : ℝ≥0∞ :=
  ⨅ D : {D : Fin 3 → SpatialField // IsPeriodicGradient v D},
    eLpNorm
      (fun z : PeriodicTorus =>
        WithLp.toLp 2 (fun j : Fin 3 => torusLift (D.1 j) z))
      p periodicTorusMeasure

/-- `02-preliminaries.tex:51` and `appendix-b-embeddings.tex:8-9`: Fourier
realization of `Λv = (-Δ)^(1/2)v`, with symbol `2π|k|`.
Needs registration / T10 alignment. -/
def IsPeriodicLambda (v w : SpatialField) : Prop :=
  MemPeriodicVector w ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      vectorFourierCoeff w i k =
        ((Real.sqrt (angularFrequencySq k) : ℝ) : ℂ) * vectorFourierCoeff v i k

/-- The physical `L^p(T³)` norm of `Λv`, totalized to `⊤` when no representative
exists.  Needs registration / T10 alignment. -/
def periodicLambdaENorm (p : ℝ≥0∞) (v : SpatialField) : ℝ≥0∞ :=
  ⨅ w : {w : SpatialField // IsPeriodicLambda v w}, torusVectorENorm p w.1

/-- Fourier realization of the componentwise Laplacian, whose multiplier is
`-4π²|k|²`.  Needs registration / T10 alignment. -/
def IsPeriodicLaplacian (v w : SpatialField) : Prop :=
  MemPeriodicVector w ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      vectorFourierCoeff w i k =
        ((-angularFrequencySq k : ℝ) : ℂ) * vectorFourierCoeff v i k

/-- The physical `L^p(T³)` norm of `Δv`, totalized to `⊤` when no representative
exists.  Needs registration / T10 alignment. -/
def periodicLaplacianENorm (p : ℝ≥0∞) (v : SpatialField) : ℝ≥0∞ :=
  ⨅ w : {w : SpatialField // IsPeriodicLaplacian v w}, torusVectorENorm p w.1

/-! ## T12 statement -/

/-- The constants of node T12.  They are separated from the `Prop`-valued API
because Lean's proof irrelevance forbids data-valued fields directly inside a
structure in `Prop`.  Passing this bundle to `MeanZeroSobolevCalculusAPI`
still chooses every constant before any field quantified by an inequality.

This is the Lean form of `appendix-b-embeddings.tex:109-110`: dependence is
only on the fixed exponents, unit torus, and norm conventions, never on a
field or its frequency support. -/
structure MeanZeroSobolevCalculusConstants where
  /-- `appendix-a-local-theory.tex:9-11` eq:Rproduct: the constant `C_m`, fixed
  for each integer `m` before the factors are quantified. -/
  Cproduct : ℕ → ℝ
  /-- `appendix-a-local-theory.tex:12` eq:Rproduct: the universal constant in
  `H²(T³) ↪ L∞(T³)`. -/
  Cinfty : ℝ
  /-- `appendix-b-embeddings.tex:29`: the universal mean-zero critical
  `Ḣ^(1/2)(T³) ↪ L³(T³)` constant. -/
  CcriticalHalf : ℝ
  /-- `appendix-b-embeddings.tex:30-31`: the universal constant serving the
  combined `L³` bounds for `∇v` and `Λv`. -/
  CcriticalThreeHalves : ℝ
  /-- `appendix-b-embeddings.tex:32`: the universal gradient-`L⁶` constant. -/
  Csix : ℝ
  /-- `03-torus.tex:492-494`: the universal mean-zero comparison constant in
  `‖v‖_{H²} ≤ C‖Δv‖₂`. -/
  CHtwo : ℝ
  /-- `02-preliminaries.tex:52-54` and `appendix-b-embeddings.tex:85-90`: the
  spectral-gap norm-equivalence constant at each nonnegative order. -/
  Cgap : ℝ → ℝ

/-- Node T12: the torus half of Lemma A.1 and the mean-zero torus half of
Lemma B.1, together with the mean-zero `H²`/Laplacian comparison used in the
continuation step of Proposition 3.7.  The constants bundle is an explicit
parameter because a `Prop`-valued Lean structure may contain proofs only. -/
structure MeanZeroSobolevCalculusAPI
    (K : MeanZeroSobolevCalculusConstants) : Prop where
  /-- `appendix-a-local-theory.tex:10`: positivity of the tame-product
  constants. -/
  Cproduct_pos : ∀ m : ℕ, 0 < K.Cproduct m
  /-- `appendix-a-local-theory.tex:12`: positivity of the
  `H²(T³) ↪ L∞(T³)` constant. -/
  Cinfty_pos : 0 < K.Cinfty
  /-- `appendix-b-embeddings.tex:12-17,29`: positivity of the
  order-one-half critical constant. -/
  CcriticalHalf_pos : 0 < K.CcriticalHalf
  /-- `appendix-b-embeddings.tex:12-17,30-31`: positivity of the
  order-three-halves critical constant. -/
  CcriticalThreeHalves_pos : 0 < K.CcriticalThreeHalves
  /-- `appendix-b-embeddings.tex:12-17,32`: positivity of the
  gradient-`L⁶` constant. -/
  Csix_pos : 0 < K.Csix
  /-- `03-torus.tex:492-494`: positivity of the mean-zero
  `H²`/Laplacian constant. -/
  CHtwo_pos : 0 < K.CHtwo
  /-- `appendix-b-embeddings.tex:85-90`: positivity of the spectral-gap
  constants. -/
  Cgap_pos : ∀ s : ℝ, 0 ≤ s → 0 < K.Cgap s

  /-- `appendix-a-local-theory.tex:9-11` eq:Rproduct, torus clause.  The
  quantifier order is `m`, its lower bound, the two factors, then their `H^m`
  membership; `Cproduct m` was already chosen above. -/
  tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ f g : ScalarField,
      MemPeriodicHmScalar m f → MemPeriodicHmScalar m g →
        periodicScalarSobolevENorm (m : ℝ) (fun x => f x * g x) ≤
          ENNReal.ofReal (K.Cproduct m) *
            (periodicScalarSobolevENorm 2 f * periodicScalarSobolevENorm (m : ℝ) g +
              periodicScalarSobolevENorm 2 g * periodicScalarSobolevENorm (m : ℝ) f)

  /-- `appendix-a-local-theory.tex:12` eq:Rproduct, second clause:
  `‖v‖∞ ≤ C‖v‖_{H²}` on the unit torus.  No mean-zero hypothesis occurs in
  the paper for this inhomogeneous embedding. -/
  boundedRepresentative :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      torusVectorENorm ⊤ v ≤
        ENNReal.ofReal K.Cinfty * periodicSobolevENorm 2 v

  /-- `appendix-b-embeddings.tex:20-29` eq:critical-derived, first line:
  `‖v‖₃ ≤ C‖v‖_{Ḣ^(1/2)}`.  The mean-zero hypothesis is essential on the
  torus (`:20-22`), and finiteness matches `:26-27`. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemPeriodicVector v → IsMeanZero v →
      periodicHomogeneousENorm (1 / 2) v ≠ ⊤ →
        torusVectorENorm 3 v ≤
          ENNReal.ofReal K.CcriticalHalf * periodicHomogeneousENorm (1 / 2) v

  /-- `appendix-b-embeddings.tex:26-32` eq:critical-derived, second line:
  `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖_{Ḣ^(3/2)}` for mean-zero periodic fields. -/
  gradientLambdaCriticalL3 :
    ∀ v : SpatialField, MemPeriodicVector v → IsMeanZero v →
      periodicHomogeneousENorm (3 / 2) v ≠ ⊤ →
        periodicGradientENorm 3 v + periodicLambdaENorm 3 v ≤
          ENNReal.ofReal K.CcriticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v

  /-- `appendix-b-embeddings.tex:26-32` eq:critical-derived, third line, in the
  mean-zero periodic form used at `03-torus.tex:471-477`:
  `‖∇v‖₆ ≤ C‖Δv‖₂`. -/
  gradientL6 :
    ∀ v : SpatialField, MemPeriodicVector v → IsMeanZero v →
      periodicLaplacianENorm 2 v ≠ ⊤ →
        periodicGradientENorm 6 v ≤
          ENNReal.ofReal K.Csix * periodicLaplacianENorm 2 v

  /-- `03-torus.tex:490-494`: the mean-zero Fourier comparison used by the
  continuation argument, `‖v‖_{H²} ≤ C‖Δv‖₂`. -/
  hTwo_le_laplacian :
    ∀ v : SpatialField, MemPeriodicVector v → IsMeanZero v →
      periodicLaplacianENorm 2 v ≠ ⊤ →
        periodicSobolevENorm 2 v ≤
          ENNReal.ofReal K.CHtwo * periodicLaplacianENorm 2 v

  /-- `02-preliminaries.tex:52-54` and `appendix-b-embeddings.tex:85-90`:
  on mean-zero periodic fields the spectral gap controls the inhomogeneous
  norm by the homogeneous norm at each fixed nonnegative order. -/
  spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicVector v → IsMeanZero v → periodicHomogeneousENorm s v ≠ ⊤ →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (K.Cgap s) * periodicHomogeneousENorm s v

end BlowupDensity.Research.T12.DraftA
