import Mathlib.Analysis.Fourier.AddCircleMulti
import NavierStokes.PeriodicIntegration

/-!
# T12 draft B: mean-zero periodic Sobolev calculus

This is a statement-only, double-blind draft.  The physical layer consists of
unit-periodic fields on `R^3`; the analytic layer consists of weighted
`lp (Fin 3 → ℤ) 2` Fourier data.  The definitions marked below are local
copies which need registration in T10 (or alignment with T10's accepted names).
-/

noncomputable section

namespace BlowupDensity.Research.T12.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Local data layer -- needs registration / alignment with T10 -/

/-- `01-introduction.tex:9-10`: physical vector fields on `R^3`, used as the
periodic realization of fields on the unit torus.  Needs registration/alignment
with T10. -/
abbrev SpatialField := Space → Space

/-- `appendix-a-local-theory.tex:9-12`: scalar factors in `eq:Rproduct`.
Needs registration/alignment with T10. -/
abbrev ScalarField := Space → ℝ

/-- `01-introduction.tex:9-10`: the unit three-torus.  Needs
registration/alignment with T10's torus carrier. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

/-- `01-introduction.tex:83-89`: the Fourier-frequency lattice of the unit
three-torus.  Needs registration/alignment with T10. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `01-introduction.tex:89`: the canonical representative in `(0,1]^3` used
to read a physical periodic field as a torus field.  This is verbatim the local
periodic-layer definition and needs registration/alignment with T10. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val))

/-- `01-introduction.tex:84,106`: `|2πk|^2`.  Needs
registration/alignment with T10's angular-frequency convention. -/
def periodicAngularFrequencySq (k : PeriodicFrequency) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `01-introduction.tex:83-84`: the inhomogeneous coefficient multiplier
`(1 + 4π²|k|²)^(s/2)`.  Needs registration/alignment with T10. -/
def periodicSobolevWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  (1 + periodicAngularFrequencySq k) ^ (s / 2)

/-- `01-introduction.tex:105-107`: the homogeneous coefficient multiplier
`|2πk|^s`; the zero mode is omitted.  Needs registration/alignment with T10. -/
def periodicHomogeneousWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else (Real.sqrt (periodicAngularFrequencySq k)) ^ s

/-- `01-introduction.tex:83-89`: the `k`-th angular Fourier coefficient of the
`i`-th component of a physical periodic vector field.  Needs
registration/alignment with T10. -/
def periodicFourierCoeff (z : SpatialField) (i : Fin 3)
    (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus => (torusLift z x i : ℂ)) k

/-- `01-introduction.tex:83-89`: scalar version of `periodicFourierCoeff`, used
by `eq:Rproduct`.  Needs registration/alignment with T10. -/
def periodicScalarFourierCoeff (z : ScalarField) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun x : PeriodicTorus => ((torusLift z x : ℝ) : ℂ)) k

/-- `01-introduction.tex:83-84,103`: a scalar weighted `ell^2(Z^3)` datum.
Needs registration/alignment with T10. -/
abbrev PeriodicScalarSobolevDatum := lp (fun _ : PeriodicFrequency => ℂ) 2

/-- `01-introduction.tex:83-84,103`: three scalar weighted `ell^2(Z^3)` data,
assembled with the Euclidean (`l^2`) product norm.  Needs
registration/alignment with T10. -/
abbrev PeriodicSobolevDatum := WithLp 2 (Fin 3 → PeriodicScalarSobolevDatum)

/-- `01-introduction.tex:83-89`: `A` is the order-`s` inhomogeneous Fourier
datum of a physical vector field.  Periodicity and `L^2` membership are part of
the realization, preventing the Fourier integral from silently totalizing a
nonintegrable field.  Needs registration/alignment with T10. -/
def IsPeriodicSobolevDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolevDatum) : Prop :=
  UnitPeriods z ∧
    MemLp (torusLift z) 2 volume ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A i k = periodicSobolevWeight s k * periodicFourierCoeff z i k

/-- `01-introduction.tex:83-89`: scalar realization predicate for
`eq:Rproduct`.  Needs registration/alignment with T10. -/
def IsPeriodicScalarSobolevDatum (s : ℝ) (z : ScalarField)
    (A : PeriodicScalarSobolevDatum) : Prop :=
  UnitPeriods z ∧
    MemLp (torusLift z) 2 volume ∧
    ∀ k : PeriodicFrequency,
      A k = periodicSobolevWeight s k * periodicScalarFourierCoeff z k

/-- `01-introduction.tex:83-84`: `||z||_{H^s(T^3)}` as an `ENNReal` datum
norm, with `top` if no datum realizes the physical field.  Needs
registration/alignment with T10. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolevDatum // IsPeriodicSobolevDatum s z A}, ‖A.1‖ₑ

/-- `01-introduction.tex:83-84`: scalar `H^s(T^3)` norm used by
`eq:Rproduct`.  Needs registration/alignment with T10. -/
def periodicScalarSobolevENorm (s : ℝ) (z : ScalarField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicScalarSobolevDatum // IsPeriodicScalarSobolevDatum s z A}, ‖A.1‖ₑ

/-- `01-introduction.tex:106-107`: the mean-zero subspace is exactly the
subspace whose `k = 0` coefficient vanishes in every component.  Needs
registration/alignment with T10. -/
def IsMeanZero (z : SpatialField) : Prop :=
  ∀ i : Fin 3, periodicFourierCoeff z i 0 = 0

/-- `01-introduction.tex:106-107`: coefficient-side mean-zero subspace.
Needs registration/alignment with T10. -/
def IsMeanZeroDatum (A : PeriodicSobolevDatum) : Prop :=
  ∀ i : Fin 3, A i 0 = 0

/-- `03-torus.tex:398-400`: the spatial mean of a physical periodic field.
Needs registration/alignment with T10. -/
def periodicMean (z : SpatialField) : Space :=
  ∫ x : PeriodicTorus, torusLift z x

/-- `03-torus.tex:398-400`: the physical mean-zero part `z - integral z`.
Needs registration/alignment with T10. -/
def meanZeroPart (z : SpatialField) : SpatialField :=
  fun x => z x - periodicMean z

/-- `01-introduction.tex:105-107`: `A` is the order-`s` homogeneous datum of a
mean-zero periodic field, with multiplier `|2πk|^s` and the zero coefficient
omitted.  Needs registration/alignment with T10. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolevDatum) : Prop :=
  UnitPeriods z ∧
    MemLp (torusLift z) 2 volume ∧
    IsMeanZero z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A i k = periodicHomogeneousWeight s k * periodicFourierCoeff z i k

/-- `01-introduction.tex:105-107`: `||z||_{dot H^s(T^3)}` on mean-zero
periodic representatives, totalized to `top` off that class.  Needs
registration/alignment with T10. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolevDatum // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/-- `appendix-b-embeddings.tex:21-22,26-27`: a physical mean-zero periodic
representative with finite displayed homogeneous norm.  Needs
registration/alignment with T10. -/
def MemPeriodicHomogeneous (s : ℝ) (z : SpatialField) : Prop :=
  UnitPeriods z ∧ MemLp (torusLift z) 2 volume ∧ IsMeanZero z ∧
    periodicHomogeneousENorm s z ≠ ⊤

/-- `appendix-a-local-theory.tex:9-12`: scalar membership in the positive
integer-order periodic Sobolev space.  Needs registration/alignment with T10. -/
def MemPeriodicHmScalar (m : ℕ) (z : ScalarField) : Prop :=
  UnitPeriods z ∧ MemLp (torusLift z) 2 volume ∧
    periodicScalarSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-a-local-theory.tex:12`: vector membership in periodic `H^m`.
Needs registration/alignment with T10. -/
def MemPeriodicHmVector (m : ℕ) (z : SpatialField) : Prop :=
  UnitPeriods z ∧ MemLp (torusLift z) 2 volume ∧
    periodicSobolevENorm (m : ℝ) z ≠ ⊤

/-- `02-preliminaries.tex:9` and `appendix-b-embeddings.tex:36-37`: the smooth
periodic vector fields to which the derivative estimates are applied.  Needs
registration/alignment with T10. -/
def SmoothPeriodicVector (z : SpatialField) : Prop :=
  ContDiff ℝ ∞ z ∧ UnitPeriods z

/-- `01-introduction.tex:104` and `appendix-b-embeddings.tex:14-17`: the
physical torus `L^p` norm of a chosen representative.  Needs
registration/alignment with T10. -/
def periodicLpENorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (z : Space → E) : ℝ≥0∞ :=
  eLpNorm (torusLift z) p volume

/-- `appendix-b-embeddings.tex:97-100`: the physical Frobenius gradient
tensor.  Needs registration/alignment with T10's spatial derivative. -/
def gradientTensor (z : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => WithLp.toLp 2 (fun i => fderiv ℝ z x (coordinateVector i))

/-- `03-torus.tex:468-477`: the componentwise spatial Laplacian.  Needs
registration/alignment with T10's spatial operator. -/
def laplacian (z : SpatialField) : SpatialField :=
  fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ z y (coordinateVector i)) x (coordinateVector i)

/-- `appendix-b-embeddings.tex:8-9,97-100`: `Lz` is the physical representative
of `Lambda z`, fixed by the multiplier `|2πk|`.  Needs
registration/alignment with T10's Fourier multiplier. -/
def IsPeriodicLambda (z Lz : SpatialField) : Prop :=
  SmoothPeriodicVector Lz ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff Lz i k =
        Real.sqrt (periodicAngularFrequencySq k) * periodicFourierCoeff z i k

/-! ## Constants and the proposition-valued API -/

/-- The universal constants in `eq:Rproduct`, `lem:calculus`, and
`lem:critical-embeddings` (`appendix-a-local-theory.tex:8-26` and
`appendix-b-embeddings.tex:11-33,109-110`).  Lean forbids non-proof projections
from a `Prop`-valued structure, so the constants are bundled separately and the
requested proposition-valued API is parameterized by this record. -/
structure MeanZeroSobolevConstants where
  /-- `appendix-a-local-theory.tex:10-11`: `C_m`, chosen before the fields. -/
  product : ℕ → ℝ
  /-- `appendix-a-local-theory.tex:10`: positivity of the tame-product constants. -/
  product_pos : ∀ m : ℕ, 0 < product m
  /-- `appendix-a-local-theory.tex:12`: the universal `H^2`-to-`L^∞` constant. -/
  linfty : ℝ
  /-- `appendix-a-local-theory.tex:12`: positivity of the embedding constant. -/
  linfty_pos : 0 < linfty
  /-- `appendix-b-embeddings.tex:29`: the universal critical `L^3` constant. -/
  criticalHalf : ℝ
  /-- `appendix-b-embeddings.tex:12-13`: positivity of that constant. -/
  criticalHalf_pos : 0 < criticalHalf
  /-- `appendix-b-embeddings.tex:30-31`: the universal derived order-`3/2` constant. -/
  criticalThreeHalves : ℝ
  /-- `appendix-b-embeddings.tex:12-13`: positivity of that constant. -/
  criticalThreeHalves_pos : 0 < criticalThreeHalves
  /-- `appendix-b-embeddings.tex:32`: the universal gradient-`L^6` constant. -/
  gradientSix : ℝ
  /-- `appendix-b-embeddings.tex:12-13`: positivity of that constant. -/
  gradientSix_pos : 0 < gradientSix
  /-- `03-torus.tex:492-493`: the universal mean-zero `H^2`/Laplacian constant. -/
  hTwo : ℝ
  /-- `03-torus.tex:492-493`: positivity of that constant. -/
  hTwo_pos : 0 < hTwo
  /-- `appendix-b-embeddings.tex:85-90`: the spectral-gap comparison constant
  at order `s`, chosen before the field. -/
  gap : ℝ → ℝ
  /-- `appendix-b-embeddings.tex:85-90`: positivity of the spectral-gap constants. -/
  gap_pos : ∀ s : ℝ, 0 < gap s

/-- T12's seven target inequalities.  Every constant is fixed by `K` before
the order and physical fields are quantified, matching the paper's universal
quantifier order (`appendix-b-embeddings.tex:109-110`). -/
structure MeanZeroSobolevAPI (K : MeanZeroSobolevConstants) : Prop where
  /-- `appendix-a-local-theory.tex:8-12` `eq:Rproduct`: for every integer
  `m >= 2`, the periodic tame product estimate. -/
  tameProduct :
    ∀ m : ℕ, 2 ≤ m → ∀ a b : ScalarField,
      MemPeriodicHmScalar m a → MemPeriodicHmScalar m b →
        periodicScalarSobolevENorm (m : ℝ) (fun x => a x * b x) ≤
          ENNReal.ofReal (K.product m) *
            (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (m : ℝ) b +
              periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (m : ℝ) a)

  /-- `appendix-a-local-theory.tex:12` `eq:Rproduct`: periodic
  `||v||_infinity <= C ||v||_{H^2}`.  No mean-zero hypothesis is added because
  this is an inhomogeneous estimate and the paper states it for either domain. -/
  boundedRepresentative :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤
        ENNReal.ofReal K.linfty * periodicSobolevENorm 2 v

  /-- `appendix-b-embeddings.tex:21-22,26-29`: the critical mean-zero
  `||v||_3 <= C ||v||_{dot H^(1/2)}` embedding. -/
  velocityCriticalL3 :
    ∀ v : SpatialField, MemPeriodicHomogeneous (1 / 2) v →
      periodicLpENorm 3 v ≤
        ENNReal.ofReal K.criticalHalf * periodicHomogeneousENorm (1 / 2) v

  /-- `appendix-a-local-theory.tex:22-26` `eq:embeddings` and
  `appendix-b-embeddings.tex:30-31`: the two order-`3/2` derivative terms,
  retained as the single displayed sum inequality. -/
  gradientLambdaCriticalL3 :
    ∀ (v Lv : SpatialField), SmoothPeriodicVector v →
      MemPeriodicHomogeneous (3 / 2) v → IsPeriodicLambda v Lv →
        periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
          ENNReal.ofReal K.criticalThreeHalves *
            periodicHomogeneousENorm (3 / 2) v

  /-- `appendix-b-embeddings.tex:26-33`, used at `03-torus.tex:470-477`:
  the mean-zero periodic `||nabla v||_6 <= C ||Delta v||_2` estimate. -/
  gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicVector v → IsMeanZero v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal K.gradientSix * periodicLpENorm 2 (laplacian v)

  /-- `03-torus.tex:490-500`: the mean-zero Fourier estimate
  `||v||_{H^2} <= C ||Delta v||_2` used by the continuation criterion. -/
  hTwo_le_laplacian :
    ∀ v : SpatialField, SmoothPeriodicVector v → IsMeanZero v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal K.hTwo * periodicLpENorm 2 (laplacian v)

  /-- `02-preliminaries.tex:50-54` and `appendix-b-embeddings.tex:85-90`:
  at each nonnegative order, the unit-torus spectral gap controls the
  inhomogeneous norm of a mean-zero field by its homogeneous norm. -/
  spectralGap :
    ∀ s : ℝ, 0 ≤ s → ∀ v : SpatialField,
      MemPeriodicHomogeneous s v →
        periodicSobolevENorm s v ≤
          ENNReal.ofReal (K.gap s) * periodicHomogeneousENorm s v

end BlowupDensity.Research.T12.DraftB
