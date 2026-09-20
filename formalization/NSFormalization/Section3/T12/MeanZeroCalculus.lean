import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Section4.A05.GradientL6
import NSFormalization.Section4.C01.Trilinear

/-!
# T12 canonical mean-zero periodic Sobolev calculus vocabulary

This definitions-only module is the local canonical realization of the new
vocabulary before `MeanZeroSobolevCalculusAPI` in `research/T12/Spec.lean`.
The periodic data layer is imported from T10 rather than copied.  The three
registered derivative spellings are reducible aliases of their existing local
Section 4 canonical sources.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
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

/-- The time-independent lift, reused from its local Section 4 canonical
source. -/
abbrev lift (v : SpatialField) : SpaceTimeField :=
  NSFormalization.Section4.C01.lift v

/-- The physical Frobenius gradient tensor, reused from the local source of
the registered `GradientL6` spelling. -/
abbrev gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  NSFormalization.Section4.A05.gradTensor v

/-- The componentwise spatial Laplacian, reused from the local source of the
registered `GradientL6` spelling. -/
abbrev laplacian (v : SpatialField) : SpatialField :=
  NSFormalization.Section4.A05.lap v

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

end NSFormalization.Section3.T12
