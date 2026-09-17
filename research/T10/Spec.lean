import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T10 reconciled specification: the periodic data layer on the unit three-torus

This is the statement-only reconciliation of the two blind drafts for the
future `Contracts/V1/TorusData.lean`.  It follows the carrier, names, and graph
form of Draft B, adds the manuscript's homogeneous datum, restores the complete
`ClassicalSolutionR` field order, and records the basic facts selected by
`research/T10/RECONCILIATION.md` in `TorusDataAPI`.

Physical fields remain unit-periodic functions on `R^3`; every Sobolev
construction is made on weighted Fourier coefficients indexed by `Z^3`.  No
declaration imports a local implementation module.
-/

noncomputable section

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

/-! ## Definitional checks requested by the lane brief

These registered whole-space abbreviations are not used by the periodic data
definitions below.  The lane brief nevertheless asks that the reconciliation's
abbreviation checks be pinned literally, so both checks are kept here. -/

/-- `Contracts/V1/Data.lean:741-744`: the inhomogeneous completed-density
abbreviation is definitionally `CompletedDenseVia` with `IsSobolevPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- `Contracts/V1/Data.lean:746-753`: the homogeneous completed-density
abbreviation is definitionally `CompletedDenseVia` with `IsHomogeneousPath`. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

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

/-- `02-preliminaries.tex:76-80`: the unit-period derivative symbol
`2π i k_j`. -/
def periodicDerivativeSymbol (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (2 * Real.pi * Complex.I) * (k j : ℂ)

/-- `02-preliminaries.tex:76-80`: coefficient-side solenoidality.  Since the
Bessel weight is scalar at each `k`, the condition is the same on weighted and
unweighted coefficients. -/
def IsSolenoidalPeriodicDatum {s : ℝ} (A : PeriodicSobolev s) : Prop :=
  ∀ k : PeriodicFrequency,
    ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k = 0

/-- `02-preliminaries.tex:76-80`: the periodic Leray projector applied to a
weighted datum. It is the identity at `k = 0` and has symbol
`I - k⊗k/|k|²` otherwise.  The result is presented coefficientwise; the
contraction lemma listed in `COMPARISON_B.md` upgrades it to an element of the
same `PeriodicSobolev s`. -/
def periodicLeray (s : ℝ) (A : PeriodicSobolev s)
    (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  if k = 0 then A.1 i k
  else
    A.1 i k -
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * A.1 j k

/-- `02-preliminaries.tex:76-80`: `B` is the same-order real Sobolev datum
obtained from `A` by the periodic Leray projector.  This graph form records the
exact quantifier order without assuming the later boundedness proof. -/
def IsPeriodicLerayDatum {s : ℝ} (A B : PeriodicSobolev s) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k = periodicLeray s A i k

/-- `01-introduction.tex:83-84` and `02-preliminaries.tex:79-80`: `B` is the
same Fourier datum as `A`, transported from order `s` to order `t` by the
scalar Bessel weight.  Exact quantifier order: `∀ i, ∀ k`. -/
def IsPeriodicReweight (s t : ℝ) (A : PeriodicSobolev s)
    (B : PeriodicSobolev t) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    B.1 i k = (periodicFrequencyWeight k) ^ ((t - s) / 2) • A.1 i k

/-! ## 3. Time paths, force norms, and the smooth input classes -/

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

/-- `02-preliminaries.tex:9` eq:inputspaces: the lifted realization of
`C∞_div(T³;R³)`. -/
def initialClassT : Set SpatialField :=
  {a | ContDiff ℝ ∞ a ∧ IsPeriodicSpatial a ∧ IsSolenoidal a}

/-- `02-preliminaries.tex:10,23-26` eq:inputspaces:
`C_c∞(T³×(0,∞);R³)` in the periodic-functions-on-`R³` realization.
Only time support is compact in the lift. -/
def MemForceT (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧
    IsPeriodicOn univ f ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ univ

/-- `02-preliminaries.tex:10` eq:inputspaces: the torus force class `F_T`. -/
def forceClassT : Set SpaceTimeField := {f | MemForceT f}

/-! ## 4. Pressure normalization and classical solutions -/

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

/-- `02-preliminaries.tex:28-36,75-115` prop:local: a classical periodic
solution of Navier–Stokes on `[0,T)` at viscosity `ν`, with initial velocity
`a`, prescribed force `f`, periodic velocity and pressure, and the pressure
representative fixed by `∫_T³p=0`.

The Sobolev field has quantifier order `∀ m, ∃ G, ContinuousOn G ... ∧
∀ t, ...`; hence every compact preterminal slice has the paper's smooth
Sobolev regularity without postulating an endpoint value at `T`. -/
structure ClassicalSolutionT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) where
  /-- `02-preliminaries.tex:28-36`: the velocity field. -/
  velocity : SpaceTimeField
  /-- `02-preliminaries.tex:28,84-88`: the scalar pressure, ultimately fixed by
  the zero-mean gauge. -/
  pressure : SpaceTimeScalar
  /-- `02-preliminaries.tex:32-36`: the horizon is a genuine positive
  interval. -/
  horizon_pos : 0 < T
  /-- `02-preliminaries.tex:28-36,105-114`: velocity smoothness on the
  closed-at-zero, open-at-`T` slab. -/
  velocity_smooth :
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `02-preliminaries.tex:28-36,84-103`: pressure smoothness on the same
  slab. -/
  pressure_smooth :
    ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `02-preliminaries.tex:28-29`: `u(0,·)=a`.  Exact quantifier order:
  `∀ x : Space`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `01-introduction.tex:4-7`: `div u=0` on `[0,T)`.  Exact quantifier
  order: `∀ t ∈ Ico 0 T, ∀ x`. -/
  divergence :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- `01-introduction.tex:4-7`: the momentum equation at interior times.
  Exact quantifier order: `∀ t ∈ Ioo 0 T, ∀ x`. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- `02-preliminaries.tex:28-36,105-114`: continuous integer-order Fourier
  data throughout the lifespan.  Exact quantifier order:
  `∀ m : ℕ, ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T`. -/
  sobolev : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T,
        IsPeriodicDatum (m : ℝ) (fun x ↦ velocity (t, x)) (G t)
  /-- `02-preliminaries.tex:101-103`: the torus analogue of
  `ClassicalSolutionR.pressure_gradient`, measured on the normalized compact
  torus.  Exact quantifier order: `∀ t ∈ Ico 0 T`. -/
  pressure_gradient : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (torusLift (fun x ↦ pressureGradient pressure t x)) 2 periodicTorusMeasure
  /-- `02-preliminaries.tex:28`: unit spatial periods for velocity.  Exact
  quantifier order is that of `IsPeriodicOn`: `∀ t ∈ Ico 0 T, ∀ x, ∀ i`. -/
  velocity_periodic : IsPeriodicOn (Ico (0 : ℝ) T) velocity
  /-- `02-preliminaries.tex:28,101-103`: unit spatial periods for pressure.
  Exact quantifier order is `∀ t ∈ Ico 0 T, ∀ x, ∀ i`. -/
  pressure_periodic : IsPeriodicOn (Ico (0 : ℝ) T) pressure
  /-- `02-preliminaries.tex:28,84-88`: the paper's unique periodic pressure
  representative.  Exact quantifier order: `∀ t ∈ Ico 0 T`. -/
  pressure_gauge : PressureGaugeT (Ico (0 : ℝ) T) pressure

/-- `02-preliminaries.tex:32-36,105-115` prop:local: the maximal classical
lifespan, as the supremum of horizons carrying a periodic classical solution.
Global lifespan is `⊤`; the empty supremum is `0`. -/
def maximalLifespanT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionT ν a f S), ENNReal.ofReal S

/-- `02-preliminaries.tex:35-36`: a periodic reference solution is regular
through `T` when it has a classical extension to `T+δ` for some `δ>0`. -/
def RegularThroughT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))

/-! ## 5. Breakdown, relative density, and the energy metric -/

/-- `02-preliminaries.tex:38-48` eq:singularforces, relative to an arbitrary
ambient periodic force class `Y`. -/
def breakdownSetInT (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField) (T : ℝ) :
    Set SpaceTimeField :=
  {f | f ∈ Y ∧ maximalLifespanT ν a f ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex:38-48` eq:singularforces:
`B_{ν,a,T}={f∈F_T:T_max^ν(a,f)≤T}`. -/
def breakdownSetT (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  breakdownSetInT forceClassT ν a T

/-- `03-torus.tex:6-15,350-355`: relative density in the periodic
`L^q(0,∞;H^s)` pseudometric.  The quantifier order is exactly
`∀ g∈Y, ∀ r>0, ∃ f∈S`. -/
def RelativelyDenseT (q : ℝ≥0∞) (s : ℝ)
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S, forceSobolevENormT q s (f - g) < r

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

/-- `01-introduction.tex:143-150`: coefficient-side spelling of the
`L∞(0,T;L²(T³))` term. -/
def coefficientEnergyEssSupT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t ↦ periodicSobolevENorm 0 (fun x ↦ z (t, x)))
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:105-109,143-150`: coefficient-side spelling of the
`L²(0,T;Ḣ¹(T³))` gradient term.  The spatial mean is removed because the
homogeneous realization requires zero mean and gradients annihilate constants. -/
def coefficientEnergyGradientT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (periodicHomogeneousENorm 1 (meanZeroPartT (fun x ↦ z (t, x)))) ^ (2 : ℝ)) ^
    ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143-150` and `03-torus.tex:556-561`: the complete
coefficient-side `E_T` quantity. -/
def coefficientEnergyENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  coefficientEnergyEssSupT T z + coefficientEnergyGradientT T z

/-! ## 6. Reconciled consumer-facing facts -/

/-- Basic facts of the periodic data layer selected by
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

  /-- `02-preliminaries.tex:76-80`: the periodic Leray map fixes every
  solenoidal datum.

  Exact quantifier order: `∀ s, ∀ A, ∀ B`, solenoidality of `A`, then the
  graph equation `B=P A`.

  Non-vacuity: the conclusion is equality in `PeriodicSobolev s`, making the
  range/fixed-point characterization directly usable. -/
  leray_fixes_solenoidal :
    ∀ (s : ℝ) (A B : PeriodicSobolev s), IsSolenoidalPeriodicDatum A →
      IsPeriodicLerayDatum A B → B = A

  /-- `02-preliminaries.tex:79-80`: Leray commutes with scalar Bessel
  reweighting between any two Sobolev orders.

  Exact quantifier order: `∀ s, ∀ t, ∀ A, ∀ B, ∀ PA, ∀ PB`, followed by the
  reweight and two Leray graph hypotheses.

  Non-vacuity: the conclusion is the coefficientwise relation transporting
  `PA` from order `s` to `PB` at order `t`; it is not an untyped commutation
  slogan. -/
  leray_commutes_weight :
    ∀ (s t : ℝ) (A : PeriodicSobolev s) (B : PeriodicSobolev t)
        (PA : PeriodicSobolev s) (PB : PeriodicSobolev t),
      IsPeriodicReweight s t A B → IsPeriodicLerayDatum A PA →
        IsPeriodicLerayDatum B PB → IsPeriodicReweight s t PA PB

  /-- `02-preliminaries.tex:76-80` and `03-torus.tex:395-411`: Leray preserves
  the mean-zero coefficient subspace because its zero-mode symbol is identity.

  Exact quantifier order: `∀ s, ∀ A, ∀ B`, zero-mode membership of `A`, then
  the Leray graph equation.

  Non-vacuity: the result is membership of the actual output datum in the
  closed zero-mode submodule. -/
  leray_preserves_meanZero :
    ∀ (s : ℝ) (A B : PeriodicSobolev s), A ∈ meanZeroPeriodicSobolev s →
      IsPeriodicLerayDatum A B → B ∈ meanZeroPeriodicSobolev s

  /-- `02-preliminaries.tex:28,84-88` and `03-torus.tex:319`: subtracting the
  spatial pressure mean produces the chosen gauge without changing its spatial
  gradient or the momentum equation.

  Exact quantifier order: `∀ I, ∀ p`, periodicity and slice integrability,
  then the normalized periodicity/gauge conclusions and finally
  `∀ ν, ∀ u, ∀ f, ∀ t ∈ I, ∀ x` for equation preservation.

  Non-vacuity: the result simultaneously supplies the normalized periodic
  pressure, its zero integral, pointwise gradient equality, and preservation of
  every concrete Navier--Stokes residual equation on `I`. -/
  pressure_normalization :
    ∀ (I : Set ℝ) (p : SpaceTimeScalar), IsPeriodicOn I p →
      (∀ t ∈ I, Integrable (torusLift (fun x ↦ p (t, x))) periodicTorusMeasure) →
        IsPeriodicOn I (normalizePressureT p) ∧
        PressureGaugeT I (normalizePressureT p) ∧
        (∀ t ∈ I, ∀ x : Space,
          pressureGradient (normalizePressureT p) t x = pressureGradient p t x) ∧
        ∀ (ν : ℝ) (u : SpaceTimeField) (f : SpaceTimeField),
          ∀ t ∈ I, ∀ x : Space,
            NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x) →
              NavierStokesR3.ProblemStatement.navierStokesResidual ν u
                (normalizePressureT p) t x = f (t, x)

  /-- `01-introduction.tex:143-150` and `03-torus.tex:299,540-561`: the
  coefficient `E_T` expression agrees with the physical Haar-space expression
  on every classical periodic velocity.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T`, then
  `∀ U : ClassicalSolutionT ν a f T`.

  Non-vacuity: this equates two independently defined `ℝ≥0∞` quantities on the
  concrete velocity carried by a genuine classical solution. -/
  energy_eq_physical :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      ∀ U : ClassicalSolutionT ν a f T,
        coefficientEnergyENormT T U.velocity = energyENormT T U.velocity

  /-- `02-preliminaries.tex:32-36,105-114`: a classical periodic solution
  transports to every shorter positive horizon without changing its fields.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T, ∀ U, ∀ S`, positivity of `S`,
  then `S ≤ T`, then `∃ V`.

  Non-vacuity: `V` is a full `ClassicalSolutionT` and both its velocity and
  pressure are pinned to those of the given solution. -/
  classicalSolution_restrict :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
        (U : ClassicalSolutionT ν a f T) (S : ℝ),
      0 < S → S ≤ T →
        ∃ V : ClassicalSolutionT ν a f S,
          V.velocity = U.velocity ∧ V.pressure = U.pressure

  /-- `01-introduction.tex:4-7` and `02-preliminaries.tex:32-36`: the solution
  predicate transports across forces equal at every interior spacetime point.

  Exact quantifier order: `∀ ν, ∀ a, ∀ f, ∀ T, ∀ U, ∀ g`, pointwise force
  equality with order `∀ t ∈ Ioo 0 T, ∀ x`, then `∃ V`.

  Non-vacuity: the witness is a full classical solution for the replacement
  force and retains the original velocity and pressure, rather than merely
  asserting equality of lifespan numbers. -/
  classicalSolution_force_transport :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
        (U : ClassicalSolutionT ν a f T) (g : SpaceTimeField),
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, f (t, x) = g (t, x)) →
        ∃ V : ClassicalSolutionT ν a g T,
          V.velocity = U.velocity ∧ V.pressure = U.pressure

end BlowupDensity.T10.Draft
