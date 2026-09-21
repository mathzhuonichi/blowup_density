import Contracts.V1.Data
import Contracts.V2.Continuation
import Contracts.V2.LocalTheory
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T11 reconciled specification: periodic local theory and continuation

This statement-only file reconciles the two blind T11 drafts according to
research/T11/RECONCILIATION.md. It specifies Proposition prop:local on the
unit three-torus, the squared-H² continuation criterion, Appendix A's
data-defined Galilean mean reduction, and positive-viscosity rescaling.

Files below research/ are not Lean modules. The T10 declarations used here
are therefore copied unchanged in the T10 Draft namespace. The data tier is
already assigned to T01.torus_data but is not present in this worktree's base;
the deferred solution-class tier remains T11's source text. Marker comments
give the source line of every copied declaration.
-/

noncomputable section

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

/-! Definitional checks required by the reconciliation. -/

/-- Contracts/V1/Data.lean:743-744: the inhomogeneous registered
abbreviation unfolds exactly to CompletedDenseVia with IsSobolevPath. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S := rfl

/-- Contracts/V1/Data.lean:752-753: the homogeneous registered
abbreviation unfolds exactly to CompletedDenseVia with IsHomogeneousPath. -/
example (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) :
    CompletedDenseHomogeneous q s S =
      CompletedDenseVia q s (IsHomogeneousPath s) S := rfl

/-! Begin declarations copied from research/T10/Spec.lean. -/

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the frequency lattice of the unit
three-torus. -/
-- copied from research/T10/Spec.lean:48
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: Mathlib's unit additive three-torus. -/
-- copied from research/T10/Spec.lean:51
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

-- copied from research/T10/Spec.lean:53
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
-- copied from research/T10/Spec.lean:54
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: normalized Haar measure on the unit torus. -/
-- copied from research/T10/Spec.lean:58
abbrev periodicTorusMeasure : Measure PeriodicTorus := volume

/-- `03-torus.tex:2-4` and the (P) representation fixed in
`collaboration/SECTION3_PLAN.md` §1: invariance under every positive unit
coordinate shift. Quantification over all `x` also supplies negative shifts. -/
-- copied from research/T10/Spec.lean:63
def IsPeriodicSpatial {E : Type*} [Add E] (z : Space → E) : Prop :=
  ∀ x : Space, ∀ i : Fin 3, z (x + coordinateVector i) = z x

/-- `02-preliminaries.tex:28`: spatial periodicity on a specified set of times,
with time as the first spacetime coordinate. -/
-- copied from research/T10/Spec.lean:68
def IsPeriodicOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t ∈ I, ∀ x : Space, ∀ i : Fin 3,
    z (t, x + coordinateVector i) = z (t, x)

/-- `03-torus.tex:2-4`, `01-introduction.tex:89`, and `TorusCube.lean:25-26`: canonical realization
of the (P) field on Mathlib's unit torus, using representatives in `(0,1]^3`.
This is the local `NSFormalization.Paper1.torusLift` definition restated
verbatim, with its one-line `toSpace` map expanded. -/
-- copied from research/T10/Spec.lean:76
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f ((EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) z).val))

/-- `03-torus.tex:2-4` and `01-introduction.tex:89`: the coefficient
`ẑ(k) = ∫_T³ z(x) exp(-2π i k·x) dx`.  This is exactly the local
`NSFormalization.Paper1.periodicFourierCoeff`, restated so the eventual
contract needs no local implementation import. -/
-- copied from research/T10/Spec.lean:84
def periodicFourierCoeff (f : Space → ℂ) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-84`: the squared Bessel weight
`1 + 4π²|k|²` in the unit-period convention. -/
-- copied from research/T10/Spec.lean:89
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `03-torus.tex:2-4`: scalar complete `ℓ²(Z³;ℂ)` coefficient data. -/
-- copied from research/T10/Spec.lean:93
abbrev PeriodicScalarData := lp (fun _ : PeriodicFrequency ↦ ℂ) 2

/-- `03-torus.tex:2-4` and `01-introduction.tex:103`: three scalar coefficient sequences with the
Euclidean (`PiLp 2`) product norm. -/
-- copied from research/T10/Spec.lean:97
abbrev PeriodicVectorData := WithLp 2 (Fin 3 → PeriodicScalarData)

/-- `02-preliminaries.tex:72-73`: the conjugate-reflection real subspace of
three-component complex Fourier data. -/
-- copied from research/T10/Spec.lean:101
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
-- copied from research/T10/Spec.lean:119
abbrev PeriodicSobolev (_s : ℝ) := realPeriodicSubmodule

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the `H^s(T³)` norm of a coefficient datum,
with squared component norms summed as prescribed in the paper. -/
-- copied from research/T10/Spec.lean:123
def periodicSobolevDataNorm (s : ℝ) (A : PeriodicSobolev s) : ℝ := ‖A‖

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: `A` is the order-`s` weighted Fourier datum
of the real physical field `z`.  The exact quantifier order is component first,
then lattice frequency.

Lead amendment (2026-09-17, `RECONCILIATION.md` §5): the datum requires the
lifted field to be Haar-integrable.  Without it the Bochner integral defining
`periodicFourierCoeff` is the junk value `0` for every non-integrable periodic
`z`, so `A = 0` would be a datum of e.g. the periodization of `x ↦ 1/x₁` and
`periodicSobolevENorm` would be `0` instead of `⊤` there. -/
-- copied from research/T10/Spec.lean:134
def IsPeriodicDatum (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (periodicFrequencyWeight k) ^ (s / 2) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the total `H^s(T³)` extended norm of a
physical field, defined as the infimum of the norms of all representing data.
The empty infimum is `⊤`. -/
-- copied from research/T10/Spec.lean:143
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicDatum s z A}, ‖A.1‖ₑ

/-! ## 2. Means, the zero mode, and homogeneous periodic data -/

/-- `03-torus.tex:395-401`: the normalized spatial mean of a real vector
field on the unit torus. -/
-- copied from research/T10/Spec.lean:150
def meanT (z : SpatialField) : Space :=
  ∫ y : PeriodicTorus, torusLift z y ∂periodicTorusMeasure

/-- `03-torus.tex:395-401`: the spatially constant part of a periodic field. -/
-- copied from research/T10/Spec.lean:154
def constantPartT (z : SpatialField) : SpatialField := fun _ ↦ meanT z

/-- `03-torus.tex:395-401`: `z - ∫_T³ z`, the mean-free part of a periodic
field. -/
-- copied from research/T10/Spec.lean:158
def meanZeroPartT (z : SpatialField) : SpatialField := fun x ↦ z x - meanT z

/-- `03-torus.tex:395-401`: the canonical constant/mean-free decomposition,
recorded as the ordered pair `(x ↦ meanT z, x ↦ z x - meanT z)`. -/
-- copied from research/T10/Spec.lean:162
def meanDecompositionT (z : SpatialField) : SpatialField × SpatialField :=
  (constantPartT z, meanZeroPartT z)

/-- `01-introduction.tex:105-108` and `03-torus.tex:395-411`: the mean-zero
closed coefficient subspace, characterized exactly by vanishing at `k = 0`.
The weight at zero is one, so this condition is independent of `s`. -/
-- copied from research/T10/Spec.lean:168
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
-- copied from research/T10/Spec.lean:181
def IsMeanZeroT (z : SpatialField) : Prop := meanT z = 0

/-- `01-introduction.tex:105-107`: the squared angular frequency
`|2πk|² = 4π²|k|²` in the unit-period convention. -/
-- copied from research/T10/Spec.lean:185
def periodicAngularFrequencySq (k : PeriodicFrequency) : ℝ :=
  4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `01-introduction.tex:105-107`: the homogeneous multiplier
`|2πk|^s = (4π²|k|²)^(s/2)`.  The omitted zero mode is represented by zero,
so every homogeneous datum has `A(0)=0`. -/
-- copied from research/T10/Spec.lean:191
def homogeneousDatumWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else Real.rpow (periodicAngularFrequencySq k) (s / 2)

/-- `01-introduction.tex:105-109`: `A` is the order-`s` homogeneous datum of a
mean-zero real periodic field.  Exact quantifier order: periodicity,
Haar integrability of the lift (lead amendment, `RECONCILIATION.md` §5: the
same junk-value reason as `IsPeriodicDatum`; it also makes `IsMeanZeroT` an
honest Haar-integral statement), zero mean, then
`∀ i : Fin 3, ∀ k : PeriodicFrequency`.  The zero-frequency equation forces
`A_i(0)=0`, as the manuscript's homogeneous convention requires. -/
-- copied from research/T10/Spec.lean:201
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Ḣ^s(T³)` extended norm of a mean-zero physical field.  It is the infimum over
homogeneous real data and is `⊤` when no datum exists. -/
-- copied from research/T10/Spec.lean:211
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/-- `02-preliminaries.tex:76-80`: the unit-period derivative symbol
`2π i k_j`. -/
-- copied from research/T10/Spec.lean:216
def periodicDerivativeSymbol (j : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (2 * Real.pi * Complex.I) * (k j : ℂ)

/-- `02-preliminaries.tex:76-80`: coefficient-side solenoidality.  Since the
Bessel weight is scalar at each `k`, the condition is the same on weighted and
unweighted coefficients. -/
-- copied from research/T10/Spec.lean:222
def IsSolenoidalPeriodicDatum {s : ℝ} (A : PeriodicSobolev s) : Prop :=
  ∀ k : PeriodicFrequency,
    ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k = 0

/-- `02-preliminaries.tex:76-80`: the periodic Leray projector applied to a
weighted datum. It is the identity at `k = 0` and has symbol
`I - k⊗k/|k|²` otherwise.  The result is presented coefficientwise; the
contraction lemma listed in `COMPARISON_B.md` upgrades it to an element of the
same `PeriodicSobolev s`. -/
-- copied from research/T10/Spec.lean:231
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
-- copied from research/T10/Spec.lean:242
def IsPeriodicLerayDatum {s : ℝ} (A B : PeriodicSobolev s) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k = periodicLeray s A i k

/-- `01-introduction.tex:83-84` and `02-preliminaries.tex:79-80`: `B` is the
same Fourier datum as `A`, transported from order `s` to order `t` by the
scalar Bessel weight.  Exact quantifier order: `∀ i, ∀ k`. -/
-- copied from research/T10/Spec.lean:248
def IsPeriodicReweight (s t : ℝ) (A : PeriodicSobolev s)
    (B : PeriodicSobolev t) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    B.1 i k = (periodicFrequencyWeight k) ^ ((t - s) / 2) • A.1 i k

/-! ## 3. Time paths, force norms, and the smooth input classes -/

/-- `01-introduction.tex:118-140`: `G` is the order-`s` datum trajectory of
the periodic physical field `f` at every nonnegative time. -/
-- copied from research/T10/Spec.lean:257
def IsPeriodicSobolevPath (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsPeriodicDatum s (fun x ↦ f (t, x)) (G t)

/-- `01-introduction.tex:118-140` and `03-torus.tex:7`: the physical-field
quantity `‖f‖_{L^q(0,∞;H^s(T³))}`.  It is the infimum over strongly
measurable representing paths, with `⊤` when no such path exists. -/
-- copied from research/T10/Spec.lean:264
def forceSobolevENormT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → PeriodicSobolev s //
      IsPeriodicSobolevPath s f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `02-preliminaries.tex:9` eq:inputspaces: the lifted realization of
`C∞_div(T³;R³)`. -/
-- copied from research/T10/Spec.lean:272
def initialClassT : Set SpatialField :=
  {a | ContDiff ℝ ∞ a ∧ IsPeriodicSpatial a ∧ IsSolenoidal a}

/-- `02-preliminaries.tex:10,23-26` eq:inputspaces:
`C_c∞(T³×(0,∞);R³)` in the periodic-functions-on-`R³` realization.
Only time support is compact in the lift. -/
-- copied from research/T10/Spec.lean:278
def MemForceT (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧
    IsPeriodicOn univ f ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ univ

/-- `02-preliminaries.tex:10` eq:inputspaces: the torus force class `F_T`. -/
-- copied from research/T10/Spec.lean:284
def forceClassT : Set SpaceTimeField := {f | MemForceT f}

/-! ## 4. Pressure normalization and classical solutions -/

/-- `02-preliminaries.tex:28,84-88`: the normalized spatial mean of a
periodic pressure slice. -/
-- copied from research/T10/Spec.lean:290
def pressureMeanT (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  ∫ y : PeriodicTorus, torusLift (fun x ↦ p (t, x)) y ∂periodicTorusMeasure

/-- `02-preliminaries.tex:28,84-88`: the pressure gauge `∫_T³ p(t)=0`,
imposed at every time in `I`. -/
-- copied from research/T10/Spec.lean:295
def PressureGaugeT (I : Set ℝ) (p : SpaceTimeScalar) : Prop :=
  ∀ t ∈ I, pressureMeanT p t = 0

/-- `02-preliminaries.tex:84-88` and `03-torus.tex:319`: subtract the
normalized spatial mean from each pressure slice. -/
-- copied from research/T10/Spec.lean:300
def normalizePressureT (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p z - pressureMeanT p z.1

/-- `02-preliminaries.tex:28-36,75-115` prop:local: a classical periodic
solution of Navier–Stokes on `[0,T)` at viscosity `ν`, with initial velocity
`a`, prescribed force `f`, periodic velocity and pressure, and the pressure
representative fixed by `∫_T³p=0`.

The Sobolev field has quantifier order `∀ m, ∃ G, ContinuousOn G ... ∧
∀ t, ...`; hence every compact preterminal slice has the paper's smooth
Sobolev regularity without postulating an endpoint value at `T`. -/
-- copied from research/T10/Spec.lean:311
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
-- copied from research/T10/Spec.lean:364
def maximalLifespanT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionT ν a f S), ENNReal.ofReal S

/-- `02-preliminaries.tex:35-36`: a periodic reference solution is regular
through `T` when it has a classical extension to `T+δ` for some `δ>0`. -/
-- copied from research/T10/Spec.lean:369
def RegularThroughT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))

/-! ## 5. Breakdown, relative density, and the energy metric -/

/-- `02-preliminaries.tex:38-48` eq:singularforces, relative to an arbitrary
ambient periodic force class `Y`. -/
-- copied from research/T10/Spec.lean:376
def breakdownSetInT (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField) (T : ℝ) :
    Set SpaceTimeField :=
  {f | f ∈ Y ∧ maximalLifespanT ν a f ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex:38-48` eq:singularforces:
`B_{ν,a,T}={f∈F_T:T_max^ν(a,f)≤T}`. -/
-- copied from research/T10/Spec.lean:382
def breakdownSetT (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  breakdownSetInT forceClassT ν a T

/-! End declarations copied from research/T10/Spec.lean. -/

end BlowupDensity.T10.Draft

namespace BlowupDensity.T11.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## Specification-local concrete notions -/

/-- appendix-a-local-theory.tex:71-76: an order-s Fourier datum path for a
physical field on a specified time set.

Non-vacuity: every G t is a concrete complete Fourier datum representing the
actual velocity slice, rather than an unconstrained path witness. -/
def IsPeriodicSobolevPathOn (s : ℝ) (I : Set ℝ) (u : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t ∈ I, IsPeriodicDatum s (fun x ↦ u (t, x)) (G t)

/-- 02-preliminaries.tex:81-82 and appendix-a-local-theory.tex:76-77:
the tensor divergence ∇·(u⊗u), copied token-for-token from the registered
Section 4 spelling except for its periodic suffix. -/
def convectionDivergenceT (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- 02-preliminaries.tex:84-88: the scalar spatial Laplacian of a periodic
pressure field. -/
def scalarSpatialLaplacianT (p : SpaceTimeScalar) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y : Space ↦
        fderiv ℝ (fun z : Space ↦ p (t, z)) y (coordinateVector i))
      x (coordinateVector i)

/-- appendix-a-local-theory.tex:117-125: one velocity-pressure pair solves on
every strictly shorter positive horizon. This mirrors
Contracts/V2/Continuation.lean:60 token-for-token at the predicate level. -/
def SolvesBelowT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionT ν a f b, w.velocity = u ∧ w.pressure = p

/-- 02-preliminaries.tex:32-36,105-115 and
appendix-a-local-theory.tex:117-125: a common pair realizes every positive
real horizon strictly below the extended maximal lifespan.

Non-vacuity: the predicate returns full ClassicalSolutionT objects whose
velocity and normalized pressure are the displayed physical fields. -/
def IsMaximalPeriodicSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanT ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanT ν a f →
      ∃ w : ClassicalSolutionT ν a f S, w.velocity = u ∧ w.pressure = p

/-- 02-preliminaries.tex:110-114: the squared periodic H² continuation
lintegral. Divergence is represented by top, never by a junk real zero. -/
def squaredHTwoIntegralT (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    periodicSobolevENorm 2 (fun x ↦ u (t, x)) ^ 2

/-- appendix-a-local-theory.tex:149-153: positive-time translation of the
fixed force, token-for-token with Contracts/V2/Continuation.lean:50. -/
def timeShiftT (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z => f (z.1 + t₀, z.2)

/-- 02-preliminaries.tex:110-114 and appendix-a-local-theory.tex:149-155:
concrete strict extension of common fields solving below S.

Non-vacuity: the witness is a full solution on S+δ with δ>0, and both velocity
and normalized pressure agree pointwise throughout the old interval. -/
def ExtendsBeyondT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT ν a f (S + δ),
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.velocity (t, x) = u (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.pressure (t, x) = p (t, x))

/-! ## Literal checks against registered Section 4 spellings -/

/-- The periodic convection definition has exactly the registered Section 4
body (Contracts/V2/LocalTheory.lean:58-60). -/
example (u : SpaceTimeField) (t : ℝ) (x : Space) :
    convectionDivergenceT u t x =
      BlowupDensity.Contracts.V2.LocalTheory.convectionDivergence u t x := rfl

/-- The periodic time shift has exactly the registered Section 4 body
(Contracts/V2/Continuation.lean:50-51). -/
example (t₀ : ℝ) (f : SpaceTimeField) :
    timeShiftT t₀ f =
      BlowupDensity.Contracts.V2.Continuation.timeShift t₀ f := rfl

/-! ## Local regularity and local/maximal existence -/

/-- 02-preliminaries.tex:75-88,116-118 and
appendix-a-local-theory.tex:65-77: the three nonredundant regularity clauses
on one periodic classical solution and one common horizon. -/
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionT ν a f T) : Prop where
  /-- appendix-a-local-theory.tex:65-77 and 02-preliminaries.tex:116-118:
  every integer Sobolev order has a smooth datum path on the same Ico 0 T.

  Exact quantifier order: ∀ m : ℕ, ∃ G, realization, then ContDiffOn.
  Non-vacuity: G takes values in the concrete complete PeriodicSobolev carrier
  and represents the actual velocity slices. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) w.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

  /-- 02-preliminaries.tex:84-88: the normalized periodic pressure solves the
  displayed Poisson equation.

  Exact quantifier order: ∀ t ∈ Ico 0 T, ∀ x : Space.
  Non-vacuity: this equates the scalar Laplacian of the actual pressure to
  divergences of the concrete force and nonlinear tensor field. -/
  pressure_poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence
          (fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2) t x

  /-- 02-preliminaries.tex:80-83, equation projected, and
  appendix-a-local-theory.tex:76-77: the projected equation with the pressure
  gradient restored.

  Exact quantifier order: ∀ t ∈ Ioo 0 T, ∀ x : Space.
  Non-vacuity: this is a pointwise equality of physical vectors for the
  concrete solution, force, and normalized pressure. -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
      (f (t, x) - convectionDivergenceT w.velocity t x) -
        pressureGradient w.pressure t x

/-- 02-preliminaries.tex:32-34,105-109,116-118 and
appendix-a-local-theory.tex:60-77,117-125: periodic local existence,
uniqueness, and maximal gluing. This structure is Type-valued because it
carries the selected horizon as data. -/
structure PeriodicLocalTheoryAPI : Type where
  /-- 02-preliminaries.tex:105-109 and appendix-a-local-theory.tex:60-70:
  the selected common local horizon.

  Exact argument order: ν, a, f.
  Non-vacuity: this is real numerical data used by solution; positivity is
  certified by the returned ClassicalSolutionT. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ

  /-- 02-preliminaries.tex:105-109: local existence for exactly
  ∀ν, 0<ν, ∀a∈initialClassT, ∀f∈forceClassT.

  Non-vacuity: the result is a full ClassicalSolutionT on the named horizon,
  not an unspecified proposition. -/
  solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (horizon ν a f)

  /-- 02-preliminaries.tex:116-118 and appendix-a-local-theory.tex:65-77:
  all three regularity clauses hold for the selected solution on that same
  horizon.

  Exact quantifier order repeats ν,hν,a,ha,f,hf before applying solution.
  Non-vacuity: the conclusion is the concrete three-field regularity record. -/
  regularity : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)

  /-- 02-preliminaries.tex:105-109 and
  appendix-a-local-theory.tex:117-124: velocity uniqueness on the common
  interval.

  Exact quantifier order is admissible ν,a,f, then T₁,T₂,u₁,u₂,t,x.
  Non-vacuity: actual physical velocity vectors are equal pointwise. -/
  velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x)

  /-- 02-preliminaries.tex:28,84-88,105-109: the zero-mean gauge upgrades
  pressure uniqueness to literal equality.

  Exact quantifier order matches velocity_unique and ends with t,x.
  Non-vacuity: the two normalized scalar pressure representatives are equal,
  not merely their gradients. -/
  pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x)

  /-- 02-preliminaries.tex:32-34: the selected local horizon lies below the
  concrete supremal lifespan.

  Exact quantifier order is admissible ν,a,f.
  Non-vacuity: this is an order relation between two concrete horizon values. -/
  horizon_le_lifespan : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f

  /-- 02-preliminaries.tex:32-34,105-109 and
  appendix-a-local-theory.tex:123-125: local solutions glue to a maximal
  velocity and normalized pressure.

  Exact quantifier order is admissible ν,a,f, then existential u,p.
  Non-vacuity: the witnesses are actual fields with full classical
  restrictions at every presingular real horizon. -/
  exists_maximal : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p

  /-- 02-preliminaries.tex:105-109 and
  appendix-a-local-theory.tex:117-125: maximal pairs agree at every
  presingular time.

  Exact quantifier order is admissible ν,a,f, two pairs, maximality proofs,
  then t, its two bounds, and x.
  Non-vacuity: both the physical velocity and normalized scalar pressure are
  identified pointwise, with no constraints on junk values after lifespan. -/
  maximal_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)

/-! ## Squared-H² continuation -/

/-- 02-preliminaries.tex:105-114 and
appendix-a-local-theory.tex:127-156: the manuscript-strength periodic
continuation package, retaining the H¹ restart ball. -/
structure PeriodicContinuationAPI : Prop where
  /-- appendix-a-local-theory.tex:146-151: for one fixed force and compact
  restart window, one positive duration works for every restart time and every
  admissible datum in a finite H¹ ball.

  Exact quantifier order: ν,hν,f,hf,S,hS,K,hK, then ∃δ>0, followed by
  t₀∈Icc 0 S and a'∈initialClassT with its H¹ bound.
  Non-vacuity: the conclusion returns a full shifted-force solution and its
  all-order regularity on the same genuine positive interval. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

  /-- appendix-a-local-theory.tex:127-147: a finite squared-H² integral and
  Grönwall bound every integer Sobolev order uniformly below S.

  Exact quantifier order is admissible ν,a,f, S>0, u,p, SolvesBelowT,
  criterion finiteness, then ∀m,∃M<top,∀t∈Ico 0 S.
  Non-vacuity: M bounds the concrete extended norm of the actual velocity
  slice; it is finite and no real integral can silently totalize to zero. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M

  /-- appendix-a-local-theory.tex:146-153: a uniform H¹ trajectory bound
  supplies one fixed positive restart margin and an exactly patched solution.

  Exact quantifier order: ν,hν,f,hf,S,hS,K,hK, ∃δ>0 before a,u,p.
  Non-vacuity: the same δ works for every admissible initial datum and the
  returned solution agrees in velocity and normalized pressure on all [0,S). -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x))

  /-- 02-preliminaries.tex:109-114, equation criterion, and
  appendix-a-local-theory.tex:127-156: finite squared-H² integral implies
  concrete extension beyond the real endpoint S.

  Exact quantifier order is admissible ν,a,f, S>0, u,p, SolvesBelowT, then
  criterion finiteness.
  Non-vacuity: ExtendsBeyondT contains δ>0, a full larger solution, and exact
  overlap equality of both velocity and normalized pressure. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p

  /-- 02-preliminaries.tex:109-114, appendix-a-local-theory.tex:124-155,
  and 03-torus.tex:490-502: local criterion finiteness at every finite
  endpoint at or below a maximal lifespan forces global lifespan.

  Exact quantifier order is admissible ν,a,f, u,p, maximality, then
  ∀S>0 with ofReal S ≤ lifespan.
  Non-vacuity: the conclusion is the concrete extended-real equality
  maximalLifespanT ν a f = top; the non-strict ≤ endpoint is load-bearing. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-! ## Data-defined Galilean mean reduction -/

/-- appendix-a-local-theory.tex:89-93 and 03-torus.tex:395-403:
the normalized spatial mean of a velocity slice. -/
def velocityMeanT (u : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ u (t, x))

/-- appendix-a-local-theory.tex:92-99 and 03-torus.tex:397-403:
the normalized spatial mean of a force slice. -/
def forceMeanT (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ f (t, x))

/-- appendix-a-local-theory.tex:89-93: the known mean trajectory
m(t)=meanT a+∫₀ᵗ meanT(f(r,·))dr, defined from data rather than from arbitrary
off-lifespan values of a solution. -/
def galileanMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, forceMeanT f r

/-- appendix-a-local-theory.tex:92-98: the known displacement
X(t)=∫₀ᵗm(r)dr, built from the data-defined Galilean mean. -/
def galileanShiftT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  ∫ r in (0 : ℝ)..t, galileanMeanT a f r

/-- appendix-a-local-theory.tex:95-99: the transformed velocity
v(t,x)=u(t,x+X(t))-m(t), with m and X defined from a and f. -/
def galileanVelocityT (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ u (z.1, z.2 + galileanShiftT a f z.1) - galileanMeanT a f z.1

/-- appendix-a-local-theory.tex:95-100: the transformed force
h(t,x)=f(t,x+X(t))-meanT(f(t,·)). No derivative operator is applied to a
possibly nondifferentiable arbitrary function. -/
def galileanForceT (a : SpatialField) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1, z.2 + galileanShiftT a f z.1) - forceMeanT f z.1

/-- appendix-a-local-theory.tex:100-106: pressure transported by the same
data-defined spatial translation, with no additive correction. -/
def galileanPressureT (a : SpatialField) (f : SpaceTimeField)
    (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p (z.1, z.2 + galileanShiftT a f z.1)

/-- appendix-a-local-theory.tex:89-106 and 03-torus.tex:395-403:
the exact periodic mean identities and Galilean reduction. -/
structure PeriodicMeanReductionAPI : Prop where
  /-- appendix-a-local-theory.tex:89-93 and 03-torus.tex:395-403:
  the solution mean equals the known initial-plus-force mean.

  Exact quantifier order is admissible ν,a,f, then T,w,t∈Ico 0 T.
  Non-vacuity: this equates two concrete vectors, one obtained from the
  physical solution and one from an actual Bochner interval integral. -/
  mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t

  /-- appendix-a-local-theory.tex:92-98 and 03-torus.tex:397-403:
  m'(t)=meanT(f(t,·)) at interior times.

  Exact quantifier order is admissible ν,a,f, then T,w,t∈Ioo 0 T.
  Non-vacuity: HasDerivAt asserts the genuine derivative of the actual
  solution-mean curve and identifies its concrete vector derivative. -/
  mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t

  /-- appendix-a-local-theory.tex:95-106: the displayed data-defined
  Galilean fields solve the mean-free equation on the same horizon and retain
  all stated regularity.

  Exact quantifier order is admissible ν,a,f, then T,w.
  Non-vacuity: the witness is a full ClassicalSolutionT whose velocity and
  pressure equal the explicit transforms and whose regularity is carried. -/
  transformed_solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            PeriodicLocalRegularity ν (meanZeroPartT a)
              (galileanForceT a f) T v

  /-- appendix-a-local-theory.tex:89-104: the explicit centered datum and
  data-defined transformed force stay in the manuscript input classes.

  Exact quantifier order is admissible ν,a,f, then T,w.
  Non-vacuity: this is membership of the displayed physical fields in T10's
  concrete classes, with no derivative junk value. -/
  transformed_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT

  /-- appendix-a-local-theory.tex:97-103: the centered datum, transformed
  velocity, and transformed force have zero normalized torus mean.

  Exact quantifier order is admissible ν,a,f,T,w, followed by
  t∈Ico 0 T for the two time-dependent clauses.
  Non-vacuity: every conclusion is a literal Haar-integral equation for an
  explicit physical field. -/
  transformed_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          meanT (meanZeroPartT a) = 0 ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanVelocityT a f w.velocity (t, x)) = 0) ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanForceT a f (t, x)) = 0)

  /-- appendix-a-local-theory.tex:102-103: spatial translations preserve
  every periodic Sobolev norm.

  Exact quantifier order: ∀s,z, periodicity, then ∀y.
  Non-vacuity: this is equality of the concrete T10 extended norms, including
  top when no representing datum exists. -/
  translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z

/-! ## Positive-viscosity rescaling -/

/-- appendix-a-local-theory.tex:79-87: the rescaled initial velocity
ã=ν⁻¹a. -/
def unitViscosityInitialT (ν : ℝ) (a : SpatialField) : SpatialField :=
  fun x ↦ ν⁻¹ • a x

/-- appendix-a-local-theory.tex:79-87: the rescaled velocity
ũ(τ,x)=ν⁻¹u(τ/ν,x). -/
def unitViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν⁻¹ • u (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:79-87: the rescaled pressure
p̃(τ,x)=ν⁻²p(τ/ν,x), using the reconciled (ν²)⁻¹ spelling. -/
def unitViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ (ν ^ 2)⁻¹ * p (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:79-87: the rescaled force
f̃(τ,x)=ν⁻²f(τ/ν,x), using the reconciled (ν²)⁻¹ spelling. -/
def unitViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ (ν ^ 2)⁻¹ • f (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse velocity scaling
u(t,x)=νũ(νt,x). -/
def restoreViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν • u (ν * z.1, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse pressure scaling. -/
def restoreViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ν ^ 2 * p (ν * z.1, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse force scaling. -/
def restoreViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν ^ 2 • f (ν * z.1, z.2)

/-- appendix-a-local-theory.tex:79-87: equivalence of positive viscosity and
unit viscosity, including class preservation and inverse formulas. -/
structure PeriodicViscosityRescalingAPI : Prop where
  /-- appendix-a-local-theory.tex:79-87: positive-viscosity rescaling
  preserves the stated smooth periodic initial and force classes.

  Exact quantifier order is ν,hν,a,ha,f,hf.
  Non-vacuity: both explicit rescaled physical fields belong to the concrete
  T10 input sets. -/
  scaled_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT

  /-- appendix-a-local-theory.tex:86-87: inverse formulas restore velocity,
  pressure, and force.

  Exact quantifier order is ν,hν, then arbitrary u,p,f.
  Non-vacuity: the conclusion contains three equalities of full physical
  fields, not merely equality of viscosity parameters. -/
  inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f

  /-- appendix-a-local-theory.tex:79-87: every viscosity-ν solution rescales
  to a viscosity-one solution on horizon νT with preserved regularity.

  Exact quantifier order is admissible ν,a,f, then T,w.
  Non-vacuity: the witness is a full unit-viscosity solution with exact
  velocity and pressure formulas on the rescaled common interval. -/
  to_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v

  /-- appendix-a-local-theory.tex:86-87: undoing the unit-viscosity change
  restores ν, the original data, horizon T, and normalized pressure.

  Exact quantifier order is admissible ν,a,f,T, then a unit solution on νT.
  Non-vacuity: the witness is a full viscosity-ν solution with exact inverse
  field formulas and its common-interval regularity record. -/
  from_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              PeriodicLocalRegularity ν a f T w

end BlowupDensity.T11.Draft
