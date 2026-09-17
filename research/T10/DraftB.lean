import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Draft B: the periodic data layer on the unit three-torus

This is a statement-only draft for `Contracts/V1/TorusData.lean`.  Physical
fields remain unit-periodic functions on `R^3`; every Sobolev construction is
made on weighted Fourier coefficients indexed by `Z^3`.
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

/-! ## 2. Means, the zero mode, and the periodic Leray symbol -/

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

/-- `02-preliminaries.tex:28-36,75-115` prop:local: a classical periodic
solution of Navier–Stokes on `[0,T)` at viscosity `ν`, with initial velocity
`a`, prescribed force `f`, periodic velocity and pressure, and the pressure
representative fixed by `∫_T³p=0`.

The Sobolev field has quantifier order `∀ m, ∃ G, ContinuousOn G ... ∧
∀ t, ...`; hence every compact preterminal slice has the paper's smooth
Sobolev regularity without postulating an endpoint value at `T`. -/
structure ClassicalSolutionT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) where
  /-- The periodic velocity field. -/
  velocity : SpaceTimeField
  /-- The periodic scalar pressure in the zero-mean gauge. -/
  pressure : SpaceTimeScalar
  /-- The horizon is positive. -/
  horizon_pos : 0 < T
  /-- Smoothness on the closed-at-zero, open-at-`T` slab. -/
  velocity_smooth :
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Smoothness of pressure on the same slab. -/
  pressure_smooth :
    ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Unit spatial periods for velocity at every lifespan time. -/
  velocity_periodic : IsPeriodicOn (Ico (0 : ℝ) T) velocity
  /-- Unit spatial periods for pressure at every lifespan time. -/
  pressure_periodic : IsPeriodicOn (Ico (0 : ℝ) T) pressure
  /-- `u(0,·)=a`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `div u=0` on `[0,T)`. -/
  divergence :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- The momentum equation at interior times. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- Continuous integer-order Fourier data throughout the lifespan. -/
  sobolev : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T,
        IsPeriodicDatum (m : ℝ) (fun x ↦ velocity (t, x)) (G t)
  /-- The paper's unique periodic pressure representative. -/
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

end BlowupDensity.Contracts.V1.TorusData
