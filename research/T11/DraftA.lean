import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T11 blind draft A: periodic local theory and continuation

This file states the torus half of `prop:local`, its squared-`H²`
continuation criterion, the periodic Galilean mean reduction, and viscosity
rescaling.  Physical fields are unit-periodic functions on `R³`; Sobolev data
live in the weighted Fourier carrier fixed by T10.

The declarations in `BlowupDensity.T10.Draft` are the minimum verbatim subset
of `research/T10/Spec.lean` used below.  They must be deleted in favor of an
import once `T01.torus_data` is registered.
-/

noncomputable section

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

-- copied from research/T10/Spec.lean:48; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the frequency lattice of the unit
three-torus. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

-- copied from research/T10/Spec.lean:51; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: Mathlib's unit additive three-torus. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

-- copied from research/T10/Spec.lean:53; delete once T01.torus_data is registered
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
-- copied from research/T10/Spec.lean:54; delete once T01.torus_data is registered
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

-- copied from research/T10/Spec.lean:58; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: normalized Haar measure on the unit torus. -/
abbrev periodicTorusMeasure : Measure PeriodicTorus := volume

-- copied from research/T10/Spec.lean:63; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and the (P) representation fixed in
`collaboration/SECTION3_PLAN.md` §1: invariance under every positive unit
coordinate shift. Quantification over all `x` also supplies negative shifts. -/
def IsPeriodicSpatial {E : Type*} [Add E] (z : Space → E) : Prop :=
  ∀ x : Space, ∀ i : Fin 3, z (x + coordinateVector i) = z x

-- copied from research/T10/Spec.lean:68; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:28`: spatial periodicity on a specified set of times,
with time as the first spacetime coordinate. -/
def IsPeriodicOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t ∈ I, ∀ x : Space, ∀ i : Fin 3,
    z (t, x + coordinateVector i) = z (t, x)

-- copied from research/T10/Spec.lean:76; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4`, `01-introduction.tex:89`, and `TorusCube.lean:25-26`: canonical realization
of the (P) field on Mathlib's unit torus, using representatives in `(0,1]^3`.
This is the local `NSFormalization.Paper1.torusLift` definition restated
verbatim, with its one-line `toSpace` map expanded. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f ((EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) z).val))

-- copied from research/T10/Spec.lean:84; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:89`: the coefficient
`ẑ(k) = ∫_T³ z(x) exp(-2π i k·x) dx`.  This is exactly the local
`NSFormalization.Paper1.periodicFourierCoeff`, restated so the eventual
contract needs no local implementation import. -/
def periodicFourierCoeff (f : Space → ℂ) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

-- copied from research/T10/Spec.lean:89; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-84`: the squared Bessel weight
`1 + 4π²|k|²` in the unit-period convention. -/
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

-- copied from research/T10/Spec.lean:93; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4`: scalar complete `ℓ²(Z³;ℂ)` coefficient data. -/
abbrev PeriodicScalarData := lp (fun _ : PeriodicFrequency ↦ ℂ) 2

-- copied from research/T10/Spec.lean:97; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:103`: three scalar coefficient sequences with the
Euclidean (`PiLp 2`) product norm. -/
abbrev PeriodicVectorData := WithLp 2 (Fin 3 → PeriodicScalarData)

-- copied from research/T10/Spec.lean:101; delete once T01.torus_data is registered
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

-- copied from research/T10/Spec.lean:119; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the complete real three-vector Sobolev datum
at order `s`.  An element is the *weighted* sequence
`(1+4π²|k|²)^(s/2) ẑ(k)` in `ℓ²`; `s` is a phantom index recording
the realization represented by that sequence. -/
abbrev PeriodicSobolev (_s : ℝ) := realPeriodicSubmodule

-- copied from research/T10/Spec.lean:134; delete once T01.torus_data is registered
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

-- copied from research/T10/Spec.lean:143; delete once T01.torus_data is registered
/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the total `H^s(T³)` extended norm of a
physical field, defined as the infimum of the norms of all representing data.
The empty infimum is `⊤`. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicDatum s z A}, ‖A.1‖ₑ

-- copied from research/T10/Spec.lean:150; delete once T01.torus_data is registered
/-- `03-torus.tex:395-401`: the normalized spatial mean of a real vector
field on the unit torus. -/
def meanT (z : SpatialField) : Space :=
  ∫ y : PeriodicTorus, torusLift z y ∂periodicTorusMeasure

-- copied from research/T10/Spec.lean:158; delete once T01.torus_data is registered
/-- `03-torus.tex:395-401`: `z - ∫_T³ z`, the mean-free part of a periodic
field. -/
def meanZeroPartT (z : SpatialField) : SpatialField := fun x ↦ z x - meanT z

-- copied from research/T10/Spec.lean:181; delete once T01.torus_data is registered
/-- `03-torus.tex:395-411`: a physical field has zero normalized torus mean. -/
def IsMeanZeroT (z : SpatialField) : Prop := meanT z = 0

-- copied from research/T10/Spec.lean:257; delete once T01.torus_data is registered
/-- `01-introduction.tex:118-140`: `G` is the order-`s` datum trajectory of
the periodic physical field `f` at every nonnegative time. -/
def IsPeriodicSobolevPath (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsPeriodicDatum s (fun x ↦ f (t, x)) (G t)

-- copied from research/T10/Spec.lean:272; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:9` eq:inputspaces: the lifted realization of
`C∞_div(T³;R³)`. -/
def initialClassT : Set SpatialField :=
  {a | ContDiff ℝ ∞ a ∧ IsPeriodicSpatial a ∧ IsSolenoidal a}

-- copied from research/T10/Spec.lean:278; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:10,23-26` eq:inputspaces:
`C_c∞(T³×(0,∞);R³)` in the periodic-functions-on-`R³` realization.
Only time support is compact in the lift. -/
def MemForceT (f : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ f ∧
    IsPeriodicOn univ f ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ univ

-- copied from research/T10/Spec.lean:284; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:10` eq:inputspaces: the torus force class `F_T`. -/
def forceClassT : Set SpaceTimeField := {f | MemForceT f}

-- copied from research/T10/Spec.lean:290; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:28,84-88`: the normalized spatial mean of a
periodic pressure slice. -/
def pressureMeanT (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  ∫ y : PeriodicTorus, torusLift (fun x ↦ p (t, x)) y ∂periodicTorusMeasure

-- copied from research/T10/Spec.lean:295; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:28,84-88`: the pressure gauge `∫_T³ p(t)=0`,
imposed at every time in `I`. -/
def PressureGaugeT (I : Set ℝ) (p : SpaceTimeScalar) : Prop :=
  ∀ t ∈ I, pressureMeanT p t = 0

-- copied from research/T10/Spec.lean:311; delete once T01.torus_data is registered
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

-- copied from research/T10/Spec.lean:364; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:32-36,105-115` prop:local: the maximal classical
lifespan, as the supremum of horizons carrying a periodic classical solution.
Global lifespan is `⊤`; the empty supremum is `0`. -/
def maximalLifespanT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionT ν a f S), ENNReal.ofReal S

end BlowupDensity.T10.Draft

namespace BlowupDensity.T11.DraftA

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## Specification-local concrete notions -/

/-- **Needs registration.** `appendix-a-local-theory.tex:71-76`: interval-local
version of T10's global `IsPeriodicSobolevPath`.  A global auxiliary physical
path is allowed outside `I`, but it agrees with `f` on `I × R³`. -/
def IsPeriodicSobolevPathOn (I : Set ℝ) (s : ℝ) (f : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∃ f' : SpaceTimeField, EqOn f' f (I ×ˢ (univ : Set Space)) ∧
    IsPeriodicSobolevPath s f' G

/-- **Needs registration.** `02-preliminaries.tex:111-114`: the physical
`H^s(T³)` extended norm of the slice at time `t`. -/
def periodicSobolevNormAtT (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicSobolevENorm s (fun x : Space ↦ u (t, x))

/-- **Needs registration.** `02-preliminaries.tex:81` and
`appendix-a-local-theory.tex:76-77`: `∇·(u⊗u)`, written as
`∑j ∂j (u_j u)`. -/
def convectionDivergenceT (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space ↦ (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- **Needs registration.** `02-preliminaries.tex:84-88`: the scalar spatial
Laplacian of a pressure field. -/
def scalarSpatialLaplacianT (p : SpaceTimeScalar) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y : Space ↦
        fderiv ℝ (fun z : Space ↦ p (t, z)) y (coordinateVector i))
      x (coordinateVector i)

/-- **Needs registration.** `appendix-a-local-theory.tex:117-125`: one pair of
fields solves the equation on every strictly shorter positive horizon. -/
def SolvesBelowT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionT ν a f b, w.velocity = u ∧ w.pressure = p

/-- **Needs registration.** `02-preliminaries.tex:111-114` (`eq:criterion`):
the squared `H²(T³)` `lintegral` on `(0,S)`.  `ℝ≥0∞` is used because T10's
physical Sobolev quantity is already an extended norm; `≠ ⊤` expresses
finiteness without a `toReal` junk value. -/
def squaredHTwoIntegralT (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S, periodicSobolevNormAtT 2 u t ^ (2 : ℝ)

/-- **Needs registration.** `appendix-a-local-theory.tex:147-153`: translate
the fixed force when restarting at time `t₀`. -/
def timeShiftT (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1 + t₀, z.2)

/-! ## Local regularity and the maximal periodic solution -/

/-- The periodic analogue of Section 4's `ManuscriptLocalRegularity`, on the
one common interval supplied by `prop:local`. -/
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionT ν a f T) : Prop where
  /-- `appendix-a-local-theory.tex:67-76`: for every integer `m`, one
  order-`m` Fourier datum path represents the velocity and is `C∞` in time on
  the same `[0,T)`.

  Exact quantifier order: `∀ m : ℕ, ∃ G`, followed by path realization and
  `ContDiffOn` on `Ico 0 T`.  Non-vacuity: `G` lies in the concrete complete
  `PeriodicSobolev m` carrier and represents the actual velocity slices. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (Ico (0 : ℝ) T) (m : ℝ) w.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

  /-- `02-preliminaries.tex:80-83` (`eq:projected`) and
  `appendix-a-local-theory.tex:76-77`: the projected equation, with the
  gradient part of the force restored as `∇p`.

  Exact quantifier order: `∀ t ∈ Ioo 0 T, ∀ x : Space`.  Non-vacuity: this is
  a pointwise equality of physical vectors, not a predicate parameter. -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
      (f (t, x) - convectionDivergenceT w.velocity t x) -
        pressureGradient w.pressure t x

  /-- `02-preliminaries.tex:84-88`: the periodic pressure is the zero-mean
  solution of `Δp = div f - ∂i∂j(u_i u_j)`.

  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x : Space`.  Non-vacuity: the
  conclusion equates the scalar Laplacian of the actual pressure to the
  divergence of concrete physical fields. -/
  pressure_poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence
          (fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2) t x

  /-- `02-preliminaries.tex:28,84-88`: velocity and pressure are spatially
  periodic, and the pressure representative has zero normalized torus mean.

  Exact quantifier order is the conjunction of `IsPeriodicOn` for velocity,
  `IsPeriodicOn` for pressure, then `PressureGaugeT`, all on `Ico 0 T`.
  Non-vacuity: the last conjunct fixes the scalar pressure rather than merely
  its gradient. -/
  periodic_and_pressure_gauge :
    IsPeriodicOn (Ico (0 : ℝ) T) w.velocity ∧
      IsPeriodicOn (Ico (0 : ℝ) T) w.pressure ∧
        PressureGaugeT (Ico (0 : ℝ) T) w.pressure

/-- A maximal periodic solution is represented by one velocity-pressure pair
on the physical half-line, whose restrictions solve below every real endpoint
at or below `maximalLifespanT`.  This is used instead of attempting to pass an
`ℝ≥0∞` endpoint to `ClassicalSolutionT`, whose horizon is real. -/
structure PeriodicMaximalSolution (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) where
  /-- `02-preliminaries.tex:105-110`: the common maximal velocity field.

  Exact quantifier order: this is data after `(ν,a,f)`.  Non-vacuity: it is an
  actual `SpaceTimeField`, consumed by every shorter classical restriction. -/
  velocity : SpaceTimeField

  /-- `02-preliminaries.tex:84-110`: the common zero-mean pressure field.

  Exact quantifier order: this is data after `(ν,a,f)`.  Non-vacuity: it is an
  actual scalar field shared by the normalized shorter solutions. -/
  pressure : SpaceTimeScalar

  /-- `02-preliminaries.tex:32-34,105-110`: admissible data have positive
  maximal lifespan.

  Exact quantifier order: no further variables.  Non-vacuity: this is strict
  positivity in `ℝ≥0∞`, ruling out the empty-supremum value `0`. -/
  lifespan_pos : 0 < maximalLifespanT ν a f

  /-- `appendix-a-local-theory.tex:117-125`: patching supplies the same fields
  on every finite `[0,S)` contained in the maximal lifespan, including the
  finite endpoint in the weaker `SolvesBelowT` sense.

  Exact quantifier order: `∀ S : ℝ`, `0 < S`, then
  `ENNReal.ofReal S ≤ maximalLifespanT`.  Non-vacuity: for every `b<S` the
  conclusion produces a concrete `ClassicalSolutionT` whose two fields are
  exactly the displayed maximal fields. -/
  solves_below : ∀ S : ℝ, 0 < S →
    ENNReal.ofReal S ≤ maximalLifespanT ν a f →
      SolvesBelowT ν a f S velocity pressure

/-- The existence, uniqueness, and maximal-lifespan half of periodic
`prop:local`.  A named real local horizon is retained for restart consumers;
the maximal object separately uses the extended-real supremum. -/
structure PeriodicLocalTheoryAPI : Type where
  /-- `02-preliminaries.tex:105-110` and
  `appendix-a-local-theory.tex:62-70`: a single named local horizon for each
  viscosity, datum, and force.

  Exact quantifier order is encoded by the function arguments `(ν,a,f)`;
  admissibility is imposed by `solution`.  Non-vacuity: this is a real horizon,
  not an opaque proposition, and its strict positivity is carried by the
  returned solution. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ

  /-- `02-preliminaries.tex:105-110`: periodic local existence for exactly
  `∀ ν>0, ∀ a∈X_T, ∀ f∈F_T`.

  Exact quantifier order: `∀ ν`, `0<ν`, `∀ a`, `a∈initialClassT`, `∀ f`,
  `f∈forceClassT`.  Non-vacuity: the result is a concrete
  `ClassicalSolutionT` on the named horizon. -/
  solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (horizon ν a f)

  /-- `02-preliminaries.tex:116-120` and
  `appendix-a-local-theory.tex:67-76`: all Sobolev orders and the periodic
  pressure prescription hold for the selected solution on that same horizon.

  Exact quantifier order matches `solution`, followed by its three membership
  proofs.  Non-vacuity: the conclusion is the concrete four-field
  `PeriodicLocalRegularity` record, so “one common interval” is enforced by
  the single occurrence of `horizon ν a f`. -/
  regularity : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)

  /-- `02-preliminaries.tex:105-110` and
  `appendix-a-local-theory.tex:117-124`: two solutions with identical data have
  equal velocities on their common interval.

  Exact quantifier order: `∀ ν>0, ∀ a∈X_T, ∀ f∈F_T`, then horizons and the two
  solutions, then `∀ t∈Ico 0 (min T₁ T₂), ∀x`.  Non-vacuity: the conclusion is
  pointwise equality of the physical velocities. -/
  velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x)

  /-- `02-preliminaries.tex:28,84-88,105-110`: the zero-mean gauge makes the
  pressure determined as well as the velocity.

  Exact quantifier order is the same as `velocity_unique`, ending with
  `∀t∈Ico 0 (min T₁ T₂), ∀x`.  Non-vacuity: this is exact scalar equality,
  stronger than equality modulo a time-dependent constant because both
  pressures already have mean zero. -/
  pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x)

  /-- `02-preliminaries.tex:32-34,105-110` and
  `appendix-a-local-theory.tex:124-125`: the unique local solutions patch to a
  maximal smooth velocity and normalized pressure.

  Exact quantifier order: `∀ ν>0, ∀ a∈X_T, ∀ f∈F_T`.  Non-vacuity: the result
  contains actual common fields and classical restrictions throughout the
  supremal lifespan. -/
  maximal_solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        PeriodicMaximalSolution ν a f

  /-- `02-preliminaries.tex:105-110`, the word “unique” at maximal lifespan.

  Exact quantifier order: admissible `(ν,a,f)`, two maximal objects, a positive
  real `S` at or below their common lifespan, then `∀t∈Ico 0 S, ∀x`.
  Non-vacuity: both velocity and normalized pressure are identified pointwise. -/
  maximal_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ U V : PeriodicMaximalSolution ν a f,
          ∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanT ν a f →
            ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
              U.velocity (t, x) = V.velocity (t, x) ∧
                U.pressure (t, x) = V.pressure (t, x)

  /-- `02-preliminaries.tex:32-34` and
  `appendix-a-local-theory.tex:124-125`: the selected positive local horizon is
  bounded above by the supremal lifespan.

  Exact quantifier order: `∀ ν>0, ∀ a∈X_T, ∀ f∈F_T`.  Non-vacuity: this is an
  order relation between the concrete named horizon and `maximalLifespanT`. -/
  horizon_le_maximal : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f

/-! ## Squared-H² continuation -/

/-- The torus continuation package proved in
`appendix-a-local-theory.tex:127-156`.  It keeps the manuscript's `H¹`
restart bound rather than Section 4's implementation-driven `H⁷` narrowing. -/
structure PeriodicContinuationAPI : Prop where
  /-- `appendix-a-local-theory.tex:147-152`: for one fixed original force and
  one compact restart window, a finite `H¹` datum ball has a common positive
  existence duration for every shifted force `f(t₀+·)`.

  Exact quantifier order: `∀ν>0, ∀f∈F_T, ∀S≥0, ∀K<∞, ∃δ>0`, then
  `∀t₀∈[0,S], ∀a'∈X_T` with `H¹` norm at most `K`.  Non-vacuity: the conclusion
  returns a concrete shifted-force `ClassicalSolutionT` on `δ`, together with
  all-order regularity on that same interval.

  The result is stated directly rather than through `PeriodicLocalTheoryAPI.horizon`:
  `timeShiftT t₀ f` may be nonzero at its new time zero and therefore need not
  lie in T10's test-force class `forceClassT`. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

  /-- `appendix-a-local-theory.tex:129-147`: finiteness of the squared `H²`
  integral and Grönwall bound every integer Sobolev order uniformly up to `S`.

  Exact quantifier order: admissible `(ν,a,f)`, `S>0`, common fields solving
  below `S`, the finite criterion, then `∀m, ∃M<∞, ∀t∈[0,S)`.
  Non-vacuity: `M` is a finite extended real bounding the physical T10
  `periodicSobolevENorm`, not a bound on an auxiliary proposition. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S, periodicSobolevNormAtT (m : ℝ) u t ≤ M

  /-- `appendix-a-local-theory.tex:147-154`: a uniform `H¹` trajectory bound
  supplies one fixed positive restart margin and a patched solution on
  `[0,S+δ)`.

  Exact quantifier order: `∀ν>0, ∀f∈F_T, ∀S>0, ∀K<∞, ∃δ>0`, then the initial
  datum, common solution fields, and their `H¹` bound.  Non-vacuity: the result
  is a concrete classical solution on the strictly larger horizon `S+δ`, with
  exact velocity and normalized-pressure agreement on `[0,S)`. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S, periodicSobolevNormAtT 1 u t ≤ K) →
                  ∃ V : ClassicalSolutionT ν a f (S + δ),
                    ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                      V.velocity (t, x) = u (t, x) ∧ V.pressure (t, x) = p (t, x)

  /-- `02-preliminaries.tex:105-114` (`eq:criterion`) and
  `appendix-a-local-theory.tex:127-156`: if `S` is a positive real endpoint
  (hence `S<∞`) and `∫₀^S ‖u(t)‖²_{H²(T³)}dt < ∞`, the solution extends beyond
  `S`.

  Exact quantifier order: `∀ν>0, ∀a∈X_T, ∀f∈F_T, ∀S>0`, common fields solving
  below `S`, then finiteness.  Non-vacuity: “extends” is rendered by
  `∃T>S, ∃V : ClassicalSolutionT ... T` with exact velocity and normalized
  pressure agreement on all of `[0,S)`. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∃ T : ℝ, S < T ∧ ∃ V : ClassicalSolutionT ν a f T,
                ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                  V.velocity (t, x) = u (t, x) ∧ V.pressure (t, x) = p (t, x)

  /-- `02-preliminaries.tex:105-114` and
  `appendix-a-local-theory.tex:124-155`: the maximal-lifespan form of the same
  criterion—local finiteness at every finite endpoint forces global lifespan.

  Exact quantifier order: admissible `(ν,a,f)`, a maximal solution object, then
  `∀S>0` at or below its lifespan and the finite integral.  Non-vacuity: the
  conclusion is the concrete equality `maximalLifespanT ν a f = ⊤`. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ U : PeriodicMaximalSolution ν a f,
          (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanT ν a f →
            squaredHTwoIntegralT S U.velocity ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-! ## Periodic mean reduction -/

/-- **Needs registration.** `appendix-a-local-theory.tex:89-99`: the spatial
mean `m(t)` of a periodic velocity. -/
def solutionMeanT (u : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x : Space ↦ u (t, x))

/-- **Needs registration.** `appendix-a-local-theory.tex:92-94`: the known
mean trajectory determined by the initial mean and the force mean. -/
def prescribedMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, meanT (fun x : Space ↦ f (r, x))

/-- **Needs registration.** `appendix-a-local-theory.tex:93-99`:
`X(t)=∫₀ᵗm(r)dr`. -/
def galileanShiftT (m : ℝ → Space) (t : ℝ) : Space :=
  ∫ r in (0 : ℝ)..t, m r

/-- **Needs registration.** `appendix-a-local-theory.tex:95-102`:
`v(t,x)=u(t,x+X(t))-m(t)`. -/
def galileanVelocityT (u : SpaceTimeField) (m : ℝ → Space) : SpaceTimeField :=
  fun z ↦ u (z.1, z.2 + galileanShiftT m z.1) - m z.1

/-- **Needs registration.** `appendix-a-local-theory.tex:95-102`:
`h(t,x)=f(t,x+X(t))-m'(t)`.  The Fréchet derivative is evaluated in the
positive unit time direction. -/
def galileanForceT (f : SpaceTimeField) (m : ℝ → Space) : SpaceTimeField :=
  fun z ↦ f (z.1, z.2 + galileanShiftT m z.1) - fderiv ℝ m z.1 1

/-- **Needs registration.** `appendix-a-local-theory.tex:100-106`: the pressure
under the same time-dependent spatial translation. -/
def galileanPressureT (p : SpaceTimeScalar) (m : ℝ → Space) : SpaceTimeScalar :=
  fun z ↦ p (z.1, z.2 + galileanShiftT m z.1)

/-- The exact periodic Galilean reduction used in Appendix A and consumed by
T20. -/
structure PeriodicMeanReductionAPI : Prop where
  /-- `appendix-a-local-theory.tex:89-94,154`: the solution mean equals the
  initial mean plus the time integral of the force mean.

  Exact quantifier order: `∀ν>0, ∀a∈X_T, ∀f∈F_T, ∀T`, a classical solution,
  then `∀t∈Ico 0 T`.  Non-vacuity: this is equality of two concrete vectors in
  `Space`, with an actual Bochner interval integral. -/
  mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            solutionMeanT w.velocity t = prescribedMeanT a f t

  /-- `appendix-a-local-theory.tex:92-100`: `m'(t)=∫_{T³}f(t,x)dx`.

  Exact quantifier order: admissible `(ν,a,f)`, a horizon and solution, then
  `∀t∈Ioo 0 T`.  Non-vacuity: `HasDerivAt` asserts the genuine derivative of
  the concrete mean curve and identifies it with the concrete force mean. -/
  mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (solutionMeanT w.velocity)
              (meanT (fun x : Space ↦ f (t, x))) t

  /-- `appendix-a-local-theory.tex:95-106`: with
  `m(t)=meanT(u(t,·))`, the translated field solves the viscosity-`ν`
  mean-free equation with force `f(t,x+∫m)-m'(t)` and translated pressure.

  Exact quantifier order: admissible `(ν,a,f)`, a horizon and classical
  solution, followed by the locally bound definition of `m`.  Non-vacuity: the
  conclusion returns a concrete `ClassicalSolutionT` for the transformed data,
  with all three physical fields fixed by exact equalities. -/
  transformed_solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          let m : ℝ → Space := solutionMeanT w.velocity
          ∃ V : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT f m) T,
            V.velocity = galileanVelocityT w.velocity m ∧
              V.pressure = galileanPressureT w.pressure m

  /-- `appendix-a-local-theory.tex:97-103`: the transformed velocity has zero
  torus mean at every time of the original lifespan.

  Exact quantifier order: admissible data, solution, the local definition of
  `m`, then `∀t∈Ico 0 T`.  Non-vacuity: the conclusion is the literal Haar
  integral equation `IsMeanZeroT` for the transformed physical slice. -/
  transformed_velocity_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          let m : ℝ → Space := solutionMeanT w.velocity
          ∀ t ∈ Ico (0 : ℝ) T,
            IsMeanZeroT (fun x : Space ↦ galileanVelocityT w.velocity m (t, x))

  /-- `appendix-a-local-theory.tex:98-103`: after subtracting `m'`, the
  transformed force is mean zero.

  Exact quantifier order: admissible data, solution, the local definition of
  `m`, then `∀t∈Ioo 0 T`.  Non-vacuity: the conclusion is the literal Haar
  integral equation for the displayed transformed force, not a named
  “mean-free equation” placeholder. -/
  transformed_force_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          let m : ℝ → Space := solutionMeanT w.velocity
          ∀ t ∈ Ioo (0 : ℝ) T,
            IsMeanZeroT (fun x : Space ↦ galileanForceT f m (t, x))

  /-- `appendix-a-local-theory.tex:103`: spatial translations preserve every
  periodic Sobolev norm.

  Exact quantifier order: `∀s`, a periodic physical field `z`, then a
  translation vector `y`.  Non-vacuity: this is equality of the concrete T10
  extended norms, including the possibility `⊤` when no datum exists. -/
  translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x : Space ↦ z (x + y)) =
        periodicSobolevENorm s z

/-! ## Viscosity rescaling -/

/-- **Needs registration.** `appendix-a-local-theory.tex:79-87`: the rescaled
initial datum `ν⁻¹a`. -/
def viscosityRescaledInitialT (ν : ℝ) (a : SpatialField) : SpatialField :=
  fun x ↦ ν⁻¹ • a x

/-- **Needs registration.** `appendix-a-local-theory.tex:79-87`:
`ũ(τ,x)=ν⁻¹u(τ/ν,x)`. -/
def viscosityRescaledVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν⁻¹ • u (z.1 / ν, z.2)

/-- **Needs registration.** `appendix-a-local-theory.tex:79-87`:
`p̃(τ,x)=ν⁻²p(τ/ν,x)`. -/
def viscosityRescaledPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ (ν⁻¹ * ν⁻¹) * p (z.1 / ν, z.2)

/-- **Needs registration.** `appendix-a-local-theory.tex:79-87`:
`f̃(τ,x)=ν⁻²f(τ/ν,x)`. -/
def viscosityRescaledForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ (ν⁻¹ * ν⁻¹) • f (z.1 / ν, z.2)

/-- **Needs registration.** The inverse velocity scaling used when “undoing”
the change at `appendix-a-local-theory.tex:86-87`. -/
def viscosityUnscaledVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν • u (ν * z.1, z.2)

/-- **Needs registration.** The inverse pressure scaling used at
`appendix-a-local-theory.tex:86-87`. -/
def viscosityUnscaledPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ν ^ 2 * p (ν * z.1, z.2)

/-- Appendix A's equivalence between positive viscosity and unit viscosity. -/
structure PeriodicViscosityRescalingAPI : Prop where
  /-- `appendix-a-local-theory.tex:79-87`: a viscosity-`ν` solution on
  `[0,T)` rescales to a viscosity-one solution on `[0,νT)` with the displayed
  data and fields.

  Exact quantifier order: `∀ν>0, ∀a∈X_T, ∀f∈F_T, ∀T`, then the solution.
  Non-vacuity: the result is a concrete unit-viscosity `ClassicalSolutionT`,
  and both of its fields are fixed by exact rescaling formulas. -/
  to_unit_viscosity : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ W : ClassicalSolutionT 1 (viscosityRescaledInitialT ν a)
              (viscosityRescaledForceT ν f) (ν * T),
            W.velocity = viscosityRescaledVelocityT ν w.velocity ∧
              W.pressure = viscosityRescaledPressureT ν w.pressure

  /-- `appendix-a-local-theory.tex:86-87`: undoing the change converts a
  unit-viscosity solution for the rescaled data back to viscosity `ν` on the
  horizon divided by `ν`.

  Exact quantifier order: `∀ν>0, ∀a∈X_T, ∀f∈F_T, ∀T`, then the rescaled
  unit-viscosity solution.  Non-vacuity: the result is a concrete
  viscosity-`ν` `ClassicalSolutionT` with exact inverse field formulas. -/
  from_unit_viscosity : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ W : ClassicalSolutionT 1 (viscosityRescaledInitialT ν a)
              (viscosityRescaledForceT ν f) T,
            ∃ w : ClassicalSolutionT ν a f (T / ν),
              w.velocity = viscosityUnscaledVelocityT ν W.velocity ∧
                w.pressure = viscosityUnscaledPressureT ν W.pressure

end BlowupDensity.T11.DraftA
