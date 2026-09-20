import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# T11 blind draft B: periodic local theory and continuation

Statement-only specification of Proposition `prop:local` on the unit
three-torus.  Physical fields use the periodic-on-`R^3` representation fixed by
Section 3, while Sobolev assertions use the reconciled T10 Fourier-data
vocabulary.  No local implementation module is imported.

The T10 declarations used below are copied verbatim because `research/` is not
an import root.  Each copied block is marked with its source line; it should be
deleted once contract `T01.torus_data` is registered.
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

-- copied from research/T10/Spec.lean:231; delete once T01.torus_data is registered
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

-- copied from research/T10/Spec.lean:242; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:76-80`: `B` is the same-order real Sobolev datum
obtained from `A` by the periodic Leray projector.  This graph form records the
exact quantifier order without assuming the later boundedness proof. -/
def IsPeriodicLerayDatum {s : ℝ} (A B : PeriodicSobolev s) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k = periodicLeray s A i k

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

-- copied from research/T10/Spec.lean:300; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:84-88` and `03-torus.tex:319`: subtract the
normalized spatial mean from each pressure slice. -/
def normalizePressureT (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p z - pressureMeanT p z.1

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

-- copied from research/T10/Spec.lean:369; delete once T01.torus_data is registered
/-- `02-preliminaries.tex:35-36`: a periodic reference solution is regular
through `T` when it has a classical extension to `T+δ` for some `δ>0`. -/
def RegularThroughT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))

end BlowupDensity.T10.Draft

namespace BlowupDensity.T11.DraftB

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## Specification-local notions -/

-- needs registration: interval-local counterpart of T10 `IsPeriodicSobolevPath`.
/-- `appendix-a-local-theory.tex:71-76`: an order-`s` Fourier datum path for a
physical field on a specified time set.  T10's `IsPeriodicSobolevPath` is
future-global (appropriate for forces); a possibly singular solution needs
this interval-local version. -/
def IsPeriodicSobolevPathOn (s : ℝ) (I : Set ℝ) (u : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t ∈ I, IsPeriodicDatum s (fun x ↦ u (t, x)) (G t)

-- needs registration: periodic spelling of the A01 convection divergence.
/-- `02-preliminaries.tex:81-82` and `appendix-a-local-theory.tex:76-77`:
the tensor divergence `∇·(u⊗u)`. -/
def convectionDivergenceT (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

-- needs registration: graph form of the periodic Helmholtz decomposition.
/-- `02-preliminaries.tex:76-87`: `G=(I-P)w`, expressed with T10 order-zero
Fourier data.  The fourth conjunct says that `w-G` has exactly the Leray datum
of `w`; the separate datum for `G` prevents an untyped or non-integrable
gradient from satisfying the relation. -/
def IsPeriodicLerayComplementT (w G : SpatialField) : Prop :=
  ∃ (A B C : PeriodicSobolev 0),
    IsPeriodicDatum 0 w A ∧
      IsPeriodicDatum 0 G B ∧
      IsPeriodicDatum 0 (fun x ↦ w x - G x) C ∧
      IsPeriodicLerayDatum A C

/-! ## Local regularity on one common interval -/

/-- The torus analogue of Section 4's `ManuscriptLocalRegularity`.  Every
clause is imposed on the same `ClassicalSolutionT` and the same horizon `T`, so
the `∀ m` field below records the appendix's one common interval for all
Sobolev orders. -/
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (u : ClassicalSolutionT ν a f T) : Prop where
  /-- `appendix-a-local-theory.tex:67-76`: for every integer order there is a
  Fourier datum path, smooth in time on the one common interval `[0,T)`.

  Exact quantifier order: `∀ m : ℕ, ∃ G`, then datum membership on every
  `t ∈ Ico 0 T`, then `ContDiffOn`.  Non-vacuity: `G t` is an actual element of
  the complete real `PeriodicSobolev m` carrier representing the physical
  velocity slice. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) u.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

  /-- `02-preliminaries.tex:107-114` and
  `appendix-a-local-theory.tex:71-76`: every integer Sobolev norm of every
  slice in the lifespan is finite.

  Exact quantifier order: `∀ m : ℕ, ∀ t ∈ Ico 0 T`.  Non-vacuity: the
  conclusion rules out `⊤` for the concrete T10 extended norm; it is not a
  bare membership slogan. -/
  sobolev_enorm_finite : ∀ m : ℕ, ∀ t ∈ Ico (0 : ℝ) T,
    periodicSobolevENorm (m : ℝ) (fun x ↦ u.velocity (t, x)) ≠ ⊤

  /-- `02-preliminaries.tex:76-87` and
  `appendix-a-local-theory.tex:76-77`: the pressure gradient is the periodic
  Leray complement of `f-∇·(u⊗u)`, including at the initial endpoint.

  Exact quantifier order: `∀ t ∈ Ico 0 T`.  Non-vacuity: the conclusion
  supplies three concrete order-zero Fourier data and pins their coefficients
  by the T10 Leray graph. -/
  pressure_recovery : ∀ t ∈ Ico (0 : ℝ) T,
    IsPeriodicLerayComplementT
      (fun x ↦ f (t, x) - convectionDivergenceT u.velocity t x)
      (fun x ↦ pressureGradient u.pressure t x)

  /-- `02-preliminaries.tex:81-83` eq:projected and
  `appendix-a-local-theory.tex:76-77`: the projected equation, written as the
  forced convection residual minus the recovered gradient.

  Exact quantifier order: `∀ t ∈ Ioo 0 T, ∀ x : Space`.  Non-vacuity: this is
  a pointwise equality of vectors for the concrete solution fields, not an
  unspecified equation predicate. -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
      (f (t, x) - convectionDivergenceT u.velocity t x) -
        pressureGradient u.pressure t x

  /-- `02-preliminaries.tex:28`: the velocity has unit spatial periods on its
  entire lifespan.

  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x, ∀ i` through `IsPeriodicOn`.
  Non-vacuity: the conclusion is equality of the actual velocity values at
  `x+e_i` and `x`. -/
  velocity_periodic : IsPeriodicOn (Ico (0 : ℝ) T) u.velocity

  /-- `02-preliminaries.tex:28,84-103`: the recovered scalar pressure has unit
  spatial periods.

  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x, ∀ i` through `IsPeriodicOn`.
  Non-vacuity: this excludes the affine-pressure ambiguity mentioned at
  `02-preliminaries.tex:101-103`. -/
  pressure_periodic : IsPeriodicOn (Ico (0 : ℝ) T) u.pressure

  /-- `02-preliminaries.tex:28,84-88` and
  `appendix-a-local-theory.tex:101-106`: the pressure representative has zero
  normalized Haar mean at every time of the lifespan.

  Exact quantifier order: `∀ t ∈ Ico 0 T` through `PressureGaugeT`.
  Non-vacuity: this is the actual scalar Bochner integral equation
  `pressureMeanT p t = 0`. -/
  pressure_gauge : PressureGaugeT (Ico (0 : ℝ) T) u.pressure

  /-- `02-preliminaries.tex:84-88`: subtracting the pressure mean fixes the
  given representative pointwise on its lifespan.

  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x : Space`.  Non-vacuity: this
  identifies concrete scalar values of `normalizePressureT u.pressure` and
  `u.pressure`, rather than merely repeating a gauge predicate. -/
  pressure_normalized : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    normalizePressureT u.pressure (t, x) = u.pressure (t, x)

/-! ## Existence, uniqueness, and the maximal solution -/

-- needs registration: a single pair of fields realizing all preterminal horizons.
/-- `02-preliminaries.tex:32-36,105-115` and
`appendix-a-local-theory.tex:117-125`: one velocity and one normalized pressure
form the maximal periodic solution when their restrictions are regular
classical solutions on every real horizon strictly below the extended
lifespan.  The maximal endpoint itself is not used as a real horizon: it may
be `⊤`, and even when finite the solution is defined only on the half-open
interval. -/
def IsMaximalPeriodicSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanT ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanT ν a f →
      ∃ w : ClassicalSolutionT ν a f S,
        w.velocity = u ∧ w.pressure = p ∧ PeriodicLocalRegularity ν a f S w

/-- The periodic local-theory interface stated by `prop:local`.  It chooses one
positive local horizon for consumers, and separately packages the unique
maximal pair on the union of all preterminal intervals.  This avoids pretending
that an `ℝ≥0∞` lifespan is itself a real endpoint carrying a solution. -/
structure PeriodicLocalTheoryAPI where
  /-- `02-preliminaries.tex:105-109` and
  `appendix-a-local-theory.tex:60-70`: the selected common local horizon.

  Exact argument order: `ν`, then `a`, then `f`.  Non-vacuity: this is real
  numerical data used as the horizon of the next field; its positivity is
  certified by that solution's `horizon_pos`. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ

  /-- `02-preliminaries.tex:105-109` and
  `appendix-a-local-theory.tex:60-70`: local existence for precisely the
  manuscript's periodic datum classes.

  Exact quantifier order: `∀ ν, 0 < ν → ∀ a, a ∈ initialClassT → ∀ f,
  f ∈ forceClassT → ...`.  Non-vacuity: the conclusion is a full
  `ClassicalSolutionT` on the selected horizon, not `Nonempty Prop`. -/
  solution : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ClassicalSolutionT ν a f (horizon ν a f)

  /-- `02-preliminaries.tex:116-119` and
  `appendix-a-local-theory.tex:67-76`: all Sobolev orders and the pressure
  recovery hold on the same selected interval.

  Exact quantifier order repeats `ν`, its positivity, `a`, its membership,
  `f`, and its membership before applying `solution`.  Non-vacuity: the result
  is the concrete seven-clause regularity record for that exact solution. -/
  regularity : ∀ (ν : ℝ) (hν : 0 < ν) (a : SpatialField)
    (ha : a ∈ initialClassT) (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)

  /-- `02-preliminaries.tex:105-109` and
  `appendix-a-local-theory.tex:117-124`: two solutions with identical data
  have identical velocities throughout their common interval.

  Exact quantifier order: admissible `ν,a,f`, then `T₁,T₂`, the two solution
  objects, then `t ∈ Ico 0 (min T₁ T₂)`, then `x`.  Non-vacuity: the conclusion
  is equality of actual velocity vectors at every common spacetime point. -/
  velocity_unique : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
        (u₂ : ClassicalSolutionT ν a f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
          u₁.velocity (t, x) = u₂.velocity (t, x)

  /-- `02-preliminaries.tex:28,84-88,105-109`: the zero-mean gauge turns
  pressure uniqueness modulo time into literal equality.

  Exact quantifier order is the same as `velocity_unique`, followed by the
  common time and spatial point.  Non-vacuity: this equates the two concrete
  normalized scalar pressure representatives, not merely their gradients. -/
  pressure_unique : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
        (u₂ : ClassicalSolutionT ν a f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
          u₁.pressure (t, x) = u₂.pressure (t, x)

  /-- `02-preliminaries.tex:32-34,105-109`: the selected local interval lies
  below the supremal classical lifespan.

  Exact quantifier order is admissible `ν,a,f`.  Non-vacuity: this is an order
  relation between the selected real horizon (embedded in `ℝ≥0∞`) and T10's
  concrete supremum over solution horizons. -/
  horizon_le_lifespan : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f

  /-- `02-preliminaries.tex:32-34,105-109` and
  `appendix-a-local-theory.tex:123-125`: patching local solutions produces a
  maximal smooth velocity with the normalized pressure.

  Exact quantifier order is `ν>0`, `a∈initialClassT`, `f∈forceClassT`, then
  existential `u,p`.  Non-vacuity: the witnesses are actual spacetime fields
  satisfying `ClassicalSolutionT` plus `PeriodicLocalRegularity` at every
  preterminal real horizon. -/
  exists_maximal : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
        IsMaximalPeriodicSolution ν a f u p

  /-- `02-preliminaries.tex:105-109` (the word “unique”) and
  `appendix-a-local-theory.tex:117-125`: any two maximal pairs coincide before
  every real horizon below the lifespan.

  Exact quantifier order is admissible `ν,a,f`, two velocity/pressure pairs,
  their maximality hypotheses, then `S`, `t`, and `x`.  Non-vacuity: both
  velocity and the zero-mean scalar pressure are equated pointwise. -/
  maximal_unique : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
        IsMaximalPeriodicSolution ν a f u₁ p₁ →
        IsMaximalPeriodicSolution ν a f u₂ p₂ →
          ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanT ν a f →
            (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
              u₁ (t, x) = u₂ (t, x)) ∧
            (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
              p₁ (t, x) = p₂ (t, x))

/-! ## Continuation -/

-- needs registration: torus version of A04 `timeShift`.
/-- `appendix-a-local-theory.tex:149-153`: positive-time translation of the
fixed force for a restart at `t₀`. -/
def timeShiftT (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1 + t₀, z.2)

-- needs registration: torus version of A04 `squaredHTwoIntegral`.
/-- `02-preliminaries.tex:110-114` eq:criterion: the squared periodic `H²`
continuation integral.  It is an `ℝ≥0∞` lintegral, rather than a real Bochner
integral, so divergence is represented by `⊤` and cannot be totalized to zero. -/
def squaredHTwoIntegralT (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    periodicSobolevENorm 2 (fun x ↦ u (t, x)) ^ (2 : ℕ)

-- needs registration: concrete extension relation for a normalized solution.
/-- `02-preliminaries.tex:110-114` and
`appendix-a-local-theory.tex:149-155`: a solution on `[0,S)` extends beyond
`S` when a strictly longer normalized classical solution agrees with both its
velocity and pressure on the whole old interval. -/
def ExtendsBeyondT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (w : ClassicalSolutionT ν a f S) : Prop :=
  RegularThroughT ν a f S ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT ν a f (S + δ),
      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        v.velocity (t, x) = w.velocity (t, x)) ∧
      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
        v.pressure (t, x) = w.pressure (t, x))

-- needs registration: the fixed-force H1 restart statement used in Appendix A.
/-- `appendix-a-local-theory.tex:147-152`: for one fixed periodic force and a
compact restart-time window, one positive duration works for every restart
time and every admissible datum in a finite `H¹` ball.  The shifted force need
not lie in `forceClassT` because a positive-time shift need not vanish near its
new time zero; the output solution class itself accepts the smooth shifted
force, exactly as the classical forced local theorem does. -/
def PeriodicRestartH1 : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
    ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassT →
          periodicSobolevENorm 1 a' ≤ K →
            ∃ v : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
              PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ v

/-- The periodic continuation interface.  It contains precisely the restart,
higher-order bound, endpoint restart, and criterion proved in Appendix A; it
does not add Section 4's later maximal-lifespan packaging
`lifespanInfiniteOfLocallyFinite`. -/
structure PeriodicContinuationAPI : Prop where
  /-- `appendix-a-local-theory.tex:147-152`: the H¹/fixed-force common restart
  duration used as `t₀ ↑ S`.

  Exact quantifier order is expanded in `PeriodicRestartH1`: `ν>0`, fixed
  `f∈forceClassT`, `S≥0`, finite `K`, then `∃δ>0`, then restart time and datum.
  Non-vacuity: the conclusion supplies a full smooth periodic solution on the
  genuine positive horizon `δ`, with its all-order regularity record. -/
  restart : PeriodicRestartH1

  /-- `appendix-a-local-theory.tex:129-147`: finiteness of the squared `H²`
  integral gives a uniform bound for every integer Sobolev order up to `S`.

  Exact quantifier order: admissible `ν,a,f`, a real `S>0`, a solution on
  `[0,S)`, finiteness of the criterion, then `∀ m, ∃ M`.  Non-vacuity: `M` is
  a finite `ℝ≥0∞` and bounds the concrete T10 `H^m` extended norm at every
  time in `Ico 0 S`. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (w : ClassicalSolutionT ν a f S),
        squaredHTwoIntegralT S w.velocity ≠ ⊤ →
          ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
            ∀ t ∈ Ico (0 : ℝ) S,
              periodicSobolevENorm (m : ℝ)
                (fun x ↦ w.velocity (t, x)) ≤ M

  /-- `appendix-a-local-theory.tex:147-153`: a uniform `H¹` bound on the old
  solution lets one restart close enough to `S`, producing a strictly longer
  solution identified with the old one by uniqueness.

  Exact quantifier order: admissible `ν,a,f`, `S>0`, a solution, finite `K`,
  then its pointwise `H¹` bound.  Non-vacuity: the conclusion is
  `ExtendsBeyondT`, which contains an explicit `δ>0`, larger
  `ClassicalSolutionT`, and pointwise agreement of velocity and normalized
  pressure on `[0,S)`. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (w : ClassicalSolutionT ν a f S),
        ∀ K : ℝ≥0∞, K ≠ ⊤ →
          (∀ t ∈ Ico (0 : ℝ) S,
            periodicSobolevENorm 1 (fun x ↦ w.velocity (t, x)) ≤ K) →
              ExtendsBeyondT ν a f S w

  /-- `02-preliminaries.tex:110-114` eq:criterion and
  `appendix-a-local-theory.tex:127-156`: the exact continuation criterion on
  `T³`.  Here `S : ℝ`, so the paper's `S<∞` is enforced by the type; `0<S` is
  explicit.

  Exact quantifier order: `ν>0`, `a∈initialClassT`, `f∈forceClassT`, `S>0`, a
  solution on `[0,S)`, then finiteness of `∫⁻₀ˢ ‖u(t)‖²_{H²}`.  Non-vacuity:
  the conclusion is the concrete larger-horizon agreement relation, not only
  a lifespan inequality. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (w : ClassicalSolutionT ν a f S),
        squaredHTwoIntegralT S w.velocity ≠ ⊤ →
          ExtendsBeyondT ν a f S w

/-! ## Periodic mean reduction -/

-- needs registration: time-dependent velocity and force means.
/-- `appendix-a-local-theory.tex:89-99`: `m(t)=meanT (u(t,·))`. -/
def velocityMeanT (u : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ u (t, x))

/-- `appendix-a-local-theory.tex:92-99`: the normalized spatial mean of the
force at time `t`, which is `m'(t)` along a solution. -/
def forceMeanT (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ f (t, x))

-- needs registration: explicit mean trajectory in Appendix A.
/-- `appendix-a-local-theory.tex:89-94`: the known mean trajectory determined
by the initial datum and force. -/
def prescribedMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, forceMeanT f r

-- needs registration: Galilean displacement and transformed fields.
/-- `appendix-a-local-theory.tex:93-98`: `X(t)=∫₀ᵗm(r)dr`, using the actual
solution mean as requested by the Galilean formula. -/
def galileanShiftT (u : SpaceTimeField) (t : ℝ) : Space :=
  ∫ r in (0 : ℝ)..t, velocityMeanT u r

/-- `appendix-a-local-theory.tex:95-99`: the Galilean velocity
`v(t,x)=u(t,x+X(t))-m(t)`. -/
def galileanVelocityT (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ u (z.1, z.2 + galileanShiftT u z.1) - velocityMeanT u z.1

/-- `appendix-a-local-theory.tex:95-100`: the transformed force
`h(t,x)=f(t,x+X(t))-m'(t)`, with `m'=meanT f` made explicit by the API below. -/
def galileanForceT (u f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1, z.2 + galileanShiftT u z.1) - forceMeanT f z.1

/-- `appendix-a-local-theory.tex:100-105`: the pressure is transported by the
same spatial translation, with no additive correction. -/
def galileanPressureT (u : SpaceTimeField) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p (z.1, z.2 + galileanShiftT u z.1)

/-- `appendix-a-local-theory.tex:97-100`: the centered initial velocity. -/
def centeredInitialT (a : SpatialField) : SpatialField :=
  fun x ↦ a x - meanT a

/-- `appendix-a-local-theory.tex:89-107`: the exact torus mean reduction used
to remove Tao's mean-zero restriction.  The transformed solution is packaged
as a full `ClassicalSolutionT`, so its PDE, divergence, periodicity, pressure
normalization, and common Sobolev interval are all concrete. -/
structure PeriodicMeanReductionAPI : Prop where
  /-- `appendix-a-local-theory.tex:89-94`: the spatial mean of a solution is
  the initial mean plus the integrated force mean.

  Exact quantifier order: admissible `ν,a,f`, `T`, a solution `w`, then
  `t ∈ Ico 0 T`.  Non-vacuity: this equates two concrete vectors in `Space`,
  one obtained from the physical velocity and one by a Bochner time integral. -/
  mean_formula : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        ∀ t ∈ Ico (0 : ℝ) T,
          velocityMeanT w.velocity t = prescribedMeanT a f t

  /-- `appendix-a-local-theory.tex:92-99`: `m'(t)=meanT(f(t,·))` at interior
  times.

  Exact quantifier order: admissible `ν,a,f`, `T`, `w`, then
  `t ∈ Ioo 0 T`.  Non-vacuity: `HasDerivAt` asserts the actual derivative of
  the vector-valued mean path and identifies it with the concrete force mean. -/
  mean_derivative : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t

  /-- `appendix-a-local-theory.tex:95-106`: the displayed Galilean fields
  solve the mean-free forced equation on the same horizon, with translated
  pressure and the zero-mean gauge.

  Exact quantifier order: admissible `ν,a,f`, `T`, then `w`; the existential
  solution follows.  Non-vacuity: its velocity, pressure, and force are pinned
  by equalities to the displayed transforms and it carries the full local
  regularity record. -/
  transformed_solution : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        ∃ v : ClassicalSolutionT ν (centeredInitialT a)
            (galileanForceT w.velocity f) T,
          v.velocity = galileanVelocityT w.velocity ∧
          v.pressure = galileanPressureT w.velocity w.pressure ∧
          PeriodicLocalRegularity ν (centeredInitialT a)
            (galileanForceT w.velocity f) T v

  /-- `appendix-a-local-theory.tex:89-104`: the transformed datum and force
  remain in the stated smooth periodic classes.

  Exact quantifier order: admissible `ν,a,f`, `T`, then the solution `w`.
  Non-vacuity: this is membership of the explicit centered datum and explicit
  transformed force in T10's concrete sets. -/
  transformed_classes : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        centeredInitialT a ∈ initialClassT ∧
          galileanForceT w.velocity f ∈ forceClassT

  /-- `appendix-a-local-theory.tex:89-103`: the centered initial velocity,
  transformed velocity, and transformed force have zero spatial mean.

  Exact quantifier order: admissible `ν,a,f`, `T`, `w`, followed by
  `t ∈ Ico 0 T` for the two time-dependent fields.  Non-vacuity: each
  conclusion is the literal Haar-integral equation `meanT (...) = 0`. -/
  transformed_mean_zero : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        meanT (centeredInitialT a) = 0 ∧
          (∀ t ∈ Ico (0 : ℝ) T,
            meanT (fun x ↦ galileanVelocityT w.velocity (t, x)) = 0) ∧
          (∀ t ∈ Ico (0 : ℝ) T,
            meanT (fun x ↦ galileanForceT w.velocity f (t, x)) = 0)

  /-- `appendix-a-local-theory.tex:101-104`: spatial translations preserve
  every Sobolev norm.  The comparison is with the centered, untranslated
  slice because subtracting the zero mode itself changes the inhomogeneous
  norm.

  Exact quantifier order: admissible `ν,a,f`, `T`, `w`, arbitrary real order
  `s`, then `t ∈ Ico 0 T`.  Non-vacuity: this is equality of two concrete T10
  extended Sobolev norms for the displayed fields. -/
  translation_preserves_sobolev : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ (s : ℝ) (t : ℝ), t ∈ Ico (0 : ℝ) T →
            periodicSobolevENorm s
                (fun x ↦ galileanVelocityT w.velocity (t, x)) =
              periodicSobolevENorm s
                (fun x ↦ w.velocity (t, x) - velocityMeanT w.velocity t)

/-! ## Viscosity rescaling -/

-- needs registration: the Appendix A rescaling to viscosity one.
/-- `appendix-a-local-theory.tex:79-87`: rescaled initial velocity
`ã=ν⁻¹a`. -/
def unitViscosityInitialT (ν : ℝ) (a : SpatialField) : SpatialField :=
  fun x ↦ ν⁻¹ • a x

/-- `appendix-a-local-theory.tex:79-87`: `ũ(τ,x)=ν⁻¹u(τ/ν,x)`. -/
def unitViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν⁻¹ • u (z.1 / ν, z.2)

/-- `appendix-a-local-theory.tex:79-87`: `p̃(τ,x)=ν⁻²p(τ/ν,x)`. -/
def unitViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ (ν ^ 2)⁻¹ * p (z.1 / ν, z.2)

/-- `appendix-a-local-theory.tex:79-87`: `f̃(τ,x)=ν⁻²f(τ/ν,x)`. -/
def unitViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ (ν ^ 2)⁻¹ • f (z.1 / ν, z.2)

-- needs registration: inverse rescaling when undoing the viscosity-one result.
/-- `appendix-a-local-theory.tex:86-87`: inverse velocity rescaling
`u(t,x)=νũ(νt,x)`. -/
def restoreViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν • u (ν * z.1, z.2)

/-- `appendix-a-local-theory.tex:86-87`: inverse pressure rescaling. -/
def restoreViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ν ^ 2 * p (ν * z.1, z.2)

/-- `appendix-a-local-theory.tex:86-87`: inverse force rescaling. -/
def restoreViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν ^ 2 • f (ν * z.1, z.2)

/-- `appendix-a-local-theory.tex:79-87`: the viscosity-one reduction and its
inverse for periodic data, including preservation of the manuscript classes. -/
structure PeriodicViscosityRescalingAPI : Prop where
  /-- `appendix-a-local-theory.tex:79-87`: positive viscosity rescaling
  preserves the smooth periodic initial and force classes.

  Exact quantifier order: `ν>0`, `a∈initialClassT`, then
  `f∈forceClassT`.  Non-vacuity: the conclusion is membership of the explicit
  rescaled physical fields in T10's concrete input sets. -/
  scaled_classes : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      unitViscosityInitialT ν a ∈ initialClassT ∧
        unitViscosityForceT ν f ∈ forceClassT

  /-- `appendix-a-local-theory.tex:86-87`: applying the inverse formulas to
  the rescaled velocity, pressure, and force restores the original fields.

  Exact quantifier order: `ν>0`, followed by arbitrary concrete `u,p,f`.
  Non-vacuity: the conclusion consists of three equalities of full physical
  spacetime fields, including the force rescaling rather than only the PDE
  parameter. -/
  inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f

  /-- `appendix-a-local-theory.tex:79-87`: every viscosity-`ν` solution
  rescales to the displayed viscosity-one solution on horizon `νT`.

  Exact quantifier order: admissible `ν,a,f`, `T`, then the solution `w`.
  Non-vacuity: the existential is a full `ClassicalSolutionT` whose velocity
  and pressure are definitionally pinned to the displayed rescalings and whose
  all-order regularity is carried on the same rescaled interval. -/
  to_unit : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
        ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
            (unitViscosityForceT ν f) (ν * T),
          v.velocity = unitViscosityVelocityT ν w.velocity ∧
          v.pressure = unitViscosityPressureT ν w.pressure ∧
          PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
            (unitViscosityForceT ν f) (ν * T) v

  /-- `appendix-a-local-theory.tex:86-87`: undoing the unit-viscosity change
  restores the original viscosity, data, horizon, and normalized pressure.

  Exact quantifier order: admissible `ν,a,f`, `T`, then a unit-viscosity
  solution for the displayed rescaled data.  Non-vacuity: the conclusion is a
  full viscosity-`ν` solution whose fields equal the explicit inverse
  rescalings, together with the common-interval regularity record. -/
  from_unit : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField),
    a ∈ initialClassT → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ),
        ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
            (unitViscosityForceT ν f) (ν * T),
          ∃ w : ClassicalSolutionT ν a f T,
            w.velocity = restoreViscosityVelocityT ν v.velocity ∧
            w.pressure = restoreViscosityPressureT ν v.pressure ∧
            PeriodicLocalRegularity ν a f T w

end BlowupDensity.T11.DraftB
