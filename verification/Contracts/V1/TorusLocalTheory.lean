import Contracts.V1.TorusData

/-!
# Contract: the periodic local theory and continuation package on `T³`

This is the second Section 3 contract.  It registers

* the **solution-class tier** of the T10 data layer that `T01.torus_data`
  deliberately deferred (`Contracts/V1/TorusData.lean`, module docstring):
  Sobolev time paths, force norms, the smooth input classes, pressure
  normalization, `ClassicalSolutionT`, the maximal lifespan, breakdown sets,
  relative density and the two energy norms; and
* the **T11 vocabulary and four public APIs** reconciled in
  `research/T11/RECONCILIATION.md` and stated in `research/T11/Spec.lean`:
  `PeriodicLocalTheoryAPI` (8 fields), `PeriodicContinuationH3API` (5),
  `PeriodicMeanReductionAPI` (6) and `PeriodicViscosityRescalingAPI` (4).

## Registered narrowing of the continuation package

`research/T11/LEAD_AMENDMENTS.md` amendment 2 and `research/T11/H1_GAP.md`.

The manuscript's continuation package is `PeriodicContinuationAPI` below, stated
here verbatim.  Two of its five fields, `restart` and `restartBeyond`, quantify
over an **`H¹` ball** of data.  The implemented periodic local theory is a
Picard contraction in the two-space pair `H³ × H²`, whose horizon is governed by
the `H³` norm of the datum; an `H¹` bound gives no control of that norm, so the
horizon cannot be made uniform over an `H¹` ball by this route at any level of
bookkeeping.  Uniformity over an `H¹` ball is the subcritical Fujita–Kato local
theory, which is in none of the three code bases.

**What is registered is therefore `PeriodicContinuationH3API`: the manuscript
structure with those two `H¹` balls replaced by `H³` balls and nothing else
changed.**  The three ball-free fields (`higherOrderBound`, `extendsBeyond`,
`lifespanInfiniteOfLocallyFinite`) are the manuscript's verbatim.  The two
`H¹` sentences are kept as the named, documented, **unproved** predicates
`PeriodicRestartH1` and `PeriodicRestartBeyondH1`, and
`periodicContinuationAPI_of_h1` in `Section3/T11/Assembly.lean` shows that the
manuscript package follows from exactly those two and nothing else.  This is the
treatment Section 4 gave `ManuscriptHorizonLowerBoundH1` next to the
owner-approved `RestartFixedForce` narrowing
(`Contracts/V2/Continuation.lean:88,105`).  No V1 statement is silently
weakened: the `H¹` wording is preserved on this page.

Consumers were checked in `research/T11/H1_GAP.md` §3.  Every use inside T11
supplies an `H³` bound through `higherOrderBound`, which produces a finite bound
at **every** order.  T20 consumes the package through `extendsBeyond` and the
criterion, which carry no ball; if a consumer is later found to need the `H¹`
ball itself, that is an owner-level gap to report, never a silent weakening.

## Restatement policy

`Contracts/*` may not import the implementation, so every declaration below is
restated here token-for-token from `research/T11/Spec.lean` (T11 vocabulary and
APIs) or from `research/T10/Spec.lean` (the deferred solution-class tier), and
`Bindings.TorusLocalTheory` checks each restated `def` against the canonical
module `NSFormalization.Section3.T{10,11}` by `rfl`.

`ClassicalSolutionT` is the contract structure exception (`CLAUDE.md`): a
`structure` restated here is a *different inductive type* from the canonical
one, so no `rfl` bridge is possible.  The binding instead supplies the fieldwise
conversions `toContract` / `ofContract` — every field type is definitionally
equal — together with both round trips, and transports the four API terms across
them.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.TorusLocalTheory

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

/-! ## 1. Time paths, force norms, and the smooth input classes

Deferred by `T01.torus_data`; restated from `research/T10/Spec.lean:257-285`. -/

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

/-! ## 2. Pressure normalization and classical solutions

Restated from `research/T10/Spec.lean:290-373`. -/

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
Sobolev regularity without postulating an endpoint value at `T`.

**Structure exception** (`CLAUDE.md`): this is a different inductive type from
the canonical `NSFormalization.Section3.T10.ClassicalSolutionT`, whose fields
are definitionally equal one by one.  `Bindings.TorusLocalTheory` supplies the
fieldwise conversions and both round trips instead of an impossible `rfl`
bridge. -/
structure ClassicalSolutionT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) where
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
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x
      = f (t, x)
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
    MemLp (torusLift (fun x ↦ pressureGradient pressure t x)) 2
      periodicTorusMeasure
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
def RegularThroughT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) :
    Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionT ν a f (T + δ))

/-! ## 3. Breakdown, relative density, and the energy metric

Restated from `research/T10/Spec.lean:376-430`. -/

/-- `02-preliminaries.tex:38-48` eq:singularforces, relative to an arbitrary
ambient periodic force class `Y`. -/
def breakdownSetInT (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField)
    (T : ℝ) : Set SpaceTimeField :=
  {f | f ∈ Y ∧ maximalLifespanT ν a f ≤ ENNReal.ofReal T}

/-- `02-preliminaries.tex:38-48` eq:singularforces:
`B_{ν,a,T}={f∈F_T:T_max^ν(a,f)≤T}`. -/
def breakdownSetT (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  breakdownSetInT forceClassT ν a T

/-- `01-introduction.tex:118-140` and `03-torus.tex:7`: relative density in the
periodic `L^q(0,∞;H^s)` pseudometric. -/
def RelativelyDenseT (q : ℝ≥0∞) (s : ℝ)
    (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r →
    ∃ f ∈ S, forceSobolevENormT q s (f - g) < r

/-- `01-introduction.tex:143-145` eq:Enorm, first summand: the periodic
`L∞(0,T;L²(T³))` extended norm. -/
def energyEssSupT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup
    (fun t ↦ eLpNorm (torusLift (fun x ↦ z (t, x))) 2 periodicTorusMeasure)
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:145` eq:Enorm, second summand: the periodic
`L²(0,T;L²(T³))` norm of the full spatial gradient. -/
def energyGradientT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x ↦ spatialGradient z t x)) 2
        periodicTorusMeasure) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143` eq:Enorm: the physical periodic energy norm. -/
def energyENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  energyEssSupT T z + energyGradientT T z

/-- `01-introduction.tex:143-145` and `03-torus.tex:2-4`: coefficient-side
`L∞(0,T;L²(T³))`. -/
def coefficientEnergyEssSupT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t ↦ periodicSobolevENorm 0 (fun x ↦ z (t, x)))
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:105-109,145`: coefficient-side `L²(0,T;Ḣ¹(T³))`. -/
def coefficientEnergyGradientT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (periodicHomogeneousENorm 1 (meanZeroPartT (fun x ↦ z (t, x)))) ^
        (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143-145`: the complete coefficient-side `E_T`
quantity. -/
def coefficientEnergyENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  coefficientEnergyEssSupT T z + coefficientEnergyGradientT T z

/-! ## 4. T11 vocabulary

Restated from `research/T11/Spec.lean:441-510` and `:768-930`. -/

/-- appendix-a-local-theory.tex:71-76: an order-`s` Fourier datum path for a
physical field on a specified time set. -/
def IsPeriodicSobolevPathOn (s : ℝ) (I : Set ℝ) (u : SpaceTimeField)
    (G : ℝ → PeriodicSobolev s) : Prop :=
  ∀ t ∈ I, IsPeriodicDatum s (fun x ↦ u (t, x)) (G t)

/-- `02-preliminaries.tex:81-82` and appendix-a-local-theory.tex:76-77:
the tensor divergence `∇·(u⊗u)`, token-for-token the registered Section 4
spelling `Contracts/V2/LocalTheory.lean:58` except for its periodic suffix. -/
def convectionDivergenceT (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space ↦ (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- `02-preliminaries.tex:84-88`: the scalar spatial Laplacian of a periodic
pressure field. -/
def scalarSpatialLaplacianT (p : SpaceTimeScalar) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ
      (fun y : Space ↦
        fderiv ℝ (fun z : Space ↦ p (t, z)) y (coordinateVector i))
      x (coordinateVector i)

/-- appendix-a-local-theory.tex:117-125: one velocity-pressure pair solves on
every strictly shorter positive horizon.  This mirrors
`Contracts/V2/Continuation.lean:60` token-for-token at the predicate level. -/
def SolvesBelowT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionT ν a f b, w.velocity = u ∧ w.pressure = p

/-- `02-preliminaries.tex:32-36,105-115` and
appendix-a-local-theory.tex:117-125: a common pair realizes every positive
real horizon strictly below the extended maximal lifespan. -/
def IsMaximalPeriodicSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanT ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanT ν a f →
      ∃ w : ClassicalSolutionT ν a f S, w.velocity = u ∧ w.pressure = p

/-- `02-preliminaries.tex:110-114`: the squared periodic `H²` continuation
lintegral.  Divergence is represented by `⊤`, never by a junk real zero. -/
def squaredHTwoIntegralT (S : ℝ) (u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    periodicSobolevENorm 2 (fun x ↦ u (t, x)) ^ 2

/-- appendix-a-local-theory.tex:149-153: positive-time translation of the
fixed force, token-for-token with `Contracts/V2/Continuation.lean:50`. -/
def timeShiftT (t₀ : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1 + t₀, z.2)

/-- `02-preliminaries.tex:110-114` and appendix-a-local-theory.tex:149-155:
concrete strict extension of common fields solving below `S`. -/
def ExtendsBeyondT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ v : ClassicalSolutionT ν a f (S + δ),
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.velocity (t, x) = u (t, x)) ∧
    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
      v.pressure (t, x) = p (t, x))

/-- appendix-a-local-theory.tex:89-93 and `03-torus.tex:395-403`:
the normalized spatial mean of a velocity slice. -/
def velocityMeanT (u : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ u (t, x))

/-- appendix-a-local-theory.tex:92-99 and `03-torus.tex:397-403`:
the normalized spatial mean of a force slice. -/
def forceMeanT (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ f (t, x))

/-- appendix-a-local-theory.tex:89-93: the known mean trajectory
`m(t)=meanT a+∫₀ᵗ meanT(f(r,·))dr`, defined from data rather than from
arbitrary off-lifespan values of a solution. -/
def galileanMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, forceMeanT f r

/-- appendix-a-local-theory.tex:92-98: the known displacement
`X(t)=∫₀ᵗ m(r)dr`, built from the data-defined Galilean mean. -/
def galileanShiftT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  ∫ r in (0 : ℝ)..t, galileanMeanT a f r

/-- appendix-a-local-theory.tex:95-99: the transformed velocity
`v(t,x)=u(t,x+X(t))-m(t)`, with `m` and `X` defined from `a` and `f`. -/
def galileanVelocityT (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ u (z.1, z.2 + galileanShiftT a f z.1) - galileanMeanT a f z.1

/-- appendix-a-local-theory.tex:95-100: the transformed force
`h(t,x)=f(t,x+X(t))-meanT(f(t,·))`. -/
def galileanForceT (a : SpatialField) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ f (z.1, z.2 + galileanShiftT a f z.1) - forceMeanT f z.1

/-- appendix-a-local-theory.tex:100-106: pressure transported by the same
data-defined spatial translation, with no additive correction. -/
def galileanPressureT (a : SpatialField) (f : SpaceTimeField)
    (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ p (z.1, z.2 + galileanShiftT a f z.1)

/-- appendix-a-local-theory.tex:79-87: the rescaled initial velocity
`ã=ν⁻¹a`. -/
def unitViscosityInitialT (ν : ℝ) (a : SpatialField) : SpatialField :=
  fun x ↦ ν⁻¹ • a x

/-- appendix-a-local-theory.tex:79-87: the rescaled velocity
`ũ(τ,x)=ν⁻¹u(τ/ν,x)`. -/
def unitViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν⁻¹ • u (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:79-87: the rescaled pressure
`p̃(τ,x)=ν⁻²p(τ/ν,x)`, using the reconciled `(ν^2)⁻¹` spelling. -/
def unitViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ (ν ^ 2)⁻¹ * p (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:79-87: the rescaled force
`f̃(τ,x)=ν⁻²f(τ/ν,x)`, using the reconciled `(ν^2)⁻¹` spelling. -/
def unitViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ (ν ^ 2)⁻¹ • f (z.1 / ν, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse velocity scaling
`u(t,x)=νũ(νt,x)`. -/
def restoreViscosityVelocityT (ν : ℝ) (u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν • u (ν * z.1, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse pressure scaling. -/
def restoreViscosityPressureT (ν : ℝ) (p : SpaceTimeScalar) : SpaceTimeScalar :=
  fun z ↦ ν ^ 2 * p (ν * z.1, z.2)

/-- appendix-a-local-theory.tex:86-87: inverse force scaling. -/
def restoreViscosityForceT (ν : ℝ) (f : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ ν ^ 2 • f (ν * z.1, z.2)

/-! ## 5. Local regularity -/

/-- `02-preliminaries.tex:75-88,116-118` and
appendix-a-local-theory.tex:65-77: the three nonredundant regularity clauses
on one periodic classical solution and one common horizon. -/
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (T : ℝ) (w : ClassicalSolutionT ν a f T) : Prop where
  /-- appendix-a-local-theory.tex:65-77 and `02-preliminaries.tex:116-118`:
  every integer Sobolev order has a smooth datum path on the same `Ico 0 T`.

  Exact quantifier order: `∀ m : ℕ, ∃ G`, realization, then `ContDiffOn`. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) w.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  /-- `02-preliminaries.tex:84-88`: the normalized periodic pressure solves the
  displayed Poisson equation.  Exact quantifier order:
  `∀ t ∈ Ico 0 T, ∀ x : Space`. -/
  pressure_poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence
          (fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2) t x
  /-- `02-preliminaries.tex:80-83` eq:projected and
  appendix-a-local-theory.tex:76-77: the projected equation with the pressure
  gradient restored.  Exact quantifier order: `∀ t ∈ Ioo 0 T, ∀ x : Space`. -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
      (f (t, x) - convectionDivergenceT w.velocity t x) -
        pressureGradient w.pressure t x

/-! ## 6. The registered APIs -/

/-- `02-preliminaries.tex:32-34,105-109,116-118` and
appendix-a-local-theory.tex:60-77,117-125: periodic local existence,
uniqueness, and maximal gluing.  `Type`-valued because it carries the selected
horizon as data.  No field is a placeholder proposition. -/
structure PeriodicLocalTheoryAPI : Type where
  /-- `02-preliminaries.tex:105-109` and appendix-a-local-theory.tex:60-70:
  the selected common local horizon.  Exact argument order: `ν`, `a`, `f`.

  Non-vacuity: this is real numerical data used by `solution`; positivity is
  certified by the returned `ClassicalSolutionT`. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- `02-preliminaries.tex:105-109`: local existence for exactly
  `∀ν, 0<ν → ∀a∈initialClassT, ∀f∈forceClassT`.

  Non-vacuity: the result is a full `ClassicalSolutionT` on the named horizon,
  not an unspecified proposition. -/
  solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (horizon ν a f)
  /-- `02-preliminaries.tex:116-118` and appendix-a-local-theory.tex:65-77:
  all three regularity clauses hold for the selected solution on that same
  horizon.

  Non-vacuity: the conclusion is the concrete three-field regularity record. -/
  regularity : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)
  /-- `02-preliminaries.tex:105-109` and appendix-a-local-theory.tex:117-124:
  velocity uniqueness on the common interval.

  Non-vacuity: actual physical velocity vectors are equal pointwise. -/
  velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x)
  /-- `02-preliminaries.tex:28,84-88,105-109`: the zero-mean gauge upgrades
  pressure uniqueness to literal equality.

  Non-vacuity: the two normalized scalar pressure representatives are equal,
  not merely their gradients. -/
  pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x)
  /-- `02-preliminaries.tex:32-34`: the selected local horizon lies below the
  concrete supremal lifespan. -/
  horizon_le_lifespan : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f
  /-- `02-preliminaries.tex:32-34,105-109` and
  appendix-a-local-theory.tex:123-125: local solutions glue to a maximal
  velocity and normalized pressure.

  Non-vacuity: the witnesses are actual fields with full classical
  restrictions at every presingular real horizon. -/
  exists_maximal : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p
  /-- `02-preliminaries.tex:105-109` and appendix-a-local-theory.tex:117-125:
  maximal pairs agree at every presingular time.

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

/-- `02-preliminaries.tex:105-114` and appendix-a-local-theory.tex:127-156:
the manuscript-strength periodic continuation package, retaining the `H¹`
restart ball.  **NOT registered; two of its five fields are open.**  It is
stated here so that the narrowing below can be read against it, and so that
`periodicContinuationAPI_of_h1` can name exactly what is missing. -/
structure PeriodicContinuationAPI : Prop where
  /-- appendix-a-local-theory.tex:146-151: for one fixed force and compact
  restart window, one positive duration works for every restart time and every
  admissible datum in a finite `H¹` ball.  **Open.** -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
  /-- appendix-a-local-theory.tex:127-147: a finite squared-`H²` integral and
  Grönwall bound every integer Sobolev order uniformly below `S`. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M
  /-- appendix-a-local-theory.tex:146-153: a uniform `H¹` trajectory bound
  supplies one fixed positive restart margin and an exactly patched solution.
  **Open.** -/
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
  /-- `02-preliminaries.tex:109-114` eq:criterion and
  appendix-a-local-theory.tex:127-156: finite squared-`H²` integral implies
  concrete extension beyond the real endpoint `S`. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p
  /-- `02-preliminaries.tex:109-114`, appendix-a-local-theory.tex:124-155 and
  `03-torus.tex:490-502`: local criterion finiteness at every finite endpoint
  at or below a maximal lifespan forces global lifespan.  The non-strict
  `ofReal S ≤ lifespan` is load-bearing. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-- **The registered narrowing of the continuation package.**  This is
`PeriodicContinuationAPI` with the `H¹` balls of `restart` and `restartBeyond`
replaced by `H³` balls; every other token, quantifier and hypothesis is
identical, and the other three fields are the manuscript's verbatim.

Exact difference from the manuscript/V1 package: the Sobolev order of the two
data balls, `3` instead of `1`.  Nothing else — not the force quantification,
not the uniformity over restart times `t₀ ∈ [0,S]`, not the `δ`-before-datum
order — is weakened.  See the module docstring and `research/T11/H1_GAP.md`. -/
structure PeriodicContinuationH3API : Prop where
  /-- appendix-a-local-theory.tex:146-151 with the datum ball at order three:
  `periodicSobolevENorm 3 a' ≤ K` in place of `periodicSobolevENorm 1 a' ≤ K`.

  Non-vacuity: the conclusion returns a full shifted-force solution and its
  all-order regularity on the same genuine positive interval. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
  /-- appendix-a-local-theory.tex:127-147, verbatim: this field carries no
  ball at all.

  Non-vacuity: `M` bounds the concrete extended norm of the actual velocity
  slice and is finite. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M
  /-- appendix-a-local-theory.tex:146-153 with the uniform trajectory bound at
  order three: `periodicSobolevENorm 3 (u (t, ·)) ≤ K`.

  Non-vacuity: the same `δ` works for every admissible initial datum and the
  returned solution agrees in velocity and normalized pressure on all
  `[0,S)`. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 3 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x))
  /-- `02-preliminaries.tex:109-114` eq:criterion, verbatim: no ball.

  Non-vacuity: `ExtendsBeyondT` contains `δ>0`, a full larger solution, and
  exact overlap equality of both velocity and normalized pressure. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p
  /-- `03-torus.tex:490-502`, verbatim: no ball.  The non-strict
  `ofReal S ≤ lifespan` is load-bearing. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-- **The manuscript's `H¹` restart sentence; NOT implied by this contract;
open.**  It is `PeriodicContinuationAPI.restart` verbatim, kept as a named
predicate exactly as `Contracts/V2/LocalTheory.lean:193`
`ManuscriptHorizonLowerBoundH1` keeps Section 4's.  Its only difference from the
registered `PeriodicContinuationH3API.restart` is the Sobolev order of the datum
ball, `1` instead of `3`; that downgrade is the subcritical Fujita–Kato local
theory (`research/T11/H1_GAP.md` §2).  This definition is documentation of an
outstanding proposition, not a proved field and not an axiom. -/
def PeriodicRestartH1 : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

/-- **The manuscript's `H¹` endpoint-restart sentence; NOT implied by this
contract; open.**  It is `PeriodicContinuationAPI.restartBeyond` verbatim.  Its
only difference from the registered `PeriodicContinuationH3API.restartBeyond` is
the Sobolev order of the uniform trajectory bound, `1` instead of `3`.  It is
named separately from `PeriodicRestartH1` so that a consumer can see precisely
which of the two manuscript sentences it needs (`research/T11/H1_GAP.md` §1,
gaps G2 and G3). -/
def PeriodicRestartBeyondH1 : Prop :=
  ∀ (ν : ℝ), 0 < ν →
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

/-- appendix-a-local-theory.tex:89-106 and `03-torus.tex:395-403`: the exact
periodic mean identities and Galilean reduction. -/
structure PeriodicMeanReductionAPI : Prop where
  /-- appendix-a-local-theory.tex:89-93: the solution mean equals the known
  initial-plus-force mean.

  Non-vacuity: this equates two concrete vectors, one obtained from the
  physical solution and one from an actual Bochner interval integral. -/
  mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t
  /-- appendix-a-local-theory.tex:92-98: `m'(t)=meanT (f(t,·))` at interior
  times.

  Non-vacuity: `HasDerivAt` asserts the genuine derivative of the actual
  solution-mean curve and identifies its concrete vector derivative. -/
  mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t
  /-- appendix-a-local-theory.tex:95-106: the displayed data-defined Galilean
  fields solve the mean-free equation on the same horizon and retain all stated
  regularity.

  Non-vacuity: the witness is a full `ClassicalSolutionT` whose velocity and
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
  data-defined transformed force stay in the manuscript input classes. -/
  transformed_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT
  /-- appendix-a-local-theory.tex:97-103: the centered datum, transformed
  velocity, and transformed force have zero normalized torus mean.

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

  Non-vacuity: this is equality of the concrete T10 extended norms, including
  `⊤` when no representing datum exists. -/
  translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z

/-- appendix-a-local-theory.tex:79-87: equivalence of positive viscosity and
unit viscosity, including class preservation and inverse formulas. -/
structure PeriodicViscosityRescalingAPI : Prop where
  /-- appendix-a-local-theory.tex:79-87: positive-viscosity rescaling
  preserves the stated smooth periodic initial and force classes. -/
  scaled_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT
  /-- appendix-a-local-theory.tex:86-87: inverse formulas restore velocity,
  pressure, and force.

  Non-vacuity: the conclusion contains three equalities of full physical
  fields, not merely equality of viscosity parameters. -/
  inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f
  /-- appendix-a-local-theory.tex:79-87: every viscosity-`ν` solution rescales
  to a viscosity-one solution on horizon `νT` with preserved regularity.

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
  restores `ν`, the original data, horizon `T`, and normalized pressure.

  Non-vacuity: the witness is a full viscosity-`ν` solution with exact inverse
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

/-! ## 7. The registered package -/

/-- The four registered periodic local-theory APIs in one object, the
declaration audited by `Tests.TorusLocalTheory`.  The continuation component is
the `H³` narrowing `PeriodicContinuationH3API`; the manuscript's two `H¹`
sentences are the unproved named predicates `PeriodicRestartH1` and
`PeriodicRestartBeyondH1` above, and are deliberately **not** fields here. -/
structure TorusLocalTheoryAPI : Type where
  /-- `02-preliminaries.tex:32-34,105-109,116-118`: the eight-field local
  theory. -/
  localTheory : PeriodicLocalTheoryAPI
  /-- appendix-a-local-theory.tex:127-156 with the registered `H³` narrowing of
  the two restart balls; see the module docstring. -/
  continuation : PeriodicContinuationH3API
  /-- appendix-a-local-theory.tex:89-106: the six-field Galilean mean
  reduction. -/
  meanReduction : PeriodicMeanReductionAPI
  /-- appendix-a-local-theory.tex:79-87: the four-field viscosity rescaling. -/
  viscosityRescaling : PeriodicViscosityRescalingAPI

end BlowupDensity.Contracts.V1.TorusLocalTheory
