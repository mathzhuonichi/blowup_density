import Contracts.V1.Data
import Contracts.V1.TorusData
import Contracts.V1.GradientL6
import Contracts.V1.CriticalRegularity
import Contracts.V1.EnergyAbsorptionPartial
import Contracts.V4.EnergyAbsorption
import Contracts.V2.Continuation

/-!
# T20 blind draft B: global regularity for a small critical periodic force

Statement-only specification of Proposition `prop:critical` and the displayed
estimates in `paper/sections/03-torus.tex:383-503`.  Physical fields remain
unit-periodic functions on `R^3`; Sobolev quantities use the registered
coefficient-side torus data.  The proof reduction here is deliberately the
untranslated one `v = u - m`, `h = g - gbar`, so the equation retains
`(m * nabla) v`.

T10 is registered and imported from `Contracts.V1.TorusData`.  The declarations
copied below are only the still-unregistered solution-class, T11, and T12
declarations used by this draft.  Marker comments give their exact sources.
-/

noncomputable section

/- copied verbatim from research/T10/Spec.lean:257-370 (selected declarations);
the already registered T10 data declarations are imported, not recopied. -/
namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

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

end BlowupDensity.T10.Draft
/- end verbatim T10 copy -/


/- copied verbatim from research/T11/Spec.lean:433-511,526-895
(selected declarations; literal check examples and viscosity rescaling are unused). -/
namespace BlowupDensity.T11.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
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


end BlowupDensity.T11.Draft
/- end verbatim T11 copy -/


/- copied verbatim from research/T12/Spec.lean:166-172,189-257,270-470
(selected declarations; registered definitional-check examples are unused). -/
namespace BlowupDensity.T12.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
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

/-! ## Reconciled Type-valued API -/

/-- The torus halves of Lemma A.1 and Lemma B.1, together with the mean-zero
order-two comparison used by Proposition 3.7.  Constants are data fields of
this Type-valued structure and therefore precede every field they control
(`appendix-b-embeddings.tex:109-110`). -/
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
  Non-vacuity: `C₀Half_pos` forces a positive datum. -/
  C₀Half : ℝ

  /-- `appendix-b-embeddings.tex:12-17,20-22`: positivity of the half-order
  critical constant; there are no later quantifiers.
  Non-vacuity: it constrains the actual constant used by
  `velocityCriticalL3`. -/
  C₀Half_pos : 0 < C₀Half

  /-- `appendix-b-embeddings.tex:26-31`: the one constant for the displayed
  sum of the gradient and Lambda `L³` norms, fixed before both fields.
  Non-vacuity: `C₀ThreeHalves_pos` forces a positive datum. -/
  C₀ThreeHalves : ℝ

  /-- `appendix-b-embeddings.tex:12-13,26-31`: positivity of the
  three-halves constant; there are no later quantifiers.
  Non-vacuity: it constrains the constant used in the combined display. -/
  C₀ThreeHalves_pos : 0 < C₀ThreeHalves

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
        ENNReal.ofReal C₀Half * periodicHomogeneousENorm (1 / 2) v

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
          ENNReal.ofReal C₀ThreeHalves *
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

end BlowupDensity.T12.Draft

/- end verbatim T12 copy -/

namespace BlowupDensity.T20.Spec

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T11.Draft
open BlowupDensity.T12.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## 1. The untranslated mean reduction -/

/-- `03-torus.tex:395-405`: for the zero initial datum, the data-defined mean
path `m(t) = ∫₀ᵗ meanT(g(s)) ds`.  This is T11's `galileanMeanT` without
performing the Galilean spatial translation. -/
def meanPathT (g : SpaceTimeField) (t : ℝ) : Space :=
  galileanMeanT (fun _ : Space ↦ 0) g t

/-- `03-torus.tex:395-401`: the untranslated mean-free velocity
`v(t,x) = u(t,x) - m(t)`. -/
def meanFreeVelocity (g u : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ u q - meanPathT g q.1

/-- `03-torus.tex:397-401`: the mean-free force
`h(t,x) = g(t,x) - meanT(g(t,·))`. -/
def meanFreeForce (g : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ g q - forceMeanT g q.1

/-- `03-torus.tex:408-411`: the constant transport `(m(t)·∇)v`, written
as the spatial Fréchet derivative of `v(t,·)` applied to `m(t)`. -/
def constantTransportT (m : ℝ → Space) (v : SpaceTimeField) : SpaceTimeField :=
  fun q ↦ spatialDerivative v q.1 q.2 (m q.1)

/-- `03-torus.tex:411`: the fixed-time operator `z ↦ (m·∇)z`, used
to state skew-adjointness and commutation with `Λ` without arbitrary values in
the time coordinate. -/
def constantTransportSpatialT (m : Space) (v : SpatialField) : SpatialField :=
  fun x ↦ spatialDerivative (fun q ↦ v q.2) 0 x m

/-- `03-torus.tex:404-405`: the extended-valued integral
`∫₀ᵗ |meanT(g(s))| ds`; unlike a totalized real integral, failure of
measurability or integrability cannot turn this quantity into a junk zero. -/
def meanForceIntegralT (g : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal ‖forceMeanT g s‖

/-! ## 2. Critical and continuation quantities -/

/-- `03-torus.tex:414-418`: `y(t)=‖v(t)‖_{Ḣ^(1/2)}` in the registered
mean-zero coefficient realization. -/
def criticalY (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `z(t)=‖v(t)‖_{Ḣ^(3/2)}` in the registered
mean-zero coefficient realization. -/
def criticalZ (v : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (3 / 2) (fun x ↦ v (t, x))

/-- `03-torus.tex:414-418`: `b(t)=‖h(t)‖_{Ḣ^(1/2)}`. -/
def criticalB (h : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ h (t, x))

/-- `03-torus.tex:441-444` (`eq:bintegral`): the proof's full-time
`B = ∫₀∞ b(t) dt`, kept in `ℝ≥0∞` so divergence is `⊤`. -/
def criticalBIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, criticalB h t ∂forceTimeMeasure

/-- `03-torus.tex:383-389`: the critical inhomogeneous force size
`ρ = ‖g‖_{L¹(0,∞;H^(1/2))}`. -/
def criticalRho (g : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENormT 1 (1 / 2) g

/-- `03-torus.tex:482-484`: `‖∇v‖²₂`, expressed through T12's
registered-spelling gradient tensor.  Its uses below explicitly assert that
the extended norm is finite before applying `toReal`. -/
def gradientSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (gradientTensor v)).toReal ^ 2

/-- `03-torus.tex:468-484`: `‖Δv‖²₂`, expressed through T12's
registered-spelling componentwise Laplacian. -/
def laplacianSqT (v : SpatialField) : ℝ :=
  (periodicLpENorm 2 (laplacian v)).toReal ^ 2

/-- `03-torus.tex:479-488`: `‖h‖²₂` on the normalized unit torus. -/
def lTwoSqT (h : SpatialField) : ℝ :=
  (periodicLpENorm 2 h).toReal ^ 2

/-- `03-torus.tex:488-500`: the full positive-time integral
`∫₀∞ ‖h(t)‖²₂ dt`, with divergence represented by `⊤`. -/
def meanFreeForceLTwoSqIntegral (h : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t, (periodicLpENorm 2 (fun x ↦ h (t, x))) ^ (2 : ℝ) ∂forceTimeMeasure

/-- `03-torus.tex:494-500`: the right-hand integrand in the orthogonal
constant/mean-zero `H²` decomposition of `u`. -/
def meanModeCriterionIntegral (S : ℝ) (g u : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) S,
    ENNReal.ofReal ‖meanPathT g t‖ ^ (2 : ℝ) +
      periodicSobolevENorm 2 (fun x ↦ meanFreeVelocity g u (t, x)) ^ (2 : ℝ)

/-- `03-torus.tex:411`: the real `L²(T³)` pairing used to state
skew-adjointness of constant transport.  Its API field below carries explicit
integrability hypotheses for both scalar integrands. -/
def periodicPairing (v w : SpatialField) : ℝ :=
  ∫ y : PeriodicTorus,
    (inner ℝ (torusLift v y) (torusLift w y) : ℝ) ∂periodicTorusMeasure

/-! ## 3. Proposition 3.7 and its displayed proof estimates -/

/-- Proposition `prop:critical` together with the named estimates in its
proof (`03-torus.tex:383-503`).  The interface is indexed by the binding T11
local/continuation/mean-reduction packages and the binding T12 calculus
package, making the DAG dependencies explicit without copying their facts as
new T20 fields.  It is **Type-valued** because the universal smallness radius
and the three absolute estimate constants are mathematical data selected
before every viscosity, force, and solution.  Their positivity and the two
bootstrap shrinkings prevent vacuous thresholds.

The estimates are stated for the untranslated field `v=u-m`; hence
`meanFreeEquation` retains `constantTransportT`.  Every occurrence of a
totalized norm is protected collectively by `reductionRegular`, while every
`toReal` use has an explicit `≠ ⊤` conclusion there. -/
structure CriticalRegularityTAPI : Type where
  /-- `03-torus.tex:383-387`: the universal smallness constant, selected
  before `ν` and `g`.
  Exact quantifier order: dependency packages first, then this constant,
  before every viscosity and force in the theorem fields.
  Non-vacuity: `hc` below forces a genuinely positive ball. -/
  c : ℝ

  /-- `03-torus.tex:383-387`: positivity of the universal smallness constant.
  Exact quantifier order: there are no later parameters.
  Non-vacuity: with `ν>0`, `ENNReal.ofReal (c*ν)` is positive. -/
  hc : 0 < c

  /-- `03-torus.tex:426-440`: the absolute constant in the critical
  trilinear estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₀_pos` excludes the zero-constant trap. -/
  C₀ : ℝ

  /-- `03-torus.tex:426-440`: positivity of `C₀`.
  Exact quantifier order: no later parameters.
  Non-vacuity: the bootstrap level `ν/(2*C₀)` is meaningful. -/
  C₀_pos : 0 < C₀

  /-- `03-torus.tex:467-484`: the absolute coefficient of `y‖Δv‖²₂`
  in the `H¹` convection estimate, fixed before all PDE data.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `C₁_pos` below rules out zero. -/
  C₁ : ℝ

  /-- `03-torus.tex:467-484`: positivity of the `H¹` convection constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the second bootstrap shrinking is therefore genuine. -/
  C₁_pos : 0 < C₁

  /-- `03-torus.tex:479-484`: the absolute constant after Young's inequality
  in `eq:H1energy`.
  Exact quantifier order: it is structure data before `ν,g,T,w,t`.
  Non-vacuity: `CH1_pos` below prevents a zero right-hand coefficient. -/
  CH1 : ℝ

  /-- `03-torus.tex:479-484`: positivity of the `H¹` energy constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: this constrains the actual constant used in `hOneEnergy`. -/
  CH1_pos : 0 < CH1

  /-- `03-torus.tex:492-500`: the absolute constant in the assembled
  squared-`H²` continuation bound.
  Exact quantifier order: it is structure data before `ν,g,T,w,S`.
  Non-vacuity: `hCcriterion` below forces it to be positive. -/
  Ccriterion : ℝ

  /-- `03-torus.tex:492-500`: positivity of the continuation constant.
  Exact quantifier order: no later parameters.
  Non-vacuity: the finite bound in `continuationBound` is quantitative. -/
  hCcriterion : 0 < Ccriterion

  /-- `03-torus.tex:457`: the first required shrinking
  `c < 1/(4 C₀)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: together with positivity it gives a nonempty, absorbing
  bootstrap regime. -/
  c_lt_C₀ : c < 1 / (4 * C₀)

  /-- `03-torus.tex:477-480`: the second required shrinking
  `c < 1/(4 C₁)`.
  Exact quantifier order: constants were selected first.
  Non-vacuity: this is the stated absorption gate for `eq:H1energy`. -/
  c_lt_C₁ : c < 1 / (4 * C₁)

  reductionRegular : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ico (0 : ℝ) T,
          let v := fun x ↦ meanFreeVelocity g w.velocity (t, x)
          let h := fun x ↦ meanFreeForce g (t, x)
          IsMeanZeroT v ∧ SmoothPeriodicT v ∧
            MemPeriodicHomogeneous (1 / 2) v ∧
            MemPeriodicHomogeneous (3 / 2) v ∧
            MemPeriodicHmVector 2 v ∧
            IsMeanZeroT h ∧ SmoothPeriodicT h ∧
            MemPeriodicHomogeneous (1 / 2) h ∧
            periodicLpENorm 2 h ≠ ⊤ ∧
            periodicLpENorm 2 (gradientTensor v) ≠ ⊤ ∧
            periodicLpENorm 2 (laplacian v) ≠ ⊤

  meanBound : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g

  /-- `03-torus.tex:407-410`, `eq:meanfree`: the untranslated mean-free field
  solves
  `∂ₜv+(v·∇)v+(m·∇)v-νΔv+∇p=h`.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht,x`.
  Non-vacuity: this is a pointwise vector equation for the explicit `v`, `m`,
  `h`, and the normalized pressure of a full classical solution. -/
  meanFreeEquation : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
          temporalDerivative (meanFreeVelocity g w.velocity) t x +
              advection (meanFreeVelocity g w.velocity) t x +
              constantTransportT (meanPathT g)
                (meanFreeVelocity g w.velocity) (t, x) -
              ν • spatialLaplacian (meanFreeVelocity g w.velocity) t x +
              pressureGradient w.pressure t x =
            meanFreeForce g (t, x)

  /-- `03-torus.tex:411`: for fixed `m`, `(m·∇)` is skew-adjoint in
  periodic `L²`.
  Exact quantifier order: `m,v,w`, smooth-periodic hypotheses, followed by
  integrability of the two concrete pairing integrands.
  Non-vacuity: the conclusion is an equality of actual torus integrals; the
  integrability premises rule out Bochner-integral junk zeros. -/
  constantTransportSkew : ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v → SmoothPeriodicT w →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m v) y)
            (torusLift w y) : ℝ)) periodicTorusMeasure →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift v y)
            (torusLift (constantTransportSpatialT m w) y) : ℝ))
        periodicTorusMeasure →
        periodicPairing (constantTransportSpatialT m v) w =
          -periodicPairing v (constantTransportSpatialT m w)

  /-- `03-torus.tex:411`: constant transport commutes with the Fourier
  multiplier `Λ`.
  Exact quantifier order: `m,v,Lv`, smooth periodicity, then the T12 Lambda
  graph.
  Non-vacuity: the conclusion is the same concrete coefficientwise Lambda
  graph for the two transported physical fields. -/
  constantTransportCommutesLambda :
    ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
      IsPeriodicLambda v Lv →
        IsPeriodicLambda (constantTransportSpatialT m v)
          (constantTransportSpatialT m Lv)

  /-- `03-torus.tex:420-440`, `eq:criticalenergy`:
  `½(y²)' + (ν-C₀y)z² ≤ by` at every interior time.
  Exact quantifier order: `ν,hν,g,hg,T,w,t,ht`, followed by an actual
  derivative witness.
  Non-vacuity: existence of `E'` prevents an implication from a nonexistent
  derivative; `reductionRegular` makes every `toReal` operand finite. -/
  criticalEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
        ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ E' : ℝ,
            HasDerivAt
                (fun s ↦ (criticalY (meanFreeVelocity g w.velocity) s).toReal ^ 2)
                E' t ∧
              E' / 2 +
                  (ν - C₀ *
                    (criticalY (meanFreeVelocity g w.velocity) t).toReal) *
                    (criticalZ (meanFreeVelocity g w.velocity) t).toReal ^ 2 ≤
                (criticalB (meanFreeForce g) t).toReal *
                  (criticalY (meanFreeVelocity g w.velocity) t).toReal

  /-- `03-torus.tex:441-444`, `eq:bintegral`:
  `∫₀∞ b(t)dt ≤ ρ`.
  Exact quantifier order: `g,hg`; no viscosity or solution is needed.
  Non-vacuity: both sides are fail-safe `ℝ≥0∞` quantities based on
  integrable Fourier data paths, and `g∈forceClassT` is explicit. -/
  bIntegral : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalBIntegral (meanFreeForce g) ≤ criticalRho g

  /-- `03-torus.tex:446-458`, `eq:ybound`, after the continuity bootstrap:
  `y(t) ≤ ∫₀ᵗ b(s)ds ≤ ρ` throughout the classical lifespan.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`.
  Non-vacuity: the strict smallness hypothesis uses the positive finite
  threshold `cν`, and the conclusion bounds the concrete homogeneous norm. -/
  yBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g

  /-- `03-torus.tex:467-484`, `eq:H1energy`:
  `(‖∇v‖²₂)' + ν‖Δv‖²₂ ≤ Cν⁻¹‖h‖²₂`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,t,ht`, followed by an
  actual derivative witness.
  Non-vacuity: `reductionRegular` supplies finiteness for every norm passed
  to `toReal`, and existence of `E'` rules out a vacuous derivative premise. -/
  hOneEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x))

  /-- `03-torus.tex:486-500`: orthogonal mode decomposition and the finite
  squared-`H²` bound used in `eq:criterion`:
  `∫₀ˢ‖u‖²_{H²} ≤ Sρ² + Cν⁻²∫₀∞‖h‖²₂ < ∞`.
  Exact quantifier order: `ν,hν,g,hg,hsmall,T,w,S,hS,hST`.
  Non-vacuity: the final conjunct explicitly proves the displayed upper bound
  finite; neither compact support nor a failed datum can be a junk zero. -/
  continuationBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ (S : ℝ), 0 < S → S ≤ T →
            squaredHTwoIntegralT S w.velocity =
                meanModeCriterionIntegral S g w.velocity ∧
              meanModeCriterionIntegral S g w.velocity ≤
                ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ∧
              ENNReal.ofReal S * criticalRho g ^ (2 : ℝ) +
                  ENNReal.ofReal (Ccriterion * (ν⁻¹) ^ 2) *
                    meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤

  globalRegularity : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤

end BlowupDensity.T20.Spec

/-- Definitional spelling checks against registered Section 4 names. -/
example (z : BlowupDensity.Contracts.V1.Data.SpatialField) : BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.l2Sq z = BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.l2Sq z := rfl
example (z : BlowupDensity.Contracts.V1.Data.SpatialField) : BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.laplacianSq z = BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.laplacianSq z := rfl
