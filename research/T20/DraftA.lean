import Contracts.V1.Data
import Contracts.V1.TorusData
import Contracts.V1.CriticalRegularity
import Contracts.V4.EnergyAbsorption
import Contracts.V2.Continuation

/-!
# T20 blind draft A: global regularity for small critical force

Statement-only draft of Proposition `prop:critical` and the labelled estimates
in its proof (`paper/sections/03-torus.tex:383-503`).  The registered T01
coefficient and mean vocabulary is used directly.  Only the still-unregistered
T10 solution layer and the T11/T12 declarations used below are copied, with
their original names, namespaces, and source markers.

The T20 interface is `Type`-valued: its universal constants are mathematical
data selected before viscosity, force, solution, and time.  A `Prop`-valued
structure could not retain those real data fields without collapsing them by
proof irrelevance.  Every extended norm is protected either by the manuscript
input class, a concrete `MemPeriodicHomogeneous` assertion, or an inequality
that forces it to be finite.  The two differential displays use `.toReal` only
after their field has asserted the corresponding extended norms are not `⊤`.
-/

noncomputable section

/-! ## Still-unregistered T10 solution declarations -/

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

/- copied verbatim from research/T10/Spec.lean:257-370 (selected declarations);
the T01 data declarations used in their bodies are now imported from
Contracts.V1.TorusData and are not copied here. -/

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

end BlowupDensity.T10.Draft

/-! ## Still-unregistered T11 continuation/mean vocabulary -/

namespace BlowupDensity.T11.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators

/- copied verbatim from research/T11/Spec.lean:471-480 and :777-787
(selected declarations). -/

/-- appendix-a-local-theory.tex:117-125: one velocity-pressure pair solves on
every strictly shorter positive horizon. This mirrors
Contracts/V2/Continuation.lean:60 token-for-token at the predicate level. -/
-- copied from research/T11/Spec.lean:471
def SolvesBelowT (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (S : ℝ)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  ∀ b : ℝ, 0 < b → b < S →
    ∃ w : ClassicalSolutionT ν a f b, w.velocity = u ∧ w.pressure = p

/-- appendix-a-local-theory.tex:92-99 and 03-torus.tex:397-403:
the normalized spatial mean of a force slice. -/
-- copied from research/T11/Spec.lean:777
def forceMeanT (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT (fun x ↦ f (t, x))

/-- appendix-a-local-theory.tex:89-93: the known mean trajectory
m(t)=meanT a+∫₀ᵗ meanT(f(r,·))dr, defined from data rather than from arbitrary
off-lifespan values of a solution. -/
-- copied from research/T11/Spec.lean:783
def galileanMeanT (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Space :=
  meanT a + ∫ r in (0 : ℝ)..t, forceMeanT f r

end BlowupDensity.T11.Draft

/-! ## Still-unregistered T12 physical membership vocabulary -/

namespace BlowupDensity.T12.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

/- copied verbatim from research/T12/Spec.lean:217-255 (selected declarations);
all referenced T10 data names resolve to the registered T01 namespace. -/

/-- `appendix-a-local-theory.tex:8-12`: vector membership in periodic
`H^m`.  The conjunct order is periodicity, physical `L²`, then finiteness of
T10's total vector datum norm. -/
-- copied from research/T12/Spec.lean:217
def MemPeriodicHmVector (m : ℕ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    periodicSobolevENorm (m : ℝ) z ≠ ⊤

/-- `appendix-b-embeddings.tex:20-22,26-27`: a physical mean-zero periodic
representative with finite displayed homogeneous norm.  The exact conjunct
order is periodicity, physical `L²`, physical Haar mean zero, then finiteness. -/
-- copied from research/T12/Spec.lean:224
def MemPeriodicHomogeneous (s : ℝ) (z : SpatialField) : Prop :=
  IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure ∧
    IsMeanZeroT z ∧ periodicHomogeneousENorm s z ≠ ⊤

/-- `appendix-b-embeddings.tex:34-37`: the smooth periodic fields used by the
article's derivative displays.  Smoothness precedes physical periodicity. -/
-- copied from research/T12/Spec.lean:230
def SmoothPeriodicT (z : SpatialField) : Prop :=
  ContDiff ℝ ∞ z ∧ IsPeriodicSpatial z

/-- `01-introduction.tex:104`: the physical `L^p(T³)` extended norm of any
normed additive target, against normalized Haar measure. -/
-- copied from research/T12/Spec.lean:235
def periodicLpENorm {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (z : Space → E) : ℝ≥0∞ :=
  eLpNorm (torusLift z) p periodicTorusMeasure

/-- `appendix-b-embeddings.tex:34-37` and `03-torus.tex:467-477`: the
time-independent lift used to reuse the registered spatial operators.
Copied token-for-token from `Contracts/V1/GradientL6.lean:78`. -/
-- copied from research/T12/Spec.lean:244
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `appendix-b-embeddings.tex:30-32,97-100`: the physical Frobenius gradient
tensor.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:89-90`. -/
-- copied from research/T12/Spec.lean:249
def gradientTensor (v : SpatialField) : Space → WithLp 2 (Fin 3 → Space) :=
  fun x => spatialGradient (lift v) 0 x

/-- `appendix-b-embeddings.tex:32,97-100` and `03-torus.tex:467-477`: the
componentwise spatial Laplacian.  Copied token-for-token from
`Contracts/V1/GradientL6.lean:94-95`. -/
-- copied from research/T12/Spec.lean:255
def laplacian (v : SpatialField) : SpatialField :=
  fun x => spatialLaplacian (lift v) 0 x

end BlowupDensity.T12.Draft

namespace BlowupDensity.T20.DraftA

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T11.Draft
open BlowupDensity.T12.Draft
open scoped ContDiff ENNReal BigOperators

/-! ## Mean-free reduction and proof quantities -/

/-- `03-torus.tex:395-405`: the data-defined mean path for a solution from
rest, `m(t)=∫₀ᵗ meanT(g(s)) ds`.  Using T11's `galileanMeanT` prevents values
of a maximal solution after its lifespan from entering the definition. -/
def meanPathT (g : SpaceTimeField) (t : ℝ) : Space :=
  galileanMeanT (fun _ : Space => 0) g t

/-- `03-torus.tex:395-410`: the untranslated mean-free velocity
`v(t,x)=u(t,x)-m(t)`.  There is deliberately no Galilean spatial shift. -/
def meanFreeVelocity (g u : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ u z - meanPathT g z.1

/-- `03-torus.tex:395-410`: the centered force
`h(t,x)=g(t,x)-meanT(g(t,·))`. -/
def meanFreeForce (g : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ g z - forceMeanT g z.1

/-- `03-torus.tex:408-411`: the constant transport `(m(t)·∇)v`, written as
the spatial derivative of `v` applied to the constant vector `m(t)`. -/
def constantTransportTerm (g u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative (meanFreeVelocity g u) t x (meanPathT g t)

/-- `03-torus.tex:414-418`: `y(t)=‖v(t)‖_{Ḣ^{1/2}(T³)}`.  The extended norm is
fail-safe (`⊤` when no homogeneous datum exists). -/
def criticalY (g u : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ meanFreeVelocity g u (t, x))

/-- `03-torus.tex:414-418`: `z(t)=‖v(t)‖_{Ḣ^{3/2}(T³)}`. -/
def criticalZ (g u : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (3 / 2) (fun x ↦ meanFreeVelocity g u (t, x))

/-- `03-torus.tex:414-418`: `b(t)=‖h(t)‖_{Ḣ^{1/2}(T³)}`. -/
def criticalBRate (g : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  periodicHomogeneousENorm (1 / 2) (fun x ↦ meanFreeForce g (t, x))

/-- `03-torus.tex:442-444`, `eq:bintegral`: the full positive-time
`B=∫₀∞b(t)dt`, as a `lintegral` so divergence is `⊤`, never a junk real zero. -/
def criticalBIntegral (g : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), criticalBRate g t

/-- `03-torus.tex:454-456`, `eq:ybound`: the partial forcing primitive
`∫₀ᵗb(s)ds`, again retaining possible divergence as `⊤`. -/
def criticalBPartial (g : SpaceTimeField) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) t, criticalBRate g s

/-- `03-torus.tex:385-387`: the paper's `ρ=‖g‖_{L¹(0,∞;H^{1/2})}`. -/
def criticalForceRadius (g : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENormT 1 (1 / 2) g

/-- Physical squared `L²(T³)` quantity against normalized Haar measure.
It is used only under the explicit smoothness/`MemLp` conclusions in
`hOneEnergy` below (`03-torus.tex:467-488`). -/
def periodicLTwoSq {E : Type*} [NormedAddCommGroup E] (z : Space → E) : ℝ :=
  ∫ x : PeriodicTorus, ‖torusLift z x‖ ^ 2 ∂periodicTorusMeasure

/-- `03-torus.tex:482-484`: `‖∇v‖₂²` with the T12 Frobenius-gradient spelling. -/
def gradientLTwoSq (v : SpatialField) : ℝ :=
  periodicLTwoSq (gradientTensor v)

/-- `03-torus.tex:482-484`: `‖Δv‖₂²` with the T12 componentwise Laplacian. -/
def laplacianLTwoSq (v : SpatialField) : ℝ :=
  periodicLTwoSq (laplacian v)

/-! ## Proposition 3.7 and its labelled proof estimates -/

/-- **Proposition 3.7** (`prop:critical`) together with the labelled estimates
used in its proof, `paper/sections/03-torus.tex:383-503`.

This structure is `Type`-valued because `c`, `C₀`, `C₁`, and `CH1` are chosen
real data, universally before all viscosity/force/solution quantifiers.  The
strict bounds on `c` record the two explicit choices at lines 457 and 477.
The theorem fields use the literal rest datum; it is definitionally a member
of `initialClassT`, rather than adding a redundant premise to the proposition. -/
structure CriticalRegularityTAPI : Type where
  /-- `03-torus.tex:383-387`: the viscosity-independent smallness constant.
  Exact order: this datum is selected before every `ν` and `g`.
  Non-vacuity: `hc` makes the strict ball below nonempty. -/
  c : ℝ

  /-- `03-torus.tex:383-387`: positivity of the smallness constant.
  Exact order: no later quantifier occurs.
  Non-vacuity: it prevents `ENNReal.ofReal (c*ν)` from collapsing to zero. -/
  hc : 0 < c

  /-- `03-torus.tex:426-440`: the absolute critical trilinear constant `C₀`,
  assembled from T12's `velocityCriticalL3` and
  `gradientLambdaCriticalL3` constants before all PDE data.
  Non-vacuity: `hC₀` forces a genuine positive coefficient. -/
  C₀ : ℝ

  /-- `03-torus.tex:426-440`: positivity of `C₀`; no later quantifiers.
  Non-vacuity: rules out a zero trilinear constant datum. -/
  hC₀ : 0 < C₀

  /-- `03-torus.tex:469-477`: the absolute `H¹` convection constant `C₁`,
  assembled from T12's `velocityCriticalL3` and `gradientLSix` constants.
  Non-vacuity: `hC₁` forces a genuine positive coefficient. -/
  C₁ : ℝ

  /-- `03-torus.tex:469-477`: positivity of `C₁`; no later quantifiers.
  Non-vacuity: rules out a zero absorption coefficient. -/
  hC₁ : 0 < C₁

  /-- `03-torus.tex:479-484`: the absolute constant after Young's inequality
  in `eq:H1energy`, selected before viscosity and force.
  Non-vacuity: `hCH1` forces a positive right-hand coefficient. -/
  CH1 : ℝ

  /-- `03-torus.tex:479-484`: positivity of the `H¹` energy constant.
  Exact order: no later quantifiers.
  Non-vacuity: rules out a spurious zero forcing coefficient. -/
  hCH1 : 0 < CH1

  /-- `03-torus.tex:457`: the first explicit shrinking of the universal
  radius.  Exact order: both constants were selected first.
  Non-vacuity: with `hC₀`, this is a genuine positive bootstrap threshold. -/
  c_lt_C₀ : c < 1 / (4 * C₀)

  /-- `03-torus.tex:477`: the second explicit shrinking of the same `c`.
  Exact order: both constants were selected first.
  Non-vacuity: with `hC₁`, it gives the strict `H¹` absorption margin. -/
  c_lt_C₁ : c < 1 / (4 * C₁)

  /-- `03-torus.tex:404-406`, `eq:meanbound`:
  `|m(t)| ≤ ∫₀ᵗ|meanT(g(s))|ds ≤ ρ`.

  Exact quantifier order: admissible `ν,g`, one positive compact horizon, a
  pair solving below it, then `t∈[0,S)`.
  Non-vacuity: the rightmost bound uses the fail-safe T10 force norm of a
  force in `forceClassT`; the middle quantity is a nonnegative `lintegral`. -/
  meanBound :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν (fun _ : Space => 0) g S u p →
              ∀ t ∈ Ico (0 : ℝ) S,
                ENNReal.ofReal ‖meanPathT g t‖ ≤
                    ∫⁻ s in Ioc (0 : ℝ) t,
                      ENNReal.ofReal ‖forceMeanT g s‖ ∧
                  (∫⁻ s in Ioc (0 : ℝ) t,
                      ENNReal.ofReal ‖forceMeanT g s‖) ≤ criticalForceRadius g

  /-- `03-torus.tex:407-411`, `eq:meanfree`: the untranslated field
  `v=u-m` satisfies
  `∂ₜv+(v·∇)v+(m·∇)v-νΔv+∇p=h`.

  Exact quantifier order: admissible `ν,g`, compact horizon, common solution
  pair, interior `t`, then `x`.
  Non-vacuity: this is a pointwise vector equation for the explicit `v`, `h`,
  and constant-transport term, not an existential transformed solution. -/
  meanFreeEquation :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν (fun _ : Space => 0) g S u p →
              ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
                NavierStokesR3.ProblemStatement.navierStokesResidual ν
                    (meanFreeVelocity g u) p t x +
                    constantTransportTerm g u t x =
                  meanFreeForce g (t, x)

  /-- `03-torus.tex:438-440`, `eq:criticalenergy`:
  `½(y²)' + (ν-C₀y)z² ≤ by`.

  Exact quantifier order: admissible `ν,g`, compact horizon, common solution
  pair, then an interior time.  At that time the three physical homogeneous
  norms are first certified by `MemPeriodicHomogeneous`; only then is their
  finite real value used in the derivative display.
  Non-vacuity: the field produces an actual derivative `E'` and its
  `HasDerivAt` witness, so the inequality cannot be satisfied by choosing an
  arbitrary derivative or by totalizing `⊤` to zero. -/
  criticalEnergy :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν (fun _ : Space => 0) g S u p →
              ∀ t ∈ Ioo (0 : ℝ) S,
                MemPeriodicHomogeneous (1 / 2)
                    (fun x ↦ meanFreeVelocity g u (t, x)) ∧
                MemPeriodicHomogeneous (3 / 2)
                    (fun x ↦ meanFreeVelocity g u (t, x)) ∧
                MemPeriodicHomogeneous (1 / 2)
                    (fun x ↦ meanFreeForce g (t, x)) ∧
                ∃ E' : ℝ,
                  HasDerivAt
                    (fun s ↦ (criticalY g u s).toReal ^ 2) E' t ∧
                  E' / 2 +
                      (ν - C₀ * (criticalY g u t).toReal) *
                        (criticalZ g u t).toReal ^ 2 ≤
                    (criticalBRate g t).toReal *
                      (criticalY g u t).toReal

  /-- `03-torus.tex:441-444`, `eq:bintegral`:
  `∫₀∞‖g-meanT(g)‖_{Ḣ^{1/2}} ≤ ρ`.

  Exact quantifier order: the force is quantified first; no viscosity,
  solution, or smallness assumption is inserted.
  Non-vacuity: the left side is a `lintegral` of fail-safe homogeneous norms,
  so this inequality itself proves it is finite whenever the class norm is. -/
  bIntegral :
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalBIntegral g ≤ criticalForceRadius g

  /-- `03-torus.tex:454-458`, `eq:ybound`, after the continuity bootstrap:
  `y(t) ≤ ∫₀ᵗb(s)ds ≤ ρ` throughout the classical lifespan.

  Exact quantifier order: `ν,hν,g,hg`, the strict `cν` smallness, one compact
  horizon, a common solution pair, then `t∈[0,S)`.
  Non-vacuity: all three quantities are extended norms or `lintegral`s; an
  absent homogeneous datum gives `⊤` and therefore cannot satisfy the first
  inequality against the finite smallness radius. -/
  yBound :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        criticalForceRadius g < ENNReal.ofReal (c * ν) →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν (fun _ : Space => 0) g S u p →
                ∀ t ∈ Ico (0 : ℝ) S,
                  criticalY g u t ≤ criticalBPartial g t ∧
                    criticalBPartial g t ≤ criticalForceRadius g

  /-- `03-torus.tex:482-484`, `eq:H1energy`:
  `(‖∇v‖₂²)' + ν‖Δv‖₂² ≤ CH1 ν⁻¹‖h‖₂²` under the same small-force choice.

  Exact quantifier order: admissible `ν,g`, strict smallness, compact horizon,
  common solution pair, then an interior time.  Smoothness and the three
  physical `L²` memberships precede the derivative witness.
  Non-vacuity: the Haar integrals cannot be junk zeros under the stated
  `MemLp` facts, and the derivative is supplied with `HasDerivAt`. -/
  hOneEnergy :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        criticalForceRadius g < ENNReal.ofReal (c * ν) →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν (fun _ : Space => 0) g S u p →
                ∀ t ∈ Ioo (0 : ℝ) S,
                  SmoothPeriodicT (fun x ↦ meanFreeVelocity g u (t, x)) ∧
                  MemLp
                      (torusLift
                        (gradientTensor
                          (fun x ↦ meanFreeVelocity g u (t, x))))
                      2 periodicTorusMeasure ∧
                  MemLp
                      (torusLift
                        (laplacian
                          (fun x ↦ meanFreeVelocity g u (t, x))))
                      2 periodicTorusMeasure ∧
                  MemLp (torusLift (fun x ↦ meanFreeForce g (t, x)))
                      2 periodicTorusMeasure ∧
                  ∃ E' : ℝ,
                    HasDerivAt
                      (fun s ↦ gradientLTwoSq
                        (fun x ↦ meanFreeVelocity g u (s, x))) E' t ∧
                    E' + ν * laplacianLTwoSq
                        (fun x ↦ meanFreeVelocity g u (t, x)) ≤
                      CH1 * ν⁻¹ * periodicLTwoSq
                        (fun x ↦ meanFreeForce g (t, x))

  /-- **The main statement**, `03-torus.tex:383-390`, `eq:smallcritical`:
  for every `ν>0` and `g∈F_T`,
  `‖g‖_{L¹(0,∞;H^{1/2})}<cν` implies
  `T_max^ν(0,g)=∞`.

  Exact quantifier order: the structure's universal `c` is fixed first, then
  `ν,hν,g,hg`, then strict smallness.
  Non-vacuity: `g∈forceClassT` supplies the paper's smooth compact-time force;
  the fail-safe norm cannot pass smallness at `⊤`; the conclusion is literal
  equality with `⊤`, not regularity through an arbitrary finite horizon. -/
  globalRegularity :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        forceSobolevENormT 1 (1 / 2) g < ENNReal.ofReal (c * ν) →
          maximalLifespanT ν (fun _ : Space => 0) g = ⊤

end BlowupDensity.T20.DraftA
