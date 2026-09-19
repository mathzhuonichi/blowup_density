import NSFormalization.Section3.T23.Geometry
import NSFormalization.Section3.T23.LocalCorrectionBridge
import NSFormalization.Section3.T23.StatementRepair
import NSFormalization.Section3.T23.NoSlipUniqueness
import NSFormalization.Section3.T23.WholeSpaceCorrection
import NSFormalization.Section3.T22.Domain
import NSFormalization.Section4.A02.Patch

/-! Canonical T23 interface. Spec field order and formulas are preserved;
packet parameters are the six raw fields, and existing records are imported.
Both statements are definitions, not existence proofs. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter Topology
open NavierStokes NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (navierStokesResidual)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section4.D01 (sobolevENorm)
open NSFormalization.Section3.T22
open NSFormalization.Section3.T16 (correctedBackground)
open NSFormalization.Source.PacketScaling (SpeedUnboundedAt)
open scoped ContDiff ENNReal Topology BigOperators
/-- `02-preliminaries.tex:32-36,105-115` and `03-torus.tex:664-666`: the maximal
bounded-domain classical lifespan, as the supremum of horizons carrying a
`ClassicalSolutionOmega`.  Global lifespan is `⊤`; the empty supremum is `0`.
Mirrors the registered `maximalLifespanT`. -/
def domainMaximalLifespan (ν : ℝ) (Ω : Set Space) (a : SpatialField)
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionOmega ν Ω a f S), ENNReal.ofReal S

/-- `02-preliminaries.tex:32-36,105-115` and `03-torus.tex:664-666`: a
bounded-domain pair `(u,p)` realizes every positive real horizon strictly below
its extended maximal lifespan.  This is the **record form** of the maximal
predicate (concept from Draft A's `IsMaximalBoundedSolution`, but spelled with
`∃ w : ClassicalSolutionOmega`, mirroring the registered
`TorusLocalTheory.IsMaximalPeriodicSolution` token-for-token with the torus
objects replaced by their domain analogues), per `RECONCILIATION.md` §3 "Take
from A" 2.  Mirrors `IsMaximalPeriodicSolution ν a f u p := 0 < maximalLifespanT
∧ ∀ S, 0 < S → ofReal S < maximalLifespanT → ∃ w : ClassicalSolutionT …`.

Non-vacuity: a positive-lifespan conjunct together with a genuine per-horizon
existence of a `ClassicalSolutionOmega` witness whose velocity and pressure are
`u` and `p`, not merely a nonemptiness. -/
def IsMaximalDomainSolution (ν : ℝ) (Ω : Set Space) (a : SpatialField)
    (g : SpaceTimeField) (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < domainMaximalLifespan ν Ω a g ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < domainMaximalLifespan ν Ω a g →
      ∃ w : ClassicalSolutionOmega ν Ω a g S, w.velocity = u ∧ w.pressure = p

/-! ## 2. Bounded-domain energy and force norms (composed from T22 + registered)

`03-torus.tex:625-628,647-649`: the energy uses `L²(Ω)` and the force uses
`L¹(0,∞;H^s(Ω))` with the restriction norm `eq:restriction-norm`. -/

/-- `01-introduction.tex:143-145` and `03-torus.tex:647`: `L∞(0,T;L²(Ω))`
essential supremum of a spacetime field's slices.  `L²(Ω)` is the order-zero
restriction norm (`BoundedDomainNormAPI.orderZero`), written here as the
concrete restricted-measure `eLpNorm`. -/
def domainEnergyEssSup (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  essSup (fun t ↦ eLpNorm (fun x ↦ z (t, x)) 2 (volume.restrict Ω))
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:145` and `03-torus.tex:647`: `L²(0,T;L²(Ω))` norm of
the full spatial gradient. -/
def domainEnergyGradient (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (fun x ↦ spatialGradient z t x) 2 (volume.restrict Ω)) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143` and `03-torus.tex:647`, `eq:Enorm` on `Ω`: the
bounded-domain energy norm `E_T(Ω)`. -/
def domainEnergyENorm (Ω : Set Space) (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  domainEnergyEssSup Ω T z + domainEnergyGradient Ω T z

/-- `03-torus.tex:647-649`, `eq:restriction-norm`: the `L¹(0,∞;H^s(Ω))` force
norm, the time integral of the order-`s` restriction quotient norm
(`domainSobolevENorm`) of each slice, restricted through `restrictField`.

Non-vacuity: `domainSobolevENorm` is the empty-`⨅ = ⊤` fail-safe infimum, so a
finite value of this integral certifies an honest `H^s(Ω)` representative at a.e.
time. -/
def domainForceSobolevENorm (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), domainSobolevENorm Ω s (restrictField Ω (fun x ↦ f (t, x)))

/-- `03-torus.tex:649-663`: the whole-space `L¹(0,∞;H^s(R³))` norm of the
literal zero extension `E_0 f`, the time integral of the registered
`sobolevENorm` of `zeroExtension Ω (f(t,·))`.  This is the norm the Euclidean
scaling proof directly bounds (`:658-663`). -/
def zeroExtForceSobolevENorm (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), sobolevENorm s (zeroExtension Ω (fun x ↦ f (t, x)))

/-- `03-torus.tex:644`: the normalized spatial mean of a pressure slice over
`Ω` (the average `(∫_Ω p(t))/|Ω|`). -/
def domainPressureMean (Ω : Set Space) (p : SpaceTimeScalar) (t : ℝ) : ℝ :=
  (∫ x in Ω, p (t, x)) / (volume Ω).toReal

/-- `03-torus.tex:644`: subtract the `Ω`-average from each pressure slice, so the
result has zero spatial mean over `Ω`. -/
def domainNormalizePressure (Ω : Set Space) (p : SpaceTimeScalar) :
    SpaceTimeScalar :=
  fun z => p z - domainPressureMean Ω p z.1

/-! ## 3. The corollary `cor:boundary`

`paper/sections/03-torus.tex:632-666`, statement `:632-651` and proof `:652-666`,
for one `ε`-family. -/

/-- **Corollary `cor:boundary` (interior no-slip insertion),
`paper/sections/03-torus.tex:632-651`, proof `:652-666`.**

Parameters (the given objects, none an inhabited registered contract): the
viscosity `ν`; the fixed energy-enhanced whole-space packet `P`; the placement
`place` of the localized insertion (`prop:scaling`/`lem:localization`); the
bounded domain `Ω`; the reconciled bounded-domain norm layer `norms`
(`BoundedDomainNormAPI`, T22 — the `eq:zero-extension` input consumed by the
comparison field); the initial velocity `a` and reference force `g`; the ball
radius `r` and regularity margin `δ`; the cutoff data `D` of `lem:potential`
(carrying `w_ε = D.correction ε`); and the bounded-domain no-slip reference
`reference` regular through `place.T + δ`.

TORUS differences from T18's `PeriodicInsertionAPI` (see module header): (1) no
periodization — the packet is the whole-space `NSFormalization.Section3.T15.scaledVelocity`, its difference
support a single ball; (2) domain norms `E_T(Ω)`, `L¹H^s(Ω)`; (3) the boundary
clauses (collar agreement, no-slip preservation, no-slip uniqueness); (4) the
`ClassicalSolutionOmega` reference and the `∫_Ω p = 0` gauge.  The torus
`ScalingAPI` is not threaded (the domain drops periodization); `prop:scaling`
enters through the whole-space packet bounds `M`,
`E` and the constant fields.

`Type`-valued: it carries `ε₀`, the inserted `velocity`/`pressure`/`force`, and
the closeness constants as data.  Every scale-dependent field is guarded by
`ε ∈ Ioc 0 ε₀`. -/
structure BoundaryInsertionAPI (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M E : ℝ)
    (place : DomainPlacementData u p f K)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)) : Type where
  -- ### Domain and reference hypotheses `03-torus.tex:632-648`
  /-- `03-torus.tex:632-633`: `Ω` is a bounded box or bounded smooth domain.
  Quantifier order: none.  Non-vacuity: `IsBoundedBoxOrSmoothDomain` is a real
  conjunction of openness, boundedness, nonemptiness, and the box-or-smooth
  disjunction (adopted from Draft A, `RECONCILIATION.md` §3). -/
  domain : IsBoundedBoxOrSmoothDomain Ω
  /-- `03-torus.tex:634`: `δ > 0`, so the reference is regular strictly past `T`.
  Quantifier order: none.  Non-vacuity: a strict inequality on the margin used
  in `reference`'s horizon `place.T + δ`. -/
  delta_pos : 0 < δ
  /-- `03-torus.tex:634-635,640`: `g ∈ 𝓕(Ω)`, the reference force is a
  bounded-domain force (smooth on each finite closed `Ω`-slab, temporal support
  compact in `(0,∞)`).  Quantifier order: none.  Non-vacuity: membership in the
  nontrivial smooth compact class. -/
  reference_force_mem : g ∈ forceClassOmega Ω
  /-- `03-torus.tex:641,646`: `a ∈ 𝓧(Ω)`, the initial velocity is smooth,
  divergence free in `Ω`, and no-slip on `∂Ω`.  Quantifier order: none.
  Non-vacuity: `initialClassOmega` fixes all three. -/
  initial_mem : a ∈ initialClassOmega Ω
  /-- `03-torus.tex:646,653-654`: the fixed localization ball `B` is a *prescribed
  interior ball* — its closure lies strictly inside `Ω` ("a smaller closed ball
  strictly inside `Ω`").  Quantifier order: none.  Non-vacuity: a genuine set
  inclusion placing the whole insertion region inside `Ω`; combined with the
  reference's `no_slip` it yields the preserved boundary values. -/
  interiorBall_in_domain :
    closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω

  -- ### The single scale threshold `03-torus.tex:646` (thm:insertion, "sufficiently small ε")
  /-- `03-torus.tex:646`: the family threshold `ε₀`.  Non-vacuity: real data used
  by every clause below through `Ioc 0 ε₀`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:646`: `ε₀ > 0`.  Non-vacuity: `(0,ε₀]` is nonempty. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:646,103`: sub-family of `prop:scaling`, so every scaling
  bound holds on `(0,ε₀]`.  Non-vacuity: a genuine `≤`. -/
  eps_le_scaling : ε₀ ≤ place.ε₀
  /-- `03-torus.tex:646,652-654`: sub-family of `lem:correction`, so every
  correction bound holds on `(0,ε₀]`.  Non-vacuity: a genuine `≤`. -/
  eps_le_cutoff : ε₀ ≤ D.ε₀

  -- ### The inserted triple and `eq:insertion` on `Ω` `03-torus.tex:646,655`
  /-- `03-torus.tex:646`: `ε ↦ u_ε`, the inserted velocity. -/
  velocity : ℝ → VelocityField
  /-- `03-torus.tex:644,646`: `ε ↦ p_ε`, the inserted pressure. -/
  pressure : ℝ → SpaceTimeScalar
  /-- `03-torus.tex:646`: `ε ↦ g_ε`, the inserted force. -/
  force : ℝ → VelocityField
  /-- `03-torus.tex:646,655` `eq:insertion`, first display: `u_ε = v + w_ε + U_ε`
  with `v = reference.velocity`, `w_ε = D.correction ε` (`lem:potential`), and
  `U_ε = NSFormalization.Section3.T15.scaledVelocity u x₀ T ε` the whole-space rescaled packet.  TORUS:
  the un-periodized single copy (`NSFormalization.Section3.T15.scaledVelocity`), not `periodizedScaledVelocity`.
  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise field equation fixing
  `velocity` on all spacetime. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = reference.velocity z + D.correction ε z +
      NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z
  /-- `03-torus.tex:644,646` `eq:insertion`, second display: `p_ε = π + P_ε`
  normalized to zero spatial mean over `Ω`, where `π = reference.pressure` and
  `P_ε = NSFormalization.Section3.T15.scaledPressure p x₀ T ε`.  TORUS: the `∫_Ω p = 0` gauge
  (`domainNormalizePressure`), not the torus Haar gauge.  Quantifier order:
  `∀ ε`.  Non-vacuity: fixes `pressure ε` as a concrete normalized field. -/
  pressure_formula : ∀ ε : ℝ,
    pressure ε = domainNormalizePressure Ω
      (fun z => reference.pressure z + NSFormalization.Section3.T15.scaledPressure p place.x₀ place.T ε z)
  /-- `03-torus.tex:646,655` `eq:insertion`, third display: `g_ε = g + H_ε + F_ε`
  with `H_ε = correctionForce ν v D ε` (`lem:correction`) and
  `F_ε = NSFormalization.Section3.T15.scaledForce f x₀ T ε` the whole-space rescaled packet force.
  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise field equation. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ν reference.velocity D ε z +
      NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε z

  -- ### Force-class memberships `03-torus.tex:646,656`
  /-- `03-torus.tex:646,656`: `g_ε ∈ 𝓕(Ω)`, the inserted force is a
  bounded-domain force ("has the same globally smooth time extension").
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: membership of the actual
  inserted force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, force ε ∈ forceClassOmega Ω
  /-- `03-torus.tex:646,656`: the force perturbation `g_ε - g = H_ε + F_ε` is a
  bounded-domain force.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity:
  `forceClassOmega` membership of the actual difference. -/
  forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (fun z => force ε z - g z) ∈ forceClassOmega Ω

  -- ### A classical no-slip trajectory on `Ω × [0,T)` `03-torus.tex:646,655`
  /-- `03-torus.tex:637-643,655`: `u_ε` is smooth on `[0,T) × cl Ω`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `SmoothOnClosedSlab` of the
  actual `velocity ε`. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SmoothOnClosedSlab (Ico (0 : ℝ) place.T) Ω (velocity ε)
  /-- `03-torus.tex:637-643,655`: `p_ε` is smooth on `[0,T) × cl Ω`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: `SmoothOnClosedSlab` of
  `pressure ε`. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SmoothOnClosedSlab (Ico (0 : ℝ) place.T) Ω (pressure ε)
  /-- `03-torus.tex:646` clause (ii): `u_ε(·,0) = a` on `Ω`, "preserving the
  initial velocity".  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ x ∈ Ω`.  Non-vacuity:
  pointwise equality of physical vectors. -/
  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x ∈ Ω, velocity ε (0, x) = a x
  /-- `03-torus.tex:641,655`: `div u_ε = 0` in `Ω` on `[0,T)`.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x ∈ Ω`.  Non-vacuity: the registered
  divergence vanishes pointwise. -/
  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
      spatialDivergence (velocity ε) t x = 0
  /-- `03-torus.tex:655`: "The computation of the momentum equation in
  Theorem `thm:insertion` is unchanged" — the NS equation holds exactly for
  `(u_ε, p_ε, g_ε)` at interior times in `Ω`.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω`.  Non-vacuity: the residual equals
  the inserted force pointwise at `ν`. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x ∈ Ω,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)
  /-- `03-torus.tex:655` "for all times before blowup": `u_ε = v` on the quiet
  initial slab `0 ≤ t ≤ T - 2ε²`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t,
  0 ≤ t, t ≤ T - 2ε², ∀ x`.  Non-vacuity: pointwise equality on the whole slab. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = reference.velocity (t, x)

  -- ### The boundary clauses `03-torus.tex:646,655` (TORUS: new for `Ω`)
  /-- `03-torus.tex:655`: "The new velocity equals the reference in a fixed
  boundary collar for all times before blowup."  The *fixed* collar is the
  complement of the fixed chart ball `B` (independent of `ε`): outside `B`,
  `u_ε = v`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`,
  `x ∉ B`.  Non-vacuity: pointwise equality on the entire fixed collar; the
  collar is `ε`-independent because `B` is. -/
  collar_agreement : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) place.T,
    ∀ x : Space, x ∉ Metric.ball place.chartCenter place.chartRadius →
      velocity ε (t, x) = reference.velocity (t, x)
  /-- `03-torus.tex:646,655`: "preserving the … no-slip boundary values" —
  `u_ε|_{∂Ω} = 0`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T,
  ∀ x ∈ frontier Ω`.  Non-vacuity: the inserted velocity vanishes pointwise on
  `∂Ω`; the mechanism is `collar_agreement` (the ball misses `∂Ω` via
  `interiorBall_in_domain`) plus `reference.no_slip`. -/
  noSlip_preserved : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) place.T,
    ∀ x ∈ frontier Ω, velocity ε (t, x) = 0

  -- ### Bundled solution, lifespan, and blowup `03-torus.tex:664-666`
  /-- `03-torus.tex:655,664-666`: for each `ε` the inserted pair `(u_ε, p_ε)` is
  a bounded-domain classical no-slip solution on `[0,T)` (carrying the `∫_Ω p=0`
  gauge).  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`, then `∃ w`.  Non-vacuity: the
  witness is a full `ClassicalSolutionOmega` with velocity and pressure equal to
  the inserted fields. -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionOmega ν Ω a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε
  /-- `03-torus.tex:666`: "the constructed solution is singular exactly at `T`":
  `T_max^ν,Ω(a, g_ε) = T`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an
  equality in `ℝ≥0∞` of the bounded-domain maximal lifespan with `ofReal T`, not
  a one-sided bound. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T
  /-- `03-torus.tex:664-666`: "classical uniqueness … identifies the constructed
  velocity with the maximal solution" — the inserted pair `(u_ε, p_ε)` *is* the
  maximal bounded-domain no-slip solution of `(ν, Ω, a, g_ε)`, in the record-form
  `IsMaximalDomainSolution` predicate (the domain mirror of the registered
  `IsMaximalPeriodicSolution`; concept from Draft A, record form per
  `RECONCILIATION.md` §3 "Take from A" 2).  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.
  Non-vacuity: the actual inserted fields realize every sub-horizon as a genuine
  `ClassicalSolutionOmega`, not merely one solution. -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalDomainSolution ν Ω a (force ε) (velocity ε) (pressure ε)
  /-- `03-torus.tex:666`: unbounded speed at `T`, in the pointwise
  `SpeedUnboundedAt` form.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: at
  every level `M` and left neighbourhood of `T`, a presingular time and point
  exceed `M`. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε)
  /-- `03-torus.tex:666`: the essential-supremum form,
  `limsup_{t↑T} ‖u_ε(t)‖_{L^∞} = ⊤`, in the frozen `MaximalPartial` vocabulary.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the left `limsup` of the
  concrete `L^∞` slice norm is exactly `⊤`. -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section4.A02.limsupLeft place.T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => velocity ε (t, x))) = ⊤

  -- ### The two vanishing cross-transport terms `03-torus.tex:655` (momentum exactness)
  /-- `03-torus.tex:655`: the first cross-advection term `(b_ε·∇)U_ε` vanishes,
  where `b_ε = v + w_ε` is the corrected background and `U_ε = NSFormalization.Section3.T15.scaledVelocity …`
  the whole-space packet.  TORUS: the un-periodized packet.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the directional derivative
  of the actual packet in the actual background direction vanishes pointwise. -/
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε) t x
          (correctedBackground reference.velocity D.correction ε (t, x)) = 0
  /-- `03-torus.tex:655`: the second cross-advection term `(U_ε·∇)b_ε` vanishes.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the
  directional derivative of the actual background in the actual packet direction
  vanishes pointwise, so (with the previous field) the momentum equation is
  exact. -/
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (correctedBackground reference.velocity D.correction ε) t x
          (NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε (t, x)) = 0

  -- ### Localization of the velocity/force differences `03-torus.tex:653-655,661-663`
  /-- `03-torus.tex:655`: `u_ε - v` is divergence free in `Ω` at every `t < T`.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x ∈ Ω`.  Non-vacuity: the
  divergence of the actual difference vanishes. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x ∈ Ω,
      spatialDivergence (fun z => velocity ε z - reference.velocity z) t x = 0
  /-- `03-torus.tex:653-654`: the fixed radius scale `ρ` giving the `O(ε)`
  support diameter of the localized difference.  Non-vacuity:
  `diffSupportRadius_pos` forces it positive. -/
  diffSupportRadius : ℝ
  /-- `03-torus.tex:653-654`: `ρ > 0`.  Non-vacuity: excludes a degenerate
  ball. -/
  diffSupportRadius_pos : 0 < diffSupportRadius
  /-- `03-torus.tex:653-654`: for every `t < T` the support of `u_ε - v` lies in
  the single ball of radius `ε·ρ` about `x₀` (diameter `O(ε)`).  TORUS: a single
  whole-space ball, not `periodicSet (ball …)`.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T`.  Non-vacuity: an actual `tsupport ⊆ ball`
  inclusion. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => velocity ε (t, x) - reference.velocity (t, x)) ⊆
        Metric.ball place.x₀ (ε * diffSupportRadius)
  /-- `03-torus.tex:653-654` "inside the chosen ball": the `O(ε)`-ball lies in the
  fixed chart ball `B`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: an
  actual metric-ball inclusion in `B`. -/
  diffSupport_in_chart : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Metric.ball place.x₀ (ε * diffSupportRadius) ⊆
      Metric.ball place.chartCenter place.chartRadius
  /-- `03-torus.tex:661-663`: "All these force-difference supports, including
  those after `T`, lie in one fixed compact interior ball `K` for every
  sufficiently small `ε`."  Here `K = cl B ⊆ Ω` (compact, interior; see
  `interiorBall_in_domain`), and the containment is stated for *all* real times
  `t`, capturing the post-`T` supports.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀,
  ∀ t, ∀ x`, nonvanishing hypothesis, then membership.  Non-vacuity: it fixes an
  `ε`-independent compact interior spatial support for `g_ε - g`, the fact making
  the `eq:zero-extension` comparison scale-independent. -/
  forceDifference_spatialSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
      x ∈ closure (Metric.ball place.chartCenter place.chartRadius)

  -- ### The energy closeness rate `03-torus.tex:647,664` (uses `L²(Ω)`)
  /-- `03-torus.tex:647` `eq:Eclose` on `Ω`: the correction energy constant
  `C = energyConst` (`eq:wE`).  Non-vacuity: `energyConst_nonneg` prevents a
  negative witness erased by `ENNReal.ofReal`. -/
  energyConst : ℝ
  /-- `03-torus.tex:647`: `C ≥ 0`.  Non-vacuity: on the used range. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- `03-torus.tex:647,664` `eq:Eclose` on `Ω`: `‖u_ε - v‖_{E_T(Ω)} ≤
  (M+D)ε^{1/2} + Cε^{3/2}` with `M = M`, `D = E`
  (`lem:packetenergy`), `C = energyConst`.  TORUS: the energy norm is `E_T(Ω)`
  (`L²(Ω)`), via `domainEnergyENorm`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.
  Non-vacuity: an `ℝ≥0∞` inequality on the actual `Ω`-energy norm of the actual
  difference. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainEnergyENorm Ω place.T (fun z => velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) +
        energyConst * ε ^ ((3 : ℝ) / 2))

  -- ### The force closeness rate `03-torus.tex:647-649,663` (uses `L¹(0,∞;H^s(Ω))`)
  /-- `03-torus.tex:647-649` `eq:Hsclose` on `Ω`: the Sobolev constant `C_s`.
  Non-vacuity: `forceDiffSobolevConst_pos` forces it positive on the used
  range. -/
  forceDiffSobolevConst : ℝ → ℝ
  /-- `03-torus.tex:649-650`: `C_s > 0` on `0 ≤ s < 1/2`.  TORUS/paper: the range
  stops at `1/2` (`:650`, "the convergence assertion remains `s<1/2`"), not `1`.
  Quantifier order: `∀ s, 0 ≤ s, s < 1/2`.  Non-vacuity: strict positivity on the
  exact range. -/
  forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < forceDiffSobolevConst s
  /-- `03-torus.tex:647-649,658-660` `eq:Hsclose` on `Ω`: `‖g_ε - g‖_{L¹_tH^s(Ω)}
  ≤ C_s(ε^{1/2-s} + ε^{3/2-s})` for `0 ≤ s < 1/2`, with the restriction norm
  `eq:restriction-norm` (`domainForceSobolevENorm`).  Quantifier order: `∀ s,
  0 ≤ s, s < 1/2, ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the empty-`⨅ = ⊤` restriction
  norm makes this `≤ finite` bound self-guarding (it forces an honest `H^s(Ω)`
  slice a.e.). -/
  forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))
  /-- `03-torus.tex:649-650,661-663`, `eq:zero-extension`: "For every real `s`,
  the domain and zero-extended force-difference norms are comparable … with a
  constant independent of `ε`."  For each `s`, one `C > 0` (chosen before `ε`,
  hence `ε`-independent) two-sidedly compares the `L¹H^s(Ω)` restriction norm and
  the whole-space `L¹H^s(R³)` zero-extension norm of `g_ε - g`.  Consumes
  `norms.zeroExtensionComparison` and `forceDifference_spatialSupport` (see
  `research/T23/COMPARISON_B.md`).  Quantifier order: `∀ s, ∃ C, 0 < C ∧
  ∀ ε ∈ Ioc 0 ε₀`.  Non-vacuity: the full two-sided chain between the two
  honest norms, with `C` before `ε`. -/
  domain_zeroExt_comparison : ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
          zeroExtForceSobolevENorm Ω s (fun z => force ε z - g z) ∧
      zeroExtForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
          ENNReal.ofReal C *
            domainForceSobolevENorm Ω s (fun z => force ε z - g z)
  /-- `03-torus.tex:659-660`: "For `s < 0`, use
  `‖E_0(g_ε-g)‖_{H^s(R³)} ≤ ‖E_0(g_ε-g)‖_{L²(R³)}` at each time" — the force
  difference tends to zero in `L¹_tH^s(Ω)` as `ε ↓ 0`.  Quantifier order:
  `∀ s, s < 0`, then the `Tendsto`.  Non-vacuity: convergence of the restriction
  norm of the actual difference to `0`. -/
  forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => domainForceSobolevENorm Ω s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  /-- `03-torus.tex:650`: "the convergence assertion remains `s<1/2`" — for
  `0 ≤ s < 1/2` the force difference tends to zero in `L¹_tH^s(Ω)`.  Quantifier
  order: `∀ s, 0 ≤ s, s < 1/2`, then the `Tendsto`.  Non-vacuity: convergence to
  finite `0` in `ℝ≥0∞` of the restriction norm; it is the corollary's asserted
  subcritical convergence. -/
  forceDifference_convergence : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    Tendsto (fun ε : ℝ => domainForceSobolevENorm Ω s (fun z => force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

  -- ### Classical no-slip uniqueness `03-torus.tex:664-665`
  /-- `03-torus.tex:664-665`: "classical uniqueness on a no-slip domain follows
  from the same difference-energy calculation as in Proposition `prop:local`;
  its boundary terms vanish."  Two bounded-domain no-slip solutions with the same
  data agree in velocity on `Ω` throughout their common interval.  Quantifier
  order: `∀ a' ∈ 𝓧(Ω), ∀ f ∈ 𝓕(Ω), ∀ T₁ T₂, ∀ u₁ u₂, ∀ t ∈ Ico 0 (min T₁ T₂),
  ∀ x ∈ Ω`.  Non-vacuity: pointwise equality of physical velocities; this is the
  uniqueness `lifespan`/`solution` rely on for "singular exactly at `T`". -/
  noSlip_uniqueness : ∀ (a' : SpatialField), a' ∈ initialClassOmega Ω →
    ∀ (f : SpaceTimeField), f ∈ forceClassOmega Ω →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionOmega ν Ω a' f T₁)
        (u₂ : ClassicalSolutionOmega ν Ω a' f T₂),
        ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x ∈ Ω,
          u₁.velocity (t, x) = u₂.velocity (t, x)

/-- **The existential form of `cor:boundary`,
`paper/sections/03-torus.tex:632-651`.**  Paper quantifier order: for every
`ν > 0`, packet `P`, cube-free interior placement `place`, bounded domain `Ω`,
bounded-domain norm layer `norms`, initial datum `a`, reference force `g`, radii
`r`, margin `δ`, cutoff data `D`, and bounded-domain no-slip reference regular
through `T+δ`, with `Ω` a bounded box or bounded smooth domain, `δ > 0`,
`g ∈ 𝓕(Ω)`, `a ∈ 𝓧(Ω)`, and the interior ball's closure strictly inside `Ω`,
there is an inserted family: `Nonempty` of the API, which carries `ε₀` as a
field.  Introducing this definition asserts nothing.

Non-vacuity: with the cube-free `DomainPlacementData` (no `chartBall_in_cube`),
the interior-ball hypothesis `closure(ball …) ⊆ Ω` is satisfiable for *every*
admissible `Ω` (e.g. `Ω = (1,2)³`), so the statement is not vacuous off the unit
cube (Draft B's trap) and not false for domains missing the origin (Draft A's
trap); see `RECONCILIATION.md` §"False clauses". -/
def boundaryInsertionStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M E : ℝ)
    (place : DomainPlacementData u p f K)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)),
    IsBoundedBoxOrSmoothDomain Ω → 0 < δ → g ∈ forceClassOmega Ω →
      a ∈ initialClassOmega Ω →
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω →
        Nonempty
          (BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference)

/-- G0 repair: choose the full matching whole-space supplier and cutoff together. -/
def boundaryInsertionStatement' : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M E : ℝ)
    (place : DomainPlacementData u p f K)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)),
    IsBoundedBoxOrSmoothDomain Ω → 0 < δ → 0 < r →
      g ∈ forceClassOmega Ω → a ∈ initialClassOmega Ω →
      closure (Metric.ball place.x₀ r) ⊆ Metric.ball place.chartCenter place.chartRadius →
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω →
      ∃ (C : WholeSpaceCorrectionAPI ν u K) (D : CutoffData),
        C.T = place.T ∧ C.δ = δ ∧ C.x₀ = place.x₀ ∧ C.r = r ∧
        (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r,
          C.v (t, x) = reference.velocity (t, x)) ∧
        D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
        D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧
        D.potential = C.potential ∧ D.correction = C.correction ∧
        Nonempty (BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference)

/-- G0's exact false instance for the canonical 48-field interface. -/
theorem boundaryInsertionAPI_zero_cutoff
    (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (M E : ℝ) (place : DomainPlacementData u p f K)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : CutoffData) (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (hD : D.ε₀ = 0) :
    ¬ Nonempty (BoundaryInsertionAPI ν u p f K M E place Ω norms a g r δ D reference) := by
  rintro ⟨A⟩
  have hl := A.eps_le_cutoff
  rw [hD] at hl
  exact (not_lt_of_ge hl) A.eps_pos

end NSFormalization.Section3.T23
