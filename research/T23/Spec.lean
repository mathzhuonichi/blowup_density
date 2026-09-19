import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.InsertionFamily
import Contracts.V1.Correction
import Contracts.V1.Scaling
import Contracts.V1.HomogeneousNorm
import Contracts.V1.MaximalPartial
import Contracts.V2.InsertionLifespan
import Contracts.V1.Data

/-!
# T23 reconciled specification: Corollary `cor:boundary` (interior no-slip insertion)

Statement-only (rule 2 of `CLAUDE.md`) for
`paper/sections/03-torus.tex:632-666`, the corollary *Interior no-slip
insertion* and its proof.  No proofs, no `sorry`, no axioms.

This is the **reconciliation** of the two blind drafts — lane 368 (Draft A,
codex gpt-5.6-sol) and lane 374 (Draft B, Opus) — per the lead-approved
`research/T23/RECONCILIATION.md`.  **Base draft: B** (mirrors the reconciled
T18 `PeriodicInsertionAPI` field-for-field, un-periodized whole-space packet,
threaded T22 norm layer, per-slice `L¹H^s(Ω)`).  Three binding changes from the
reconciliation are folded in:
  1. **Cube-free interior placement** (`DomainPlacementData`, §0 below) replacing
     Draft B's torus `PlacementData` and Draft A's origin-centred support — the
     single most important ruling (`RECONCILIATION.md` §"False clauses" #1–2).
  2. **Draft A's domain-shape disjunction** `IsBoundedBoxOrSmoothDomain`
     (`IsBoxDomain ∨ IsRegularLevelDomain`), plus Draft B's explicit `Ω.Nonempty`.
  3. **A record-form `maximal` field** (`IsMaximalDomainSolution`), concept from
     Draft A, spelled like the registered `IsMaximalPeriodicSolution`.

`cor:boundary` is `thm:insertion` (T18) restricted to a bounded domain
`Ω ⊂ R³`: the localized packet/correction insertion is performed inside a fixed
interior ball `B ⋐ Ω`, so the new velocity equals the reference in a fixed
boundary collar and the no-slip boundary values are preserved; the energy uses
`L²(Ω)` and the force uses `L¹(0,∞;H^s(Ω))` with the restriction norm
`eq:restriction-norm`, whose comparison with the whole-space zero-extension
norm `eq:zero-extension` is `ε`-uniform; and classical no-slip uniqueness holds
by the same difference-energy calculation as `prop:local`.

## What is imported vs. copied

* **Imported registered contracts** (used by name): `Contracts.V1.Data`
  (`SpatialField`, `sobolevENorm`, `spatialGradient`, `spatialDivergence`, …),
  `Contracts.V1.Packet` / `Contracts.V1.PacketImport`
  (`PacketAPI`, `PacketImportAPI`, `navierStokesResidual`, `spatialDerivative`,
  `temporalDerivative`, `spatialLaplacian`, `advection`, `zeroPastField`),
  `Contracts.V1.Scaling` / `Contracts.V1.Correction`
  (`scaledPacket`, `scaledPressure`, `scaledForce`, `SpeedUnboundedAt`),
  `Contracts.V1.MaximalPartial` (`limsupLeft`, `speedENorm`),
  `Contracts.V1.TorusData` / `Contracts.V1.TorusLocalTheory` (loaded so the
  registered vocabulary namespace is available).  **The registered whole-space
  `ScalingAPI`/`CorrectionAPI` are consumed, not threaded** — asymmetric to T18,
  which threads the *torus* (unregistered) scaling/correction chain (`prop:scaling`
  therefore enters as the whole-space packet energy/force rate *constants*, which
  appear as fields, plus `P.energyBound`, `P.dissipationBound`).  The rescaled
  packet is the registered `scaledPacket`/`scaledPressure`/`scaledForce`, so no
  wrapper is copied.
* **Copied verbatim** (T13 copy policy — same names, namespaces, provenance
  comments): from `research/T18/Spec.lean` the shared insertion vocabulary
  `CutoffData` and `correctedBackground` (T16.Draft), `correctionForce`
  (T17.Spec); from `research/T22/Spec.lean` the reconciled bounded-domain norm
  layer `DomainTest`, `DomainFunctional`, `restrictDatum`, `domainSobolevENorm`,
  `restrictField`, `zeroExtension`, `IsCutoffDatum`, `BoundedDomainNormAPI`.
  The torus `fundamentalCube` (T13.Spec) and `PlacementData` (T15.Draft) are
  **dropped** — the cube-free `DomainPlacementData` (§0) is adapted from the
  latter with `chartBall_in_cube`/`fundamentalCube` removed.

## How the torus (T18) differs on the bounded domain (documented inline)

1. **No periodization.**  The domain uses the single whole-space rescaled packet
   `scaledPacket P.velocity …` (support in one interior ball `⋐ Ω`), not
   `periodizedScaledVelocity`; the velocity-difference support is a single ball,
   not `periodicSet (ball …)`.  The torus scaling record `ScalingAPI` (the
   periodization layer) is therefore not threaded; the registered whole-space
   scaling/correction are consumed at proof time.
2. **Domain norms.**  Energy in `L²(Ω)` and force in `L¹(0,∞;H^s(Ω))` use the
   restriction norm (`domainSobolevENorm`, `restrictField`), not the torus Haar
   norms; `BoundedDomainNormAPI` (T22, unregistered) is **threaded** as the
   norm-layer input and consumed by `domain_zeroExt_comparison`.
3. **No-slip boundary.**  New clauses: the fixed boundary collar agreement, the
   preserved no-slip values, and classical no-slip uniqueness.
4. **Reference and pressure gauge.**  The reference is a bounded-domain no-slip
   classical solution `ClassicalSolutionOmega` (the paper's assumed compatible
   reference), not the periodic `ClassicalSolutionT`; the pressure gauge is zero
   spatial mean over `Ω`.

The local implementation candidate
`formalization/NSFormalization/Paper1/BoundaryCorollary.lean` (`BoundedReference`,
`BoundedFlow`, `domainForceNorm`, `exists_interior_noSlip_insertion`) has a
`sorry` at `:90` and is **cited only, never imported**.

`Type`-valued structures carry data (fields as data: velocity/pressure/force,
`ε₀`, closeness constants); `Prop`-valued ones carry only hypotheses/conclusions.
Suprema are `ℝ≥0∞` `⨆`/`⨅`, never real `sSup`.  The bounded-domain quotient norm
is the empty-`⨅ = ⊤` fail-safe infimum, so every displayed `≤ finite` bound is
self-guarding (it forces the norm finite), exactly as the torus `energyENormT`
bounds are.
-/

noncomputable section

open Set MeasureTheory Filter Topology

-- copied verbatim from research/T18/Spec.lean:863-922 (T16.Draft)
namespace BlowupDensity.T16.Draft

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open Set MeasureTheory
open scoped ContDiff Topology

/-- The corrected background `v + w_ε` in `eq:bgzero`;
`paper/sections/03-torus.tex:190-192`.

Non-vacuity: evaluation is the pointwise sum of the given reference and the
chosen correction at the specified scale. -/
def correctedBackground (v : SpaceTimeField) (w : ℝ → SpaceTimeField) (ε : ℝ) :
    SpaceTimeField :=
  fun z => v z + w ε z

/-- The witnesses chosen once before the small scale `ε` is quantified;
`paper/sections/03-torus.tex:167-188,212`.

The data live in `Type`, while `LocalPotentialAPI` lives in `Prop`, so
downstream consumers can project the actual cutoffs, threshold, potential, and
correction family. -/
structure CutoffData where
  /-- Spatial cutoff from the Urysohn construction;
  `paper/sections/03-torus.tex:167-172,181`.

  Non-vacuity: this is a concrete real-valued function on physical space. -/
  θ : Space → ℝ
  /-- Temporal cutoff used in `eq:cutoff`;
  `paper/sections/03-torus.tex:173-174,182-186`.

  Non-vacuity: this is a concrete real-valued function of physical time. -/
  η : ℝ → ℝ
  /-- Open plateau on which `θ` is one;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: the set is retained as data and is constrained below to contain
  the prescribed compact set. -/
  plateau : Set Space
  /-- Fixed support radius for `θ`;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: the API requires this actual real radius to be strictly
  positive and to bound `tsupport θ`. -/
  θRadius : ℝ
  /-- Common upper threshold for every sufficiently small `ε`;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the API requires one strictly positive threshold shared by all
  scale-dependent conclusions. -/
  ε₀ : ℝ
  /-- Radial vector potential `A` from `eq:potential`;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: this is a concrete time-first spacetime vector field whose
  formula and curl are fixed below. -/
  potential : SpaceTimeField
  /-- Scale-indexed correction family `w_ε` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-193`.

  Non-vacuity: this is one concrete family shared by smoothness, periodicity,
  support, divergence, and cancellation fields. -/
  correction : ℝ → SpaceTimeField

end BlowupDensity.T16.Draft

-- copied verbatim from research/T18/Spec.lean:1330-1339 (T17.Spec)
namespace BlowupDensity.T17.Spec

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T16.Draft
open Set MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators

/-- `03-torus.tex:219-223`: the registered force formula
`∂ₜw−νΔw+(v·∇)w+(w·∇)v+(w·∇)w`. -/
def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2

end BlowupDensity.T17.Spec

-- copied verbatim from research/T22/Spec.lean:1-190 (T22.Draft)
namespace BlowupDensity.T22.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## Bounded-domain distributional vocabulary -/

/-- `03-torus.tex:601-604`: compactly supported smooth tests inside `Omega`,
represented as Schwartz functions on `R^3`.

This definition needs registration. -/
abbrev DomainTest (Ω : Set Space) :=
  {ψ : SchwartzMap Space ℂ // HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω}

/-- `03-torus.tex:601-606`: coordinates of a distribution restricted to
`Omega`.  Only functionals admitting a Sobolev extension have finite norm
below; the ambient type itself is deliberately total.

This definition needs registration. -/
abbrev DomainFunctional (Ω : Set Space) := Fin 3 → DomainTest Ω → ℂ

/-- `03-torus.tex:601-604`: distributional restriction of a registered
whole-space datum, including at negative orders.

This definition needs registration. -/
def restrictDatum (Ω : Set Space) (s : ℝ) (A : RealVectorSobolev s) :
    DomainFunctional Ω :=
  fun i ψ => angularRealization s ((A i : FourierData)) ψ.1

/-- `03-torus.tex:603-606`, `eq:restriction-norm`: the quotient extended norm,
literally the infimum over all distributional `H^s(R^3)` extensions.  An empty
extension family has value `top`, so the definition remains fail-safe at every
real order, including negative orders.

This definition needs registration. -/
def domainSobolevENorm (Ω : Set Space) (s : ℝ)
    (z : DomainFunctional Ω) : ℝ≥0∞ :=
  ⨅ A : {A : RealVectorSobolev s // restrictDatum Ω s A = z}, ‖A.1‖ₑ

/-- `03-torus.tex:608-615`: a locally smooth physical field restricted to
`Omega`, paired only against compactly supported interior tests.  Values
outside `Omega` do not contribute.

This definition needs registration. -/
def restrictField (Ω : Set Space) (z : SpatialField) : DomainFunctional Ω :=
  fun i ψ => ∫ x in Ω, ψ.1 x * ((z x i : ℝ) : ℂ)

/-- `03-torus.tex:610-615`: literal extension by zero of the values on
`Omega`.  Values supplied by the ambient representative outside `Omega` are
ignored.

This definition needs registration. -/
def zeroExtension (Ω : Set Space) (z : SpatialField) : SpatialField :=
  Ω.indicator z

/-- `03-torus.tex:616-624`: `B` is the product of a whole-space Sobolev datum
`A` by the fixed real cutoff `chi`, expressed through the transpose action on
Schwartz tests.  No conjugation is inserted.

For the smooth compact cutoffs quantified in `cutoffMultiplier`,
`SchwartzMap.smulLeftCLM` is ordinary pointwise multiplication.  This graph
definition needs registration. -/
def IsCutoffDatum (s : ℝ) (χ : Space → ℝ)
    (A B : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((B i : FourierData)) ψ =
      angularRealization s ((A i : FourierData))
        (SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ)) ψ)

/-! ## Reconciled target API -/

/-- The three bounded-domain norm facts selected by
`research/T22/RECONCILIATION.md` for `03-torus.tex:600-630`.

The quotient-norm identity is the definition `domainSobolevENorm`, rather than
a redundant API field.  `Omega` is any open set; boundedness and boundary
regularity are not used by these local statements. -/
structure BoundedDomainNormAPI : Prop where
  /-- `03-torus.tex:606-607`: at order zero the restriction quotient norm is
  the usual vector `L^2(Omega)` norm.  Local smoothness makes the displayed
  physical pairing meaningful; either side is allowed to be infinite.

  Exact quantifier order: `forall Omega`, openness, `forall z`, then
  smoothness on `Omega`.

  Non-vacuity: this equates the independently defined distributional infimum
  with the concrete restricted-measure `eLpNorm`; it is not an unfolding of
  `domainSobolevENorm`. -/
  orderZero : ∀ (Ω : Set Space), IsOpen Ω → ∀ z : SpatialField,
    ContDiffOn ℝ ∞ z Ω →
    domainSobolevENorm Ω 0 (restrictField Ω z) =
      eLpNorm z 2 (volume.restrict Ω)

  /-- `03-torus.tex:616-624`: multiplication by a fixed compactly supported
  smooth cutoff is bounded on `H^s(R^3)` for every real `s`.  The finite
  positive constant depends only on `s` and `chi`, and is chosen before `A`.

  Exact quantifier order: `forall s chi`, regularity of `chi`, `exists C > 0`,
  `forall A`, then `exists B` realizing the cutoff product.

  Non-vacuity: the conclusion produces an actual datum `B`, pins its
  distributional graph by `IsCutoffDatum`, and bounds its concrete extended
  norm uniformly over all input data. -/
  cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ

  /-- `03-torus.tex:608-626`, `eq:zero-extension`: for a fixed compact
  `K` contained in an open `Omega`, every real Sobolev order has one positive
  constant giving the displayed two-sided comparison for all smooth fields
  whose zero extension is supported in `K`.

  Exact quantifier order: `forall Omega K`, the geometric hypotheses,
  `forall s`, `exists C > 0`, and only then `forall z`.  Thus `C` is uniform
  over smaller supports, time slices, and shrinking `epsilon`-families that
  stay inside the same `K`, as required at `03-torus.tex:626-629`.

  Non-vacuity: the conclusion is the full chain between the domain quotient
  norm and the registered whole-space norm of the literal zero extension.
  Its interior-support hypothesis deliberately prevents this field from
  asserting a bounded zero-extension operator on arbitrary domain data. -/
  zeroExtensionComparison :
      ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
        ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
          ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
          domainSobolevENorm Ω s (restrictField Ω z) ≤
              sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
              ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)

end BlowupDensity.T22.Draft

/-! # T23 reconciled spec: the bounded-domain layer and `cor:boundary` -/

namespace BlowupDensity.T23.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T16.Draft
open BlowupDensity.T17.Spec
open BlowupDensity.T22.Draft
open scoped ContDiff ENNReal BigOperators Topology

/-! ## 0. Cube-free interior placement `03-torus.tex:101-107,646,653-654`

The reconciliation (`research/T23/RECONCILIATION.md` §"False clauses" #1–2, §3)
rejects both blind drafts' interior-ball encoding: Draft A hard-codes the support
ball at the **origin** (`boundaryInsertionStatement` becomes FALSE for admissible
domains not containing `0`, e.g. `Ω = (1,2)³`), and Draft B threads the torus
`PlacementData` whose `chartBall_in_cube : closure(ball …) ⊆ interior (0,1)³`
makes the statement **vacuous** for `Ω` disjoint from the unit cube.  The fix is a
**cube-free** placement: Draft A's origin center is dropped (support balls are
centred at the free `x₀`, as in Draft B), and Draft B's torus cube field
`chartBall_in_cube` / `fundamentalCube` is dropped.  The domain containment is
carried instead by `BoundaryInsertionAPI.interiorBall_in_domain :
closure(ball chartCenter chartRadius) ⊆ Ω`. -/

/-- Cube-free interior placement data, **adapted from** the T15 torus
`PlacementData` (`research/T18/Spec.lean:454-548`) by **removing**
`chartBall_in_cube` (the torus artifact `closure(ball …) ⊆ interior
fundamentalCube`) and never referencing `fundamentalCube`; every other field is
kept verbatim.  On a bounded domain `Ω ⊂ R³` there is no torus, so the ball's
placement is fixed by the free center `chartCenter`/`x₀` and its interior
containment is a field of the API (`interiorBall_in_domain`), not of the
placement.  `Kstar` still contains both spatial packet supports.

Non-vacuity: the fields below constrain actual real data (a positive time,
a positive-radius metric ball, a compact `Kstar` carrying the packet and force
supports, a positive threshold with genuine scale conditions); nothing is
`True`. -/
structure DomainPlacementData {ν : ℝ} (P : PacketAPI ν) where
  /-- `03-torus.tex:103-106`: the target singular time `T`.

  Non-vacuity: positivity makes `(0,T)` a genuine evolution interval. -/
  T : ℝ
  /-- `03-torus.tex:103-106`: `0<T`.

  Non-vacuity: this rules out the empty or reversed time interval. -/
  time_pos : 0 < T
  /-- `03-torus.tex:102-105`: center of the fixed localization ball `B`.

  Non-vacuity: it is used in the concrete ball containment below. -/
  chartCenter : Space
  /-- `03-torus.tex:102-105`: radius of the fixed localization ball `B`.

  Non-vacuity: the next field requires this radius to be positive. -/
  chartRadius : ℝ
  /-- `03-torus.tex:102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:102,105`: the placement center `x₀∈B`.

  Non-vacuity: the point is tied to the same concrete chart ball. -/
  x₀ : Space
  /-- `03-torus.tex:102`: `x₀∈B`.

  Non-vacuity: this is membership in the explicit ball above. -/
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  /-- `03-torus.tex:101-102`: the compact spatial set `K_*` enlarged to cover
  both the velocity/pressure carrier and the spatial projection of `supp F`.

  Non-vacuity: the following three fields constrain this actual set. -/
  Kstar : Set Space
  /-- `03-torus.tex:101`: `K_*` is compact.

  Non-vacuity: this is an assertion about the carried set, not an existential
  choice made separately for each scale. -/
  Kstar_compact : IsCompact Kstar
  /-- `03-torus.tex:101`: `K⊆K_*`, where `K` is T14's packet carrier.

  Exact quantifier order: every point of `P.carrier` lies in the fixed
  `Kstar`.  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : P.carrier ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  /-- `03-torus.tex:103`: one positive threshold for all sufficiently small
  scales.

  Non-vacuity: every conclusion below uses the same interval `(0,ε₀]`. -/
  ε₀ : ℝ
  /-- `03-torus.tex:103`: `ε₀>0`.

  Non-vacuity: `(0,ε₀]` contains admissible scales. -/
  eps_pos : 0 < ε₀
  /-- `03-torus.tex:103`, harmless normalization after shrinking: `ε₀≤1`.

  Non-vacuity: this is a quantitative restriction on the one threshold. -/
  eps_le_one : ε₀ ≤ 1
  /-- `03-torus.tex:104-106`: `2ε²<T`, before `t_ε` is defined.

  Exact quantifier order: first `ε∈(0,ε₀]`, then the inequality.
  Non-vacuity: it gives `t_ε>0`, so positive-time force norms contain the
  complete rescaled temporal support. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  /-- `03-torus.tex:104-105`: `x₀+εK_*⊆B`.

  Exact quantifier order: first `ε∈(0,ε₀]`, then every `y∈Kstar`.
  Non-vacuity: together with `interiorBall_in_domain`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-! ## 0'. Bounded-domain geometry, classes, and the smoothness convention -/

/-- `03-torus.tex:638-642`: the manuscript's closed-spacetime-slab smoothness
convention — "restriction of a `C∞` field from an open neighborhood of that
slab" (this also fixes smoothness at edges and corners of a box).  Encoded as
the literal restriction: an open `N` covering the slab `I × cl Ω` on which the
(total) field is genuinely `C∞`.

Non-vacuity: `ContDiffOn ℝ ∞ f N` on the open `N` is real smoothness, not the
closed-set `ContDiffOn` on `cl Ω`; it is the honest reading of the convention. -/
def SmoothOnClosedSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (Ω : Set Space) (f : SpaceTime → E) : Prop :=
  ∃ N : Set SpaceTime, IsOpen N ∧ I ×ˢ closure Ω ⊆ N ∧ ContDiffOn ℝ ∞ f N

/-- `03-torus.tex:632-634`: concrete regular-level-set encoding of a bounded
smooth domain (adopted from Draft A per `RECONCILIATION.md` §3 "Take from A" 1).
A `C∞` defining function `φ` with `Ω = {φ < 0}` and nonvanishing boundary
gradient.  The box-vs-smooth distinction governs only the *assumed* reference's
elliptic regularity (`:645`), which the corollary takes as a hypothesis; but
statement fidelity (`CLAUDE.md` rule 2) keeps the paper's disjunction.

Non-vacuity: it carries an actual `C∞` defining function and a nonzero boundary
derivative, not an unconstrained proposition; owner question `RECONCILIATION.md`
§4.3 flags this encoding. -/
def IsRegularLevelDomain (Ω : Set Space) : Prop :=
  ∃ φ : Space → ℝ, ContDiff ℝ ∞ φ ∧ Ω = {x | φ x < 0} ∧
    ∀ x ∈ frontier Ω, fderiv ℝ φ x ≠ 0

/-- `03-torus.tex:632-634`: coordinate-box domain (adopted from Draft A).

Non-vacuity: the stored lower and upper corners have strict coordinate
separation, so `Ω` is a genuine open box. -/
def IsBoxDomain (Ω : Set Space) : Prop :=
  ∃ lo hi : Fin 3 → ℝ, (∀ i, lo i < hi i) ∧
    Ω = {x : Space | ∀ i : Fin 3, lo i < x i ∧ x i < hi i}

/-- `03-torus.tex:632-633`: the paper's disjunctive domain class — `Ω ⊂ R³` is a
bounded box or a bounded smooth domain.  Adopted from Draft A's disjunction
(`RECONCILIATION.md` §3 "Take from A" 1), with Draft B's explicit `Ω.Nonempty`
folded in (the smooth branch `{φ < 0}` may be empty; openness already gives
measurability).  The box-vs-smooth disjunction is kept for statement fidelity.

Non-vacuity: a genuine conjunction of openness, boundedness, nonemptiness, and
the honest box-or-smooth disjunction on `Ω`; it is neither `True` nor an
unfolding. -/
def IsBoundedBoxOrSmoothDomain (Ω : Set Space) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Ω.Nonempty ∧
    (IsBoxDomain Ω ∨ IsRegularLevelDomain Ω)

/-- `02-preliminaries.tex:9` and `03-torus.tex:640-644`: the bounded-domain
initial class — smooth on `cl Ω` (slab convention at `t=0`), divergence free in
`Ω`, and no-slip on `∂Ω`.  The torus analogue is `initialClassT`.

Non-vacuity: three concrete clauses; the divergence reuses the registered
`spatialDivergence` of the constant-in-time extension. -/
def initialClassOmega (Ω : Set Space) : Set SpatialField :=
  {a | ContDiffOn ℝ ∞ a (closure Ω) ∧
    (∀ x ∈ Ω, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0) ∧
    (∀ x ∈ frontier Ω, a x = 0)}

/-- `03-torus.tex:638-642`: the bounded-domain force class `𝓕(Ω)` — smooth on
`cl Ω × [0,T']` for every finite `T'` (slab convention, "`g` on each finite
closed slab"), with temporal support compact in `(0,∞)`.  The torus analogue is
`MemForceT`; periodicity is dropped and smoothness is over `cl Ω`.

Non-vacuity: the smoothness conjunct is universal over `T'`, and the temporal
support conjunct is a genuine compact-in-`(0,∞)` witness. -/
def MemForceOmega (Ω : Set Space) (f : SpaceTimeField) : Prop :=
  (∀ T' : ℝ, SmoothOnClosedSlab (Icc (0 : ℝ) T') Ω f) ∧
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ (univ : Set Space)

/-- `03-torus.tex:638-642`: the bounded-domain reference/inserted force class. -/
def forceClassOmega (Ω : Set Space) : Set SpaceTimeField := {f | MemForceOmega Ω f}

/-! ## 1. Bounded-domain classical no-slip solutions -/

/-- `03-torus.tex:640-648` and `02-preliminaries.tex:28-36`: a classical
no-slip solution of Navier–Stokes on the bounded domain `Ω` over `[0,T)`, at
viscosity `ν`, initial velocity `a`, force `g`, with the equation and
incompressibility holding *in* `Ω`, no-slip on `∂Ω`, and the pressure fixed by
zero spatial mean over `Ω` (`:644`, "Pressure may be normalized by zero spatial
mean").  This is the paper's assumed *compatible reference* (`:648`).

**Structure exception** (`CLAUDE.md`): a genuinely new bounded-domain solution
record, mirroring the registered torus `ClassicalSolutionT`
(`Contracts/V1/TorusLocalTheory.lean`) field-for-field with `univ → cl Ω`,
periodicity/`sobolev` dropped, no-slip added, and the equation restricted to
`Ω`.  The local implementation candidate is
`Paper1/BoundaryCorollary.lean:28` `BoundedReference` / `:42` `BoundedFlow`
(cite only; that module has a `sorry`). -/
structure ClassicalSolutionOmega (ν : ℝ) (Ω : Set Space) (a : SpatialField)
    (g : SpaceTimeField) (T : ℝ) where
  /-- `02-preliminaries.tex:28-36`: the velocity field. -/
  velocity : SpaceTimeField
  /-- `02-preliminaries.tex:28,84-88` and `03-torus.tex:644`: the scalar
  pressure, ultimately fixed by the zero-`Ω`-mean gauge. -/
  pressure : SpaceTimeScalar
  /-- `02-preliminaries.tex:32-36`: the horizon is a genuine positive
  interval.  Non-vacuity: a strict inequality. -/
  horizon_pos : 0 < T
  /-- `03-torus.tex:637-643`: velocity smoothness on `[0,T) × cl Ω` in the
  slab-neighborhood convention.  Non-vacuity: `SmoothOnClosedSlab` gives a real
  open-neighborhood `C∞` extension. -/
  velocity_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω velocity
  /-- `03-torus.tex:637-643`: pressure smoothness on the same slab. -/
  pressure_smooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω pressure
  /-- `02-preliminaries.tex:28-29` and `03-torus.tex:643`: `u(0,·)=a` on `Ω`.
  Exact quantifier order: `∀ x ∈ Ω`.  Non-vacuity: pointwise equality of
  physical vectors on the domain. -/
  initial : ∀ x ∈ Ω, velocity (0, x) = a x
  /-- `03-torus.tex:643` "incompressibility hold in `Ω`": `div u = 0` in `Ω`.
  Exact quantifier order: `∀ t ∈ Ico 0 T, ∀ x ∈ Ω`.  Non-vacuity: the
  registered physical divergence vanishes pointwise. -/
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω, spatialDivergence velocity t x = 0
  /-- `03-torus.tex:644` "The equation … hold in `Ω`": the momentum equation at
  interior times, inside `Ω`.  Exact quantifier order: `∀ t ∈ Ioo 0 T,
  ∀ x ∈ Ω`.  Non-vacuity: the NS residual equals `g` pointwise at `ν`. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
    navierStokesResidual ν velocity pressure t x = g (t, x)
  /-- `03-torus.tex:641` "`v|_{∂Ω}=0`": no-slip on the boundary.  Exact
  quantifier order: `∀ t ∈ Ico 0 T, ∀ x ∈ frontier Ω`.  Non-vacuity: the
  velocity vanishes pointwise on `∂Ω = frontier Ω`. -/
  no_slip : ∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, velocity (t, x) = 0
  /-- `03-torus.tex:644`: the pressure gauge `∫_Ω p(t)=0`.  Exact quantifier
  order: `∀ t ∈ Ico 0 T`.  Non-vacuity: an actual set-integral equation over
  `Ω`. -/
  pressure_gauge : ∀ t ∈ Ico (0 : ℝ) T, (∫ x in Ω, pressure (t, x)) = 0

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
periodization — the packet is the whole-space `scaledPacket`, its difference
support a single ball; (2) domain norms `E_T(Ω)`, `L¹H^s(Ω)`; (3) the boundary
clauses (collar agreement, no-slip preservation, no-slip uniqueness); (4) the
`ClassicalSolutionOmega` reference and the `∫_Ω p = 0` gauge.  The torus
`ScalingAPI` is not threaded (the domain drops periodization); `prop:scaling`
enters through the whole-space packet bounds `P.energyBound`,
`P.dissipationBound` and the constant fields.

`Type`-valued: it carries `ε₀`, the inserted `velocity`/`pressure`/`force`, and
the closeness constants as data.  Every scale-dependent field is guarded by
`ε ∈ Ioc 0 ε₀`. -/
structure BoundaryInsertionAPI (ν : ℝ) (P : PacketImportAPI ν)
    (place : DomainPlacementData P.toPacketAPI)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
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
  `U_ε = scaledPacket P.velocity x₀ T ε` the whole-space rescaled packet.  TORUS:
  the un-periodized single copy (`scaledPacket`), not `periodizedScaledVelocity`.
  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise field equation fixing
  `velocity` on all spacetime. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = reference.velocity z + D.correction ε z +
      scaledPacket P.velocity place.x₀ place.T ε z
  /-- `03-torus.tex:644,646` `eq:insertion`, second display: `p_ε = π + P_ε`
  normalized to zero spatial mean over `Ω`, where `π = reference.pressure` and
  `P_ε = scaledPressure P.pressure x₀ T ε`.  TORUS: the `∫_Ω p = 0` gauge
  (`domainNormalizePressure`), not the torus Haar gauge.  Quantifier order:
  `∀ ε`.  Non-vacuity: fixes `pressure ε` as a concrete normalized field. -/
  pressure_formula : ∀ ε : ℝ,
    pressure ε = domainNormalizePressure Ω
      (fun z => reference.pressure z + scaledPressure P.pressure place.x₀ place.T ε z)
  /-- `03-torus.tex:646,655` `eq:insertion`, third display: `g_ε = g + H_ε + F_ε`
  with `H_ε = correctionForce ν v D ε` (`lem:correction`) and
  `F_ε = scaledForce P.force x₀ T ε` the whole-space rescaled packet force.
  Quantifier order: `∀ ε, ∀ z`.  Non-vacuity: a pointwise field equation. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z + correctionForce ν reference.velocity D ε z +
      scaledForce P.force place.x₀ place.T ε z

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
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft place.T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => velocity ε (t, x))) = ⊤

  -- ### The two vanishing cross-transport terms `03-torus.tex:655` (momentum exactness)
  /-- `03-torus.tex:655`: the first cross-advection term `(b_ε·∇)U_ε` vanishes,
  where `b_ε = v + w_ε` is the corrected background and `U_ε = scaledPacket …`
  the whole-space packet.  TORUS: the un-periodized packet.  Quantifier order:
  `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the directional derivative
  of the actual packet in the actual background direction vanishes pointwise. -/
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (scaledPacket P.velocity place.x₀ place.T ε) t x
          (correctedBackground reference.velocity D.correction ε (t, x)) = 0
  /-- `03-torus.tex:655`: the second cross-advection term `(U_ε·∇)b_ε` vanishes.
  Quantifier order: `∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Ico 0 T, ∀ x`.  Non-vacuity: the
  directional derivative of the actual background in the actual packet direction
  vanishes pointwise, so (with the previous field) the momentum equation is
  exact. -/
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDerivative (correctedBackground reference.velocity D.correction ε) t x
          (scaledPacket P.velocity place.x₀ place.T ε (t, x)) = 0

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
  (M+D)ε^{1/2} + Cε^{3/2}` with `M = P.energyBound`, `D = P.dissipationBound`
  (`lem:packetenergy`), `C = energyConst`.  TORUS: the energy norm is `E_T(Ω)`
  (`L²(Ω)`), via `domainEnergyENorm`.  Quantifier order: `∀ ε ∈ Ioc 0 ε₀`.
  Non-vacuity: an `ℝ≥0∞` inequality on the actual `Ω`-energy norm of the actual
  difference. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainEnergyENorm Ω place.T (fun z => velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
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
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketImportAPI ν)
    (place : DomainPlacementData P.toPacketAPI)
    (Ω : Set Space) (norms : BoundedDomainNormAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ)
    (D : BlowupDensity.T16.Draft.CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)),
    IsBoundedBoxOrSmoothDomain Ω → 0 < δ → g ∈ forceClassOmega Ω →
      a ∈ initialClassOmega Ω →
      closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω →
        Nonempty
          (BoundaryInsertionAPI ν P place Ω norms a g r δ D reference)

/-! ## 4. Drift checks

`RECONCILIATION.md` §3 "Copy policy": everything registered is imported and used
by its registered name, never copied — so no copied block below shadows a
registered declaration.  The whole-space rescaled packet objects that the three
insertion formulas point to are the registered
`BlowupDensity.Contracts.V1.{scaledPacket,scaledPressure,scaledForce}` and
`SpeedUnboundedAt`, and the blow-up field uses the registered
`MaximalPartial.{limsupLeft,speedENorm}`; the copied T22 layer's
`zeroExtensionComparison` uses the registered `Contracts.V1.Data.sobolevENorm`.
The `rfl` examples below pin the short names that appear in the statement to
their fully-qualified registered definitions, guarding against a future local
shadow (the T18 house-style `alphaT = Contracts.V1.alpha` drift check). -/

example (U : VelocityField) (x₀ : Space) (T ε : ℝ) :
    scaledPacket U x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPacket U x₀ T ε := rfl

example (Pr : PressureField) (x₀ : Space) (T ε : ℝ) :
    scaledPressure Pr x₀ T ε =
      BlowupDensity.Contracts.V1.scaledPressure Pr x₀ T ε := rfl

example (F : VelocityField) (x₀ : Space) (T ε : ℝ) :
    scaledForce F x₀ T ε =
      BlowupDensity.Contracts.V1.scaledForce F x₀ T ε := rfl

example (T : ℝ) (u : VelocityField) :
    SpeedUnboundedAt T u =
      BlowupDensity.Contracts.V1.SpeedUnboundedAt T u := rfl

example (s : ℝ) (z : SpatialField) :
    sobolevENorm s z = BlowupDensity.Contracts.V1.Data.sobolevENorm s z := rfl

end BlowupDensity.T23.Spec
