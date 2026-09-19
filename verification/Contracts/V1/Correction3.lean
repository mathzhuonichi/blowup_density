import Contracts.V1.TorusData
import Contracts.V1.TorusLocalTheory
import Contracts.V1.Packet
import Contracts.V1.PacketImport
import Contracts.V1.LocalPotential
import Contracts.V1.Localization
import Contracts.V1.Scaling

/-! T17 `lem:correction`, paper/sections/03-torus.tex:218-285.
The `Packet` namespace preserves the reconciled Spec record and unamended
statement verbatim. The enclosing namespace uses G3's raw-field spelling,
with the same 45 fields, to register the completed G4 statement.
The unamended assertion is false (nonpositive viscosity or nonperiodic
reference). G1 is resolved by global smoothness at statement level; G4 also
requires positive radius and margin, r < 1/2, local divergence, raw packet
support and ball-in-chart. Compactness, positive target time and cube geometry
come from placement. No conclusion field is weakened.
-/
noncomputable section
namespace BlowupDensity.Contracts.V1.Correction3
open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal Topology BigOperators

/- Unregistered T15 norm vocabulary, verbatim from Spec.lean:537-565. -/
/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure


/-- `03-torus.tex:133-138`: an honest periodic Sobolev Bochner path; the
registered `IsPeriodicDatum` includes Haar integrability. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure


/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`, with
`ENNReal.toReal ⊤=0`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal


/- Unregistered T15 placement, canonical raw-field spelling (G3). -/
structure PlacementData (u : VelocityField) (p : PressureField)
    (f : VelocityField) (K : Set Space) where
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
  /-- `03-torus.tex:22-23,102`: `B` has positive radius.

  Non-vacuity: this excludes an empty metric ball. -/
  chartRadius_pos : 0 < chartRadius
  /-- `03-torus.tex:22-23,102-105`: the closure of `B` is contained in the
  coordinate chart, here the interior of the fixed fundamental cube.

  Non-vacuity: this is the separation from other lattice translates used by
  the single-copy clauses. -/
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆ interior fundamentalCube
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

  Exact quantifier order: every point of `K` lies in the fixed `Kstar`.
  Non-vacuity: this links placement to the selected packet. -/
  carrier_subset : K ⊆ Kstar
  /-- `03-torus.tex:101-102`: the spatial projection of `supp F` is in `K_*`.

  Exact quantifier order: for every spacetime support point `(t,x)`, its
  spatial coordinate lies in `Kstar`.  Non-vacuity: this rules out choosing a
  set that only covers the velocity carrier. -/
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport f → x ∈ Kstar
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
  Non-vacuity: together with `chartBall_in_cube`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/- Unregistered profile vocabulary, Spec.lean:679-723 with bare (x₀,T). -/
def rescaledPotential (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  fun z => ∫ ρ in (0 : ℝ)..1,
    ρ • cross (v (T + ε ^ 2 * z.1, x₀ + ε • (ρ • z.2))) z.2

/-- `03-torus.tex:245-260`, `Spec.lean:679-682`: the fixed manuscript cylinder
in rescaled coordinates; its endpoints and radius are independent of `ε`. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) D.θRadius

/-- `03-torus.tex:256-259`, `Spec.lean:684-687`: the correction chart based at
`T` (not at `t_ε = T-ε²`); `z ↦ (T + ε²z.1, x₀ + εz.2)`. -/
def correctionChartPoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  (T + ε ^ 2 * z.1, x₀ + ε • z.2)

/-- `03-torus.tex:256-259`, `Spec.lean:706-709`: the exact amplitude-one
correction profile `W_ε = -curl_z(η(σ)θ(z)𝒜_ε)`. -/
def rescaledCorrectionProfile (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (D : CutoffData) : SpaceTimeField :=
  fun z => -curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotential v x₀ T ε (z.1, y)) z.2

/-! ## 1. The `def` bridge `W_ε = CorrectionProfile.profile` -/

def rescaledReference (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  fun z => v (T + ε ^ 2 * z.1, x₀ + ε • z.2)

/-- `03-torus.tex:264-272`, `Spec.lean:712-723`: the bracketed amplitude-one
force profile `H_ε = ∂ₜW − νΔW + ε(∇W·V) + ε²(∇v·W) + ε(W·∇)W`. -/
def rescaledForceProfile (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (D : CutoffData) : SpaceTimeField :=
  let W := rescaledCorrectionProfile v x₀ T ε D
  let V := rescaledReference v x₀ T ε
  fun z =>
    temporalDerivative W z.1 z.2 - ν • spatialLaplacian W z.1 z.2 +
      ε • spatialDerivative W z.1 z.2 (V z) +
      (ε ^ 2) • spatialDerivative v
        (T + ε ^ 2 * z.1) (x₀ + ε • z.2) (W z) +
      ε • advection W z.1 z.2

def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2


def torusSpaceTimeLift (f : SpaceTimeField) : ℝ × PeriodicTorus → Space :=
  fun z => torusLift (fun x => f (z.1, x)) z.2

/-- `03-torus.tex:225`: spatial projection of the lifted support. -/
def torusSpatialSupport (f : SpaceTimeField) : Set PeriodicTorus :=
  Prod.snd '' tsupport (torusSpaceTimeLift f)

/-- `03-torus.tex:225`: temporal projection of the same lifted support. -/
def torusTemporalSupport (f : SpaceTimeField) : Set ℝ :=
  Prod.fst '' tsupport (torusSpaceTimeLift f)

structure CorrectionAPI (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData) : Type where
  /-- `03-torus.tex:176-217`: a T16 local-potential witness for the same
  reference, enlarged set, chart center, radius, time, margin, and cutoffs.
  Non-vacuity: this field carries the concrete potential and correction family
  used by every later field. -/
  potential : LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D
  /-- `03-torus.tex:22-98`: the T13 localization witness used for the fractional
  torus estimate.  Non-vacuity: its six concrete integral identities and
  endpoint transfers are available to the `H^s` consumer. -/
  localization : LocalizationAPI
  /-- `03-torus.tex:219-223`: positive viscosity.  Non-vacuity: excludes the
  degenerate zero-viscosity force formula. -/
  viscosity_pos : 0 < ν
  /-- `03-torus.tex:102-105`: positive chart radius.  Non-vacuity: the local
  ball used by the potential is nonempty. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:102-105`: `ball x₀ r ⊆ ball chartCenter chartRadius`.
  Non-vacuity: this is the chart inclusion consumed by T13's localization
  witness together with `place.chartBall_in_cube`. -/
  ball_in_chart : Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius
  /-- `03-torus.tex:103,242`: the T16 threshold is within the shared placement
  threshold.  Non-vacuity: all scale clauses use one common interval. -/
  eps_le_placement : D.ε₀ ≤ place.ε₀
  /-- `03-torus.tex:2-4`: the reference velocity is unit-periodic.
  Non-vacuity: this is the actual periodicity hypothesis used by every chart
  and torus norm. -/
  reference_periodic : IsPeriodicOn univ v

  /-- `03-torus.tex:256-260`: the correction profile is smooth on the fixed
  cylinder.  Non-vacuity: this is regularity of the displayed `W_ε`, not an
  unspecified profile. -/
  correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile v place.x₀ place.T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:256-260`: `W_ε` is supported in the fixed cylinder.
  Non-vacuity: the topological support of the concrete profile is bounded. -/
  correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile v place.x₀ place.T ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:254-260`: data constants for every full derivative order.
  Non-vacuity: the constants are selected before `ε`. -/
  correctionProfileConst : ℕ → ℝ
  /-- `03-torus.tex:254-260`: nonnegative profile constants.  Non-vacuity:
  excludes a negative real witness collapsed by `ENNReal.ofReal`. -/
  correctionProfileConst_nonneg : ∀ k, 0 ≤ correctionProfileConst k
  /-- `03-torus.tex:254-260`: uniform derivative bounds for `W_ε`.
  Non-vacuity: each fixed order has one bound on every admissible scale. -/
  correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v place.x₀ place.T ε D) z‖ ≤
        correctionProfileConst k
  /-- `03-torus.tex:262-273`: the force profile is smooth on the fixed
  cylinder.  Non-vacuity: this regularity applies to the displayed bracket. -/
  force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν v place.x₀ place.T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:262-273`: the bracketed force profile is supported in the
  fixed cylinder.  Non-vacuity: no unbounded rescaled support is admitted. -/
  force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν v place.x₀ place.T ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:262-273`: data constants for force-profile derivatives.
  Non-vacuity: the constants are fixed before `ε`. -/
  forceProfileConst : ℕ → ℝ
  /-- `03-torus.tex:262-273`: nonnegative force-profile constants.
  Non-vacuity: excludes a negative witness collapsed by `ENNReal.ofReal`. -/
  forceProfileConst_nonneg : ∀ k, 0 ≤ forceProfileConst k
  /-- `03-torus.tex:262-273`: uniform derivative bounds for the bracket.
  Non-vacuity: every fixed order is controlled throughout the cylinder. -/
  force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v place.x₀ place.T ε D) z‖ ≤
        forceProfileConst k
  /-- `03-torus.tex:256-259`: physical correction equals `W_ε` in the chart.
  Non-vacuity: this links the bound-bearing family `D.correction` to the
  profile family rather than leaving them independent. -/
  correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint place.x₀ place.T ε z) =
        rescaledCorrectionProfile v place.x₀ place.T ε D z
  /-- `03-torus.tex:264-272`: physical force equals `ε⁻²` times the bracket.
  Non-vacuity: this is the exact affine rescaling identity with all three
  interior powers present in the profile definition. -/
  force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint place.x₀ place.T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v place.x₀ place.T ε D z
  /-- `03-torus.tex:225`: global smoothness across `T` and zero extension.
  Non-vacuity: this is a regularity property of the concrete `H_ε`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν v D ε)
  /-- `03-torus.tex:225,235-240`: unit periodicity of `H_ε`.
  Non-vacuity: it makes the torus lift represent the physical force. -/
  force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν v D ε)
  /-- `03-torus.tex:225`: force support on the torus lift uses the manuscript's
  open spatial ball.  Non-vacuity: no closed-ball weakening is allowed. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν v D ε) ⊆
      Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.ball place.x₀ (ε * D.θRadius))
  /-- `03-torus.tex:225`: real spatial-volume constant.  Non-vacuity:
  nonnegativity below makes its `ENNReal.ofReal` bound meaningful. -/
  spatialVolumeConst : ℝ
  /-- `03-torus.tex:225`: spatial-volume constant is nonnegative.
  Non-vacuity: this rules out a negative constant erased by `ENNReal.ofReal`. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- `03-torus.tex:225`: one-copy torus spatial support has volume `O(ε³)`.
  Non-vacuity: the support is measured after the torus lift, not in periodic
  Euclidean space where it would have infinite volume. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- `03-torus.tex:225`: temporal projection has length at most `4ε²`.
  Non-vacuity: the same lifted support is used for both projections. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2)
  /-- `03-torus.tex:226-229`: derivative constants for `w_ε`.
  Non-vacuity: these are concrete data fixed before `ε`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- `03-torus.tex:226-229`: nonnegative correction derivative constants.
  Non-vacuity: each displayed rate has a nonnegative real coefficient. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `03-torus.tex:226-229`: arbitrary unit time/spatial directions give
  `C_{j,m} ε^{-2j-m}`.  Non-vacuity: the guard `(∀ i, ‖u i‖≤1)` makes
  the iterated Fréchet derivative a genuine directional derivative bound. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)
  /-- `03-torus.tex:229-232`: force derivative constants.
  Non-vacuity: these coefficients are selected before `ε`. -/
  forceDerivConst : ℕ → ℝ
  /-- `03-torus.tex:229-232`: nonnegative force derivative constants.
  Non-vacuity: no negative coefficient is hidden by `ENNReal.ofReal`. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `03-torus.tex:229-232`: spatial directional bound including `m=0`.
  Non-vacuity: the unit-direction guard makes the derivative tensor honest. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (ε⁻¹) ^ (2 + m)
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` slices of
  `w_ε`.  Non-vacuity: these guards make both Bochner integrals in
  `energyENormT` honest rather than junk-small. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction ε (t, x))) 2 periodicTorusMeasure
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` full-gradient
  slices.  Non-vacuity: this is the second honesty guard for `energyENormT`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction ε) t x)) 2
      periodicTorusMeasure
  /-- `03-torus.tex:234,242`: real energy constant fixed before `ε`.
  Non-vacuity: its nonnegative field prevents a collapsed negative witness. -/
  energyConst : ℝ
  /-- `03-torus.tex:234,242`: energy constant nonnegative.
  Non-vacuity: the real coefficient cannot collapse to zero through `ofReal`. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- `03-torus.tex:234-280`: `‖w_ε‖_{E_T}≤Cε^{3/2}` with T10's torus
  energy norm.  Non-vacuity: the two preceding `MemLp` fields make the
  ess-supremum and lower Bochner integral honest. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT place.T (D.correction ε) ≤
      ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:235-237`: every force slice has an honest Haar-`L^p`
  representative.  Non-vacuity: this is the slice guard for the mixed norm. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v D ε (t, x))) p
        periodicTorusMeasure
  /-- `03-torus.tex:235-237,242`: real mixed constants fixed before `ε`.
  Non-vacuity: nonnegativity below prevents `ENNReal.ofReal` collapse. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:235-237,242`: mixed constants are nonnegative.
  Non-vacuity: this applies on the exact `1≤p,q` range of the bound. -/
  mixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst p q
  /-- `03-torus.tex:235-237,281-282`: for `[Fact (1≤p)]` and `1≤q`,
  `‖H_ε‖_{L^q_tL^p_x}≤C_{p,q} ε^{alpha(p,q)+1}`.  The slice `MemLp`
  field above is the hygiene guard making each representing path honest. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (mixedConst p q * ε ^ (alphaT p q + 1))
  /-- `03-torus.tex:239-242`: real Sobolev constants fixed before `ε`.
  Non-vacuity: strict positivity below makes the displayed finite bound
  meaningful on the full `[0,1]` range. -/
  sobolevConst : ℝ → ℝ
  /-- `03-torus.tex:239-242`: `C_s>0` on `0≤s≤1`.
  Non-vacuity: strict positivity excludes a collapsed Sobolev coefficient. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s
  /-- `03-torus.tex:239-242`: an honest `L¹_tH^s_x` Fourier-data path.
  Non-vacuity: `MemLp` makes the Bochner infimum in `forceSobolevENormT` honest. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      MemForceSobolevT 1 s (correctionForce ν v D ε)
  /-- `03-torus.tex:239-242,284`: the `H^s` estimate, with its honest
  `MemForceSobolevT 1 s` guard and `0≤s≤1` quantifiers. -/
  force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))

def correctionStatement : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    ∃ D : CutoffData,
      LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (CorrectionAPI ν place v r δ D)

/-- The completed G4 hypothesis block; `correctionStatement` remains unchanged. -/
def correctionStatementAmended : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)


/-! The packet-indexed spelling is preserved token-for-token from the Spec.
Only already-registered dependencies are reused; placement is the specialization
of the raw record at the four packet projections. -/
namespace Packet
abbrev PlacementData {ν : ℝ} (P : PacketAPI ν) :=
  Correction3.PlacementData P.velocity P.pressure P.force P.carrier

/-- `03-torus.tex:245-260`: the fixed manuscript cylinder in rescaled
coordinates.  Its endpoints and radius are independent of `ε`. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) D.θRadius

/-- `03-torus.tex:256-259`: the correction chart based at `T`, not at
`T-ε²`; this is the chart used by both profile identities. -/
def correctionChartPoint {ν : ℝ} {P : PacketAPI ν}
    (place : PlacementData P) (ε : ℝ) (z : SpaceTime) : SpaceTime :=
  (place.T + ε ^ 2 * z.1, place.x₀ + ε • z.2)

/-- `03-torus.tex:245,262-263`: `V_ε(z,σ)=v(T+ε²σ,x₀+εz)`. -/
def rescaledReference {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) : SpaceTimeField :=
  fun z => v (place.T + ε ^ 2 * z.1, place.x₀ + ε • z.2)

/-- `03-torus.tex:247-253`: the amplitude-one radial-potential profile
`𝒜_ε(z,σ)=∫₀¹ρ v(T+ε²σ,x₀+ερz)×z dρ`. -/
def rescaledPotential {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) : SpaceTimeField :=
  fun z => ∫ ρ in (0 : ℝ)..1,
    ρ • cross
      (v (place.T + ε ^ 2 * z.1,
        place.x₀ + ε • (ρ • z.2))) z.2

/-- `03-torus.tex:256-259`: the exact amplitude-one correction profile
`W_ε=-curl_z(η(σ)θ(z)𝒜_ε)`. -/
def rescaledCorrectionProfile (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) (D : CutoffData) : SpaceTimeField :=
  fun z => -curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotential v place ε (z.1, y)) z.2

/-- `03-torus.tex:264-272`: the bracketed amplitude-one force profile. -/
def rescaledForceProfile (ν : ℝ) (v : SpaceTimeField) (place : PlacementData P)
    (ε : ℝ) (D : CutoffData) : SpaceTimeField :=
  let W := rescaledCorrectionProfile v place ε D
  let V := rescaledReference v place ε
  fun z =>
    temporalDerivative W z.1 z.2 - ν • spatialLaplacian W z.1 z.2 +
      ε • spatialDerivative W z.1 z.2 (V z) +
      (ε ^ 2) • spatialDerivative v
        (place.T + ε ^ 2 * z.1) (place.x₀ + ε • z.2) (W z) +
      ε • advection W z.1 z.2

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

/-- `03-torus.tex:225`: the torus-lifted spacetime field used to measure one
periodic copy of the force support. -/
def torusSpaceTimeLift (f : SpaceTimeField) : ℝ × PeriodicTorus → Space :=
  fun z => torusLift (fun x => f (z.1, x)) z.2

/-- `03-torus.tex:225`: spatial projection of the lifted support. -/
def torusSpatialSupport (f : SpaceTimeField) : Set PeriodicTorus :=
  Prod.snd '' tsupport (torusSpaceTimeLift f)

/-- `03-torus.tex:225`: temporal projection of the same lifted support. -/
def torusTemporalSupport (f : SpaceTimeField) : Set ℝ :=
  Prod.fst '' tsupport (torusSpaceTimeLift f)

/-- Reconciled Type-valued API for `lem:correction`,
`paper/sections/03-torus.tex:218-285`.  The placement packet is threaded only
so T15/T17/T18 share definitionally the same `T,x₀,K_*,B,ε₀`; no packet field
is used by the correction mathematics.  Every norm bound carries the guard
that makes its Bochner integrals honest. -/
structure CorrectionAPI (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData) : Type where
  /-- `03-torus.tex:176-217`: a T16 local-potential witness for the same
  reference, enlarged set, chart center, radius, time, margin, and cutoffs.
  Non-vacuity: this field carries the concrete potential and correction family
  used by every later field. -/
  potential : LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D
  /-- `03-torus.tex:22-98`: the T13 localization witness used for the fractional
  torus estimate.  Non-vacuity: its six concrete integral identities and
  endpoint transfers are available to the `H^s` consumer. -/
  localization : LocalizationAPI
  /-- `03-torus.tex:219-223`: positive viscosity.  Non-vacuity: excludes the
  degenerate zero-viscosity force formula. -/
  viscosity_pos : 0 < ν
  /-- `03-torus.tex:102-105`: positive chart radius.  Non-vacuity: the local
  ball used by the potential is nonempty. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:102-105`: `ball x₀ r ⊆ ball chartCenter chartRadius`.
  Non-vacuity: this is the chart inclusion consumed by T13's localization
  witness together with `place.chartBall_in_cube`. -/
  ball_in_chart : Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius
  /-- `03-torus.tex:103,242`: the T16 threshold is within the shared placement
  threshold.  Non-vacuity: all scale clauses use one common interval. -/
  eps_le_placement : D.ε₀ ≤ place.ε₀
  /-- `03-torus.tex:2-4`: the reference velocity is unit-periodic.
  Non-vacuity: this is the actual periodicity hypothesis used by every chart
  and torus norm. -/
  reference_periodic : IsPeriodicOn univ v

  /-- `03-torus.tex:256-260`: the correction profile is smooth on the fixed
  cylinder.  Non-vacuity: this is regularity of the displayed `W_ε`, not an
  unspecified profile. -/
  correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile v place ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:256-260`: `W_ε` is supported in the fixed cylinder.
  Non-vacuity: the topological support of the concrete profile is bounded. -/
  correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile v place ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:254-260`: data constants for every full derivative order.
  Non-vacuity: the constants are selected before `ε`. -/
  correctionProfileConst : ℕ → ℝ
  /-- `03-torus.tex:254-260`: nonnegative profile constants.  Non-vacuity:
  excludes a negative real witness collapsed by `ENNReal.ofReal`. -/
  correctionProfileConst_nonneg : ∀ k, 0 ≤ correctionProfileConst k
  /-- `03-torus.tex:254-260`: uniform derivative bounds for `W_ε`.
  Non-vacuity: each fixed order has one bound on every admissible scale. -/
  correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v place ε D) z‖ ≤
        correctionProfileConst k
  /-- `03-torus.tex:262-273`: the force profile is smooth on the fixed
  cylinder.  Non-vacuity: this regularity applies to the displayed bracket. -/
  force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν v place ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:262-273`: the bracketed force profile is supported in the
  fixed cylinder.  Non-vacuity: no unbounded rescaled support is admitted. -/
  force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν v place ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:262-273`: data constants for force-profile derivatives.
  Non-vacuity: the constants are fixed before `ε`. -/
  forceProfileConst : ℕ → ℝ
  /-- `03-torus.tex:262-273`: nonnegative force-profile constants.
  Non-vacuity: excludes a negative witness collapsed by `ENNReal.ofReal`. -/
  forceProfileConst_nonneg : ∀ k, 0 ≤ forceProfileConst k
  /-- `03-torus.tex:262-273`: uniform derivative bounds for the bracket.
  Non-vacuity: every fixed order is controlled throughout the cylinder. -/
  force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v place ε D) z‖ ≤
        forceProfileConst k
  /-- `03-torus.tex:256-259`: physical correction equals `W_ε` in the chart.
  Non-vacuity: this links the bound-bearing family `D.correction` to the
  profile family rather than leaving them independent. -/
  correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint place ε z) =
        rescaledCorrectionProfile v place ε D z
  /-- `03-torus.tex:264-272`: physical force equals `ε⁻²` times the bracket.
  Non-vacuity: this is the exact affine rescaling identity with all three
  interior powers present in the profile definition. -/
  force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint place ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v place ε D z
  /-- `03-torus.tex:225`: global smoothness across `T` and zero extension.
  Non-vacuity: this is a regularity property of the concrete `H_ε`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν v D ε)
  /-- `03-torus.tex:225,235-240`: unit periodicity of `H_ε`.
  Non-vacuity: it makes the torus lift represent the physical force. -/
  force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν v D ε)
  /-- `03-torus.tex:225`: force support on the torus lift uses the manuscript's
  open spatial ball.  Non-vacuity: no closed-ball weakening is allowed. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν v D ε) ⊆
      Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.ball place.x₀ (ε * D.θRadius))
  /-- `03-torus.tex:225`: real spatial-volume constant.  Non-vacuity:
  nonnegativity below makes its `ENNReal.ofReal` bound meaningful. -/
  spatialVolumeConst : ℝ
  /-- `03-torus.tex:225`: spatial-volume constant is nonnegative.
  Non-vacuity: this rules out a negative constant erased by `ENNReal.ofReal`. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- `03-torus.tex:225`: one-copy torus spatial support has volume `O(ε³)`.
  Non-vacuity: the support is measured after the torus lift, not in periodic
  Euclidean space where it would have infinite volume. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- `03-torus.tex:225`: temporal projection has length at most `4ε²`.
  Non-vacuity: the same lifted support is used for both projections. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2)
  /-- `03-torus.tex:226-229`: derivative constants for `w_ε`.
  Non-vacuity: these are concrete data fixed before the scale quantifier. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- `03-torus.tex:226-229`: nonnegative correction derivative constants.
  Non-vacuity: each displayed rate has a nonnegative real coefficient. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `03-torus.tex:226-229`: arbitrary unit time/spatial directions give
  `C_{j,m} ε^{-2j-m}`.  Non-vacuity: the guard `(∀ i, ‖u i‖≤1)` makes the
  iterated Fréchet derivative a genuine directional derivative bound. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)
  /-- `03-torus.tex:229-232`: force derivative constants.
  Non-vacuity: these coefficients are selected before `ε`. -/
  forceDerivConst : ℕ → ℝ
  /-- `03-torus.tex:229-232`: nonnegative force derivative constants.
  Non-vacuity: no negative coefficient is hidden by `ENNReal.ofReal`. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `03-torus.tex:229-232`: spatial directional bound including `m=0`.
  Non-vacuity: the unit-direction guard makes the derivative tensor honest. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (ε⁻¹) ^ (2 + m)
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` slices of
  `w_ε`.  Non-vacuity: these guards make both Bochner integrals in `energyENormT`
  honest rather than junk-small. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction ε (t, x))) 2 periodicTorusMeasure
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` full-gradient
  slices.  Non-vacuity: this is the second honesty guard for `energyENormT`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction ε) t x)) 2
      periodicTorusMeasure
  /-- `03-torus.tex:234,242`: real energy constant fixed before `ε`.
  Non-vacuity: its nonnegative field prevents a collapsed negative witness. -/
  energyConst : ℝ
  /-- `03-torus.tex:234,242`: energy constant nonnegative.
  Non-vacuity: the real coefficient cannot collapse to zero through `ofReal`. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- `03-torus.tex:234-280`: `‖w_ε‖_{E_T}≤Cε^{3/2}` with T10's torus
  energy norm.  Non-vacuity: the two preceding `MemLp` fields make the
  ess-supremum and lower Bochner integral honest. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT place.T (D.correction ε) ≤
      ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:235-237`: every force slice has an honest Haar-`L^p`
  representative.  Non-vacuity: this is the slice guard for the mixed norm. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v D ε (t, x))) p
        periodicTorusMeasure
  /-- `03-torus.tex:235-237,242`: real mixed constants fixed before `ε`.
  Non-vacuity: nonnegativity below prevents `ENNReal.ofReal` collapse. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:235-237,242`: mixed constants are nonnegative.
  Non-vacuity: this applies on the exact `1≤p,q` range of the bound. -/
  mixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst p q
  /-- `03-torus.tex:235-237,281-282`: for `[Fact (1≤p)]` and `1≤q`,
  `‖H_ε‖_{L^q_tL^p_x}≤C_{p,q} ε^{alpha(p,q)+1}`.  The slice `MemLp`
  field above is the hygiene guard making each representing path honest. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (mixedConst p q * ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1))
  /-- `03-torus.tex:239-242`: real Sobolev constants fixed before `ε`.
  Non-vacuity: strict positivity below makes the displayed finite bound
  meaningful on the full `[0,1]` range. -/
  sobolevConst : ℝ → ℝ
  /-- `03-torus.tex:239-242`: `C_s>0` on `0≤s≤1`.
  Non-vacuity: strict positivity excludes a collapsed Sobolev coefficient. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s
  /-- `03-torus.tex:239-242`: an honest `L¹_tH^s_x` Fourier-data path.
  Non-vacuity: `MemLp` makes the Bochner infimum in `forceSobolevENormT` honest. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      MemForceSobolevT 1 s (correctionForce ν v D ε)
  /-- `03-torus.tex:239-242,284`: the `H^s` estimate, with its honest
  `MemForceSobolevT 1 s` guard and `0≤s≤1` quantifiers. -/
  force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))

/-- `Contracts.V1.Correction.lean:160`: arithmetic drift check for the
registered exponent.  It is intentionally not a record field. -/
example (p q : ℝ≥0∞) :
    -2 + 3 / p.toReal + 2 / q.toReal =
      BlowupDensity.Contracts.V1.alpha p q + 1 := by
  simp [BlowupDensity.Contracts.V1.alpha]
  ring

/-- The local mixed norm is definitionally the copied T15 vocabulary. -/
example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    mixedLebesgueENormT q p f = BlowupDensity.Contracts.V1.Correction3.mixedLebesgueENormT q p f := rfl

/-- The copied T15 exponent is definitionally the registered exponent. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.Contracts.V1.Correction3.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-- The existential closure matches the registered statement style without
adding a mathematical field. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P)
    (v : SpaceTimeField) (r δ : ℝ),
    ∃ D : CutoffData,
      LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (CorrectionAPI ν place v r δ D)

end Packet
end BlowupDensity.Contracts.V1.Correction3
