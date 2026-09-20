import Contracts.V1.TorusData
import Contracts.V1.Correction
import Contracts.V2.Correction
import Contracts.V1.Scaling
import Contracts.V1.HomogeneousNorm

/-!
# T17 reconciled specification: bounds for the background correction

Statement-only reconciliation of `lem:correction`, `paper/sections/03-torus.tex:218-285`,
following `research/T17/RECONCILIATION.md`.  The copied vocabulary below is
limited to still-unregistered declarations; no field is a placeholder.
-/

noncomputable section

/- copied verbatim from research/T10/Spec.lean:255-268,393-411;
   registered `Contracts.V1.TorusData` supplies the torus vocabulary. -/
namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators

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

/-- `01-introduction.tex:143-150` eq:Enorm: the periodic
`L∞(0,T;L²(T³))` norm on the open time interval. -/
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

end BlowupDensity.T10.Draft

/- end verbatim T10 copy -/

/- copied verbatim from research/T13/Spec.lean:168-312; dependencies resolve
   through registered `Contracts.V1.TorusData`. -/
namespace BlowupDensity.T13.Spec

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:23,53,79-80`: the fixed closed unit fundamental cube
`[0,1]³`.  Its interior is the coordinate chart in which the support ball must
lie.  This is the fixed cube underlying T10's `(0,1]³` torus representative. -/
def fundamentalCube : Set Space :=
  {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

/-- `03-torus.tex:23`: the zero extension is supported in the open coordinate
ball with center `c` and radius `r`, in the topological-support sense. -/
def SupportedInBall (c : Space) (r : ℝ) (f : SpatialField) : Prop :=
  tsupport f ⊆ Metric.ball c r

/-- `03-torus.tex:53-56`: embed a lattice frequency as its Euclidean vector. -/
def latticeVector (n : PeriodicFrequency) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i ↦ (n i : ℝ))

/-- `03-torus.tex:23`: the actual spatial lattice periodization of the
whole-space zero extension; it is a function, not an existential relation. -/
def periodize (f : SpatialField) : SpatialField :=
  fun x ↦ ∑' n : PeriodicFrequency, f (x - latticeVector n)

/-! ## Fractional kernels and difference integrals -/

/-- `03-torus.tex:35,43-48,54-56`: the extended nonnegative singular power
`|h|^{-3-2s}`.  The singular value at `h=0` is retained as `⊤`. -/
def fractionalRadialKernel (s : ℝ) (h : Space) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖h‖) ^ (-(3 + 2 * s))

/-- `03-torus.tex:35-39`: the paper's single explicit constant
`c_s = ∫_ℝ³ |exp(i h₁)-1|² |h|^{-3-2s} dh`, with no hidden `2π` factor. -/
def cFrac (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Space,
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h

/-- `03-torus.tex:53-57`: the periodized fractional kernel
`K_s(h)=∑_{n∈ℤ³}|h+n|^{-3-2s}` on the fixed unit lattice. -/
def periodicKernel (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : PeriodicFrequency, fractionalRadialKernel s (h + latticeVector n)

/-- `03-torus.tex:40-48`: the vector-valued whole-space Gagliardo integral
`I_ℝ`, with the Euclidean norm summing the three component squares. -/
def IReal (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ h : Space, ∫⁻ x : Space,
    ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2) * fractionalRadialKernel s h

/-- `03-torus.tex:53-67`: the vector-valued torus Gagliardo integral over the
fixed fundamental cube, using the literal representative difference `x-y`. -/
def ITorus (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
    ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y)

/-! ## Endpoint quantities -/

/-- `03-torus.tex:29,97-98`: the physical `L²` gradient norm, with the
Hilbert--Schmidt convention (sum over all three spatial derivatives). -/
def gradientENorm (f : SpatialField) (μ : Measure Space) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x (coordinateVector i)‖ ^ 2) ∂μ) ^
    ((2 : ℝ)⁻¹)

/-! ## Reconciled six-field API -/

/-- Statement-only API for `lem:localization` and the Fourier/Gagliardo
identifications used by its proof (`03-torus.tex:22-98`).  The range is always
`0 < s < 1`; the two endpoints are stated separately. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:35-39`: the defined constant `c_s` is strictly positive
  and finite for `0 < s < 1`.

  Non-vacuity: this constrains the concrete integral `cFrac s`, rather than
  allowing an arbitrary positive constant to be chosen. -/
  constant_pos_finite :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤

  /-- `03-torus.tex:40-51`: the whole-space Gagliardo integral of every smooth
  compactly supported real vector field equals `c_s` times the square of the
  registered `dotHomogeneousENorm`.

  Non-vacuity: compact smooth fields exist (in particular the zero field), and
  the conclusion both proves finiteness and fixes the exact norm value. -/
  wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)

  /-- `03-torus.tex:53-72`: the periodic Gagliardo integral of every smooth
  periodic vector field equals the same `c_s` times T10's homogeneous norm of
  its explicitly mean-zero part; the T10 weight retains the exact `2π` factor.

  Non-vacuity: the zero field is smooth and periodic, while the identity also
  applies to nonconstant trigonometric modes and asserts a finite integral. -/
  torus_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ)

  /-- `03-torus.tex:22-28,73-96`, equation `eq:localization`: for every fixed
  positive-radius ball strictly inside the fixed cube, one positive finite real
  constant is chosen before every smooth zero extension supported in that ball.
  The torus and whole-space terms use T10's `periodicSobolevENorm`, the
  registered `eLpNorm f 2 volume`, and the registered homogeneous norm.

  Non-vacuity: positive-radius balls with closure inside `(0,1)³` exist, and
  the quantifier order makes one `C_{s,B}` control every smaller support. -/
  localization :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)

  /-- `03-torus.tex:29,96-98`: at `s=0`, integration over the single copy of
  the support gives equality of the physical `L²` norms.

  Non-vacuity: the equality compares the concrete periodization on the fixed
  cube with the whole-space field, under the same nonempty ball condition as
  the fractional statement. -/
  endpoint_zero :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume

  /-- `03-torus.tex:29,96-98`: at `s=1`, integration over the single copy of
  the support gives equality of the corresponding physical `L²` gradient
  norms, without identifying them with the full inhomogeneous `H¹` norm.

  Non-vacuity: this is an equality of explicit Hilbert--Schmidt gradient norms
  for every supported smooth field, not a restatement of `endpoint_zero`. -/
  endpoint_one :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume

end BlowupDensity.T13.Spec

/- end verbatim T13 copy -/

/- copied verbatim from research/T16/Spec.lean:53-336; only the T16 helpers,
   `CutoffData`, and `LocalPotentialAPI` are retained. -/
namespace BlowupDensity.T16.Draft

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open Set MeasureTheory
open scoped ContDiff Topology

/-! ## Periodic physical-layer helpers -/

/-- The Euclidean lattice vector associated with a torus frequency;
`paper/sections/03-torus.tex:188,212`.

Non-vacuity: this is the actual integer translation in the physical
`R³` lift, not an abstract quotient label. -/
def latticeVector (k : PeriodicFrequency) : Space :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- The lift to `R³` of a spatial set on the unit torus;
`paper/sections/03-torus.tex:188,212`.

Non-vacuity: membership supplies a concrete lattice translate whose
representative lies in `S`. -/
def periodicSet (S : Set Space) : Set Space :=
  {x | ∃ k : PeriodicFrequency, x - latticeVector k ∈ S}

/-- The periodized rescaled packet used by `eq:bgzero`;
`paper/sections/03-torus.tex:112-120,214-215`.

Non-vacuity: this is the locally finite integer-translate formula consumed
later for T14's compactly supported packet, not an unspecified packet family. -/
def periodicScaledPacket (U : SpaceTimeField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z => ∑' k : PeriodicFrequency,
    scaledPacket U x₀ T ε (z.1, z.2 - latticeVector k)

/-- The corrected background `v + w_ε` in `eq:bgzero`;
`paper/sections/03-torus.tex:190-192`.

Non-vacuity: evaluation is the pointwise sum of the given reference and the
chosen correction at the specified scale. -/
def correctedBackground (v : SpaceTimeField) (w : ℝ → SpaceTimeField) (ε : ℝ) :
    SpaceTimeField :=
  fun z => v z + w ε z

/-! ## Construction data and the reconciled API -/

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

/-- The reconciled clauses of Lemma `lem:potential`;
`paper/sections/03-torus.tex:167-215`.

All witnesses are stored in `D` before `ε` is quantified.  The local curl
formula is stated in the selected Euclidean chart; the global correction is a
unit-periodic physical lift and therefore has translated rather than compact
support in all of `R³`. -/
structure LocalPotentialAPI (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData) : Prop where
  /-- The spatial Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:167-174,181`.

  Non-vacuity: this is global `C∞` regularity of the concrete function
  `D.θ`. -/
  theta_smooth : ContDiff ℝ ∞ D.θ
  /-- The spatial Urysohn cutoff has compact support;
  `paper/sections/03-torus.tex:167-174,181`.

  Non-vacuity: this constrains the topological support of `D.θ`, rather than
  merely asserting existence of some compact set. -/
  theta_compactSupport : HasCompactSupport D.θ
  /-- The spatial cutoff takes values in `[0,1]`;
  `paper/sections/03-torus.tex:171-172`.

  Non-vacuity: the closed-interval membership is required pointwise for every
  spatial input. -/
  theta_range : ∀ x, D.θ x ∈ Icc (0 : ℝ) 1
  /-- The plateau is an open neighborhood;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: openness is imposed on the actual stored set `D.plateau`. -/
  plateau_open : IsOpen D.plateau
  /-- The prescribed enlarged compact set `K_*` lies in the plateau;
  `paper/sections/03-torus.tex:101-102,168-172,181`.

  Non-vacuity: every point of the caller-supplied `K` is forced into the
  same plateau used by the cancellation field. -/
  prescribed_subset_plateau : K ⊆ D.plateau
  /-- The spatial cutoff is identically one on its plateau;
  `paper/sections/03-torus.tex:172,181`.

  Non-vacuity: this is a pointwise equality on the open set that contains
  `K`. -/
  theta_one : EqOn D.θ (fun _ => 1) D.plateau
  /-- The fixed cutoff-support radius is positive;
  `paper/sections/03-torus.tex:168-172,212`.

  Non-vacuity: strict positivity rules out a degenerate radius witness. -/
  theta_radius_pos : 0 < D.θRadius
  /-- The spatial cutoff support lies in the fixed reference ball;
  `paper/sections/03-torus.tex:168-172,181,212`.

  Non-vacuity: this bounds the actual `tsupport D.θ` by the radius later used
  in `eps_space`. -/
  theta_support : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius
  /-- The temporal Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:173-174,182`.

  Non-vacuity: this is global `C∞` regularity of the concrete function
  `D.η`. -/
  eta_smooth : ContDiff ℝ ∞ D.η
  /-- The temporal cutoff has compact support;
  `paper/sections/03-torus.tex:173-174,182`.

  Non-vacuity: this constrains the actual topological support of `D.η`. -/
  eta_compactSupport : HasCompactSupport D.η
  /-- The temporal cutoff takes values in `[0,1]`;
  `paper/sections/03-torus.tex:171-174`.

  Non-vacuity: the closed-interval membership is required for every time. -/
  eta_range : ∀ t, D.η t ∈ Icc (0 : ℝ) 1
  /-- The temporal cutoff equals one throughout `[-1,1]`;
  `paper/sections/03-torus.tex:182,214-215`.

  Non-vacuity: the equality is pointwise on the entire closed active
  interval. -/
  eta_one : EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- The temporal cutoff is supported strictly inside `(-2,2)`;
  `paper/sections/03-torus.tex:182,188-189`.

  Non-vacuity: this is an inclusion for the actual `tsupport D.η`, with open
  endpoints as in the manuscript. -/
  eta_support : tsupport D.η ⊆ Ioo (-2 : ℝ) 2
  /-- The common small-scale threshold is positive;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: strict positivity ensures that admissible scales exist. -/
  eps_pos : 0 < D.ε₀
  /-- Every admissible time window remains inside the positive regular slab;
  `paper/sections/03-torus.tex:103-106,188,212`.

  Non-vacuity: the strict inequality holds for each concrete
  `ε ∈ (0,D.ε₀]`. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
  /-- Every admissible scaled cutoff lies strictly inside the coordinate ball;
  `paper/sections/03-torus.tex:103-105,188,212`.

  Non-vacuity: the same threshold controls the concrete product
  `ε * D.θRadius` relative to `r`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
  /-- The radial potential is smooth on the local spacetime slab;
  `paper/sections/03-torus.tex:177-181`.

  Non-vacuity: regularity is asserted for the stored potential on the actual
  open time-ball product. -/
  potential_smooth : ContDiffOn ℝ ∞ D.potential
    (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r)
  /-- The radial integral formula `eq:potential`;
  `paper/sections/03-torus.tex:177-180`.

  Non-vacuity: this fixes `D.potential` pointwise to the displayed integral,
  including the center, cross product, and integration interval. -/
  potential_formula : ∀ t x, D.potential (t, x) =
    ∫ ρ in (0 : ℝ)..1,
      ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- The spatial curl of the radial potential is the reference velocity;
  `paper/sections/03-torus.tex:181,196-210`.

  Non-vacuity: this is pointwise equality of concrete vector fields throughout
  the local regularity slab. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    curl (fun y => D.potential (t, y)) x = v (t, x)
  /-- The chart formula `w_ε=-curl(η_ε θ_ε A)` from `eq:cutoff`;
  `paper/sections/03-torus.tex:183-188,212`.

  Non-vacuity: for every admissible scale, this identifies the stored
  correction pointwise on the coordinate ball with the registered cutoff and
  curl expression. -/
  correction_formula : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    ∀ x ∈ Metric.ball x₀ r,
      D.correction ε (t, x) =
        -curl (fun y =>
          (scaledTemporalCutoff D.η T ε t *
            scaledSpatialCutoff D.θ x₀ ε y) • D.potential (t, y)) x
  /-- The zero-extended, periodized correction is globally smooth;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: global `C∞` regularity is required of the same concrete
  correction family used by all later fields. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (D.correction ε)
  /-- The physical lift of the correction is unit-periodic in space;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: T10's `IsPeriodicOn` requires equality under every coordinate
  unit shift, at every real time and spatial point. -/
  correction_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (D.correction ε)
  /-- The correction is divergence free because it is a spatial curl;
  `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: the registered physical divergence vanishes pointwise for every
  time and position. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
    spatialDivergence (D.correction ε) t x = 0
  /-- The correction is supported in the prescribed temporal window;
  `paper/sections/03-torus.tex:188-189,212`.

  Non-vacuity: the inclusion forces the full spacetime support to vanish
  outside `(T-2ε²,T+2ε²)`; spatial localization is imposed separately below. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (D.correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)
  /-- Each spatial slice is supported in the periodic lift of the coordinate
  ball; `paper/sections/03-torus.tex:188,212`.

  Non-vacuity: this rules out correction support outside all integer
  translates of the concrete ball `Metric.ball x₀ r`. -/
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    tsupport (fun x => D.correction ε (t, x)) ⊆
      periodicSet (Metric.ball x₀ r)
  /-- `eq:bgzero` on the packet's active interval;
  `paper/sections/03-torus.tex:190-193,214-215`.

  Non-vacuity: for every admissible scale and active time, this supplies an
  actual open neighborhood containing the periodized packet support on which
  the concrete corrected background vanishes pointwise. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, correctedBackground v D.correction ε (t, x) = 0

/-- Exact construction quantifiers for Lemma `lem:potential`;
`paper/sections/03-torus.tex:101-105,163-188,212-215`.

The reference is assumed only periodic and locally smooth/divergence-free.
The packet input contributes only its compact source-time spatial support.
Every cutoff, potential, threshold, and correction witness is chosen before
the scale quantified inside `LocalPotentialAPI`. -/
def localPotentialStatement : Prop :=
  ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
    0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
    IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
    ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D

end BlowupDensity.T16.Draft

/- end verbatim T16 copy -/

/- copied verbatim from research/T15/Spec.lean:510-653; only mixed-norm
   vocabulary and `PlacementData` are retained. -/
namespace BlowupDensity.T15.Spec

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Honest mixed, Sobolev, and energy carriers -/

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

/-- The torus exponent is definitionally the registered `I03.scaling`
exponent, `03-torus.tex:130-131`. -/
example (p q : ℝ≥0∞) :
    alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-! ## Placement data fixed before every scale -/

/-- The choices and smallness conditions made at `03-torus.tex:101-107`.
`Kstar` contains both spatial packet supports.  Its scaled translate lies in a
fixed coordinate ball whose closure is inside the fundamental cube; this is
the hypothesis that makes the lattice sum a single copy on that cube. -/
structure PlacementData {ν : ℝ} (P : PacketAPI ν) where
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
  Non-vacuity: together with `chartBall_in_cube`, this is precisely the
  support-versus-scale condition used by the single-copy conclusions. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

end BlowupDensity.T15.Spec
/- end verbatim T15 copy -/

namespace BlowupDensity.T17.Spec

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.T10.Draft
open BlowupDensity.T13.Spec
open BlowupDensity.T15.Spec
open BlowupDensity.T16.Draft
open scoped ContDiff ENNReal Topology BigOperators

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
    mixedLebesgueENormT q p f = BlowupDensity.T15.Spec.mixedLebesgueENormT q p f := rfl

/-- The copied T15 exponent is definitionally the registered exponent. -/
example (p q : ℝ≥0∞) :
    BlowupDensity.T15.Spec.alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

/-- The existential closure matches the registered statement style without
adding a mathematical field. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) {P : PacketAPI ν} (place : PlacementData P)
    (v : SpaceTimeField) (r δ : ℝ),
    ∃ D : CutoffData,
      LocalPotentialAPI v P.velocity place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (CorrectionAPI ν place v r δ D)

end BlowupDensity.T17.Spec
