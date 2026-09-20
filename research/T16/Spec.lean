import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti
import Contracts.V1.Correction

/-!
# T16 reconciled specification: a local divergence-free cutoff on the three-torus

This statement-only file reconciles the two blind drafts for Lemma
`lem:potential` (`paper/sections/03-torus.tex:176-216`).  It follows Draft
B's data/API packaging and field order, uses Draft A's precise manuscript
citations, and replaces the drafts' provisional periodicity predicate with the
reconciled T10 vocabulary.

Research files are not importable Lean modules.  Until `T01.torus_data` is
registered, the two T10 declarations actually used here are therefore copied
verbatim below in their original namespace.  All other field types and
Euclidean operators come from the registered Section 4 contracts.
-/

noncomputable section

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

-- copied verbatim from research/T10/Spec.lean:46-48,66-70; must stay identical until T01.torus_data is registered

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the frequency lattice of the unit
three-torus. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `02-preliminaries.tex:28`: spatial periodicity on a specified set of times,
with time as the first spacetime coordinate. -/
def IsPeriodicOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t ∈ I, ∀ x : Space, ∀ i : Fin 3,
    z (t, x + coordinateVector i) = z (t, x)

end BlowupDensity.T10.Draft

namespace BlowupDensity.T16.Spec

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
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

end BlowupDensity.T16.Spec
