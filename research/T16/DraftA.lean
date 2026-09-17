import Contracts.V1.Correction
import NSFormalization.Paper1.TorusCube

/-!
# T16 draft A: a local divergence-free cutoff on the three-torus

This is an independent statement draft for Lemma `lem:potential`.  The physical
layer is a smooth unit-periodic field on `R^3`; the provisional Fourier layer is
the weighted `l^2(Z^3)` representation selected in
`collaboration/SECTION3_PLAN.md` section 1.

The definitions in section 1 are local copies for this draft only.  They need
registration and alignment with T10 before any contract is accepted.  The
Euclidean differential vocabulary in section 2 is reused from the registered
Section 4 I02 contract so that coincident objects have literally the same
meaning and names.
-/

noncomputable section

namespace BlowupDensity.Research.T16.DraftA

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

abbrev Space := BlowupDensity.Contracts.V1.Space
abbrev SpaceTime := BlowupDensity.Contracts.V1.SpaceTime
abbrev SpatialField := Space → Space
abbrev VelocityField := BlowupDensity.Contracts.V1.VelocityField
abbrev PeriodicFrequency := Fin 3 → ℤ

/-! ## 1. Provisional T10 data vocabulary

Every declaration in this section is **NEEDS REGISTRATION / TO BE ALIGNED WITH
T10**.  It is included to make the representation choice explicit; T16 itself
uses only the physical periodic layer below.
-/

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The scalar coefficient
carrier `l^2(Z^3)` for the unit torus.  The Fourier convention is the one in
`paper/sections/01-introduction.tex:83-90`. -/
abbrev PeriodicScalarDatum := lp (fun _ : PeriodicFrequency => ℂ) 2

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The Euclidean three-vector
product of three scalar coefficient carriers.  Squared component norms are
summed, as required by `paper/sections/01-introduction.tex:103`. -/
abbrev PeriodicVectorDatum := PiLp 2 (fun _ : Fin 3 => PeriodicScalarDatum)

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The lattice quantity
`|k|^2` used by the torus weights in
`paper/sections/01-introduction.tex:83-84`. -/
def periodicFrequencySq (k : PeriodicFrequency) : ℝ :=
  ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The coefficient multiplier
`(1 + 4 pi^2 |k|^2)^(s/2)` whose square gives the inhomogeneous Sobolev weight
of `paper/sections/01-introduction.tex:83-84,96-97`. -/
def periodicSobolevWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  (1 + 4 * Real.pi ^ 2 * periodicFrequencySq k) ^ (s / 2)

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The coefficient multiplier
`|2 pi k|^s` for the homogeneous norm of a mean-zero periodic field.  The zero
mode is explicitly omitted, exactly as in
`paper/sections/01-introduction.tex:105-108`. -/
def periodicHomogeneousWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0
  else (2 * Real.pi * Real.sqrt (periodicFrequencySq k)) ^ s

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The `i`-th component's
unit-torus Fourier coefficient, normalized as
`paper/sections/01-introduction.tex:88-90`. -/
def periodicVectorFourierCoeff (z : SpatialField) (i : Fin 3)
    (k : PeriodicFrequency) : ℂ :=
  NSFormalization.Paper1.periodicFourierCoeff (fun x => (z x i : ℂ)) k

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  `A` is the weighted
inhomogeneous coefficient datum of the physical periodic field `z`; compare
the datum style of `verification/Contracts/V1/Data.lean:160-190` with the
torus formula in `paper/sections/01-introduction.tex:83-103`. -/
def IsPeriodicSobolevDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    A i k = (periodicSobolevWeight s k : ℂ) * periodicVectorFourierCoeff z i k

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The totalized
`H^s(T^3)` norm of a physical field, using an infimum over genuine weighted
`l^2` data as in `verification/Contracts/V1/Data.lean:177-190`; the intended
torus norm is `paper/sections/01-introduction.tex:80-103`. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicSobolevDatum s z A}, ‖A.1‖ₑ

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  Mean zero means precisely
that every component's `k = 0` Fourier coefficient vanishes, as stipulated in
`paper/sections/01-introduction.tex:105-108`. -/
def IsPeriodicMeanZero (z : SpatialField) : Prop :=
  ∀ i : Fin 3, periodicVectorFourierCoeff z i 0 = 0

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The spatial mean over one
unit fundamental cube, used in the decomposition `v = u - m` at
`paper/sections/03-torus.tex:395-407`. -/
def periodicMean (z : SpatialField) : Space :=
  NavierStokes.PeriodicIntegration.cubeIntegral z

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The mean-zero component
`z - mean(z)` from `paper/sections/03-torus.tex:395-407`. -/
def periodicMeanZeroPart (z : SpatialField) : SpatialField :=
  fun x => z x - periodicMean z

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  `A` is the weighted
homogeneous datum of a mean-zero physical periodic field.  The omitted zero
mode and weight `|2 pi k|^s` are exactly
`paper/sections/01-introduction.tex:105-108`. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  IsPeriodicMeanZero z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A i k =
        (periodicHomogeneousWeight s k : ℂ) * periodicVectorFourierCoeff z i k

/-- **NEEDS REGISTRATION / TO BE ALIGNED WITH T10.**  The totalized
homogeneous norm on the mean-zero subspace, with the zero Fourier mode omitted
as in `paper/sections/01-introduction.tex:105-108`. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/-! ## 2. Physical periodic geometry and registered I02 vocabulary -/

/-- The integer lattice vector corresponding to one torus translate;
`paper/sections/03-torus.tex:53-66`. -/
def latticeVector (n : PeriodicFrequency) : Space :=
  NavierStokes.PeriodicIntegration.toSpace (fun i => (n i : ℝ))

/-- All integer translates of a set in one fundamental cube.  This is the
physical-layer spelling of periodization in
`paper/sections/03-torus.tex:22-30,53-66`. -/
def periodicCopies (S : Set Space) : Set Space :=
  {x | ∃ n : PeriodicFrequency, x - latticeVector n ∈ S}

/-- The affine copy `x0 + eps S` used for the localized packet and cutoff in
`paper/sections/03-torus.tex:101-118,184`. -/
def scaledSpatialSet (x₀ : Space) (ε : ℝ) (S : Set Space) : Set Space :=
  {x | ∃ y ∈ S, x = x₀ + ε • y}

/-- The interior of the unit fundamental cube with lower corner `a` in the
physical `R^3` representation; the coordinate ball has closure inside a cube
of this form in `paper/sections/03-torus.tex:22-23,53`. -/
def fundamentalCubeInterior (a : NavierStokes.PeriodicIntegration.Coords) : Set Space :=
  NavierStokes.PeriodicIntegration.toSpace ''
    Ioo a (a + 1)

/-- The registered Section 4 curl, reused verbatim because the vector-potential
calculation is local in any Euclidean ball
(`paper/sections/04-whole-space.tex:23-28`). -/
abbrev curl := BlowupDensity.Contracts.V1.curl

/-- The registered Section 4 cross product in the radial potential; see
`paper/sections/03-torus.tex:178-180`. -/
abbrev cross := BlowupDensity.Contracts.V1.cross

/-- The registered spelling of `theta_eps`; see
`paper/sections/03-torus.tex:183-185`. -/
abbrev scaledSpatialCutoff := BlowupDensity.Contracts.V1.scaledSpatialCutoff

/-- The registered spelling of `eta_eps`; see
`paper/sections/03-torus.tex:183-186`. -/
abbrev scaledTemporalCutoff := BlowupDensity.Contracts.V1.scaledTemporalCutoff

/-! ## 3. The T16 statement -/

/-- The clauses of Lemma `lem:potential` for fixed inputs and fixed witnesses.

The witnesses are parameters rather than data-valued projections because the
API is deliberately `Prop`-valued.  Each field is one concrete manuscript
clause: the Urysohn cutoffs, `eq:potential`, `eq:cutoff`, global smoothness,
unit periodicity, zero divergence, periodized support, or `eq:bgzero`.  There
are no placeholder propositions.
-/
structure LocalDivergenceFreeCutoffAPI
    (T δ r : ℝ) (v : VelocityField) (x₀ : Space) (Kstar : Set Space)
    (localizedVelocity : ℝ → VelocityField)
    (θ : Space → ℝ) (plateau : Set Space) (θRadius : ℝ)
    (η : ℝ → ℝ) (ε₀ : ℝ) (potential : VelocityField)
    (correction : ℝ → VelocityField) : Prop where
  /-- The spatial Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:167-174,181`. -/
  theta_smooth : ContDiff ℝ ∞ θ
  /-- The spatial Urysohn cutoff has compact support;
  `paper/sections/03-torus.tex:167-174,181`. -/
  theta_compactSupport : HasCompactSupport θ
  /-- The spatial cutoff takes nonnegative values;
  `paper/sections/03-torus.tex:171-172`. -/
  theta_nonneg : ∀ x : Space, 0 ≤ θ x
  /-- The spatial cutoff takes values at most one;
  `paper/sections/03-torus.tex:171-172`. -/
  theta_le_one : ∀ x : Space, θ x ≤ 1
  /-- The set on which `theta` is one is an open neighborhood;
  `paper/sections/03-torus.tex:172,181`. -/
  plateau_open : IsOpen plateau
  /-- The prescribed compact `K_*` lies in that neighborhood;
  `paper/sections/03-torus.tex:101-102,168-172,181`. -/
  prescribed_subset_plateau : Kstar ⊆ plateau
  /-- `theta = 1` throughout the open plateau;
  `paper/sections/03-torus.tex:172,181`. -/
  theta_one : EqOn θ (fun _ => 1) plateau
  /-- The explicit radius controlling the compact support is positive;
  `paper/sections/03-torus.tex:168-172,212`. -/
  theta_radius_pos : 0 < θRadius
  /-- The support of `theta` lies in the fixed reference ball;
  `paper/sections/03-torus.tex:168-172,212`. -/
  theta_support : tsupport θ ⊆ Metric.ball (0 : Space) θRadius
  /-- The time Urysohn cutoff is smooth;
  `paper/sections/03-torus.tex:173-174,182`. -/
  eta_smooth : ContDiff ℝ ∞ η
  /-- The time Urysohn cutoff has compact support;
  `paper/sections/03-torus.tex:173-174,182`. -/
  eta_compactSupport : HasCompactSupport η
  /-- The time cutoff takes nonnegative values;
  `paper/sections/03-torus.tex:171-174`. -/
  eta_nonneg : ∀ t : ℝ, 0 ≤ η t
  /-- The time cutoff takes values at most one;
  `paper/sections/03-torus.tex:171-174`. -/
  eta_le_one : ∀ t : ℝ, η t ≤ 1
  /-- `eta = 1` on `[-1,1]`;
  `paper/sections/03-torus.tex:181-182,214-215`. -/
  eta_one : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- `supp eta` lies in `(-2,2)`;
  `paper/sections/03-torus.tex:182,188-189`. -/
  eta_support : tsupport η ⊆ Ioo (-2 : ℝ) 2
  /-- The threshold in "for sufficiently small `eps`" is positive;
  `paper/sections/03-torus.tex:103-106,188`. -/
  eps_pos : 0 < ε₀
  /-- The cutoff time window stays in the regular positive-time slab;
  `paper/sections/03-torus.tex:212`. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ
  /-- The scaled spatial cutoff stays strictly inside the coordinate ball;
  `paper/sections/03-torus.tex:103-105,212`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r
  /-- The radial vector potential is smooth on the same local spacetime slab
  as the reference; `paper/sections/03-torus.tex:177-181`. -/
  potential_smooth :
    ContDiffOn ℝ ∞ potential
      (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r)
  /-- `A(x,t) = integral_0^1 rho v(x0 + rho (x-x0),t) cross (x-x0) d rho`;
  `paper/sections/03-torus.tex:177-180` (`eq:potential`). -/
  potential_formula : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    potential (t, x) =
      ∫ ρ in (0 : ℝ)..1,
        ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- The spatial curl of the radial potential equals the reference velocity;
  `paper/sections/03-torus.tex:181,196-210`. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    curl (fun y : Space => potential (t, y)) x = v (t, x)
  /-- `w_eps = -curl(eta_eps theta_eps A)` on the chosen coordinate ball;
  its periodic extension is specified by the following fields.
  `paper/sections/03-torus.tex:183-188` (`eq:cutoff`). -/
  correction_formula : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
    z.2 ∈ Metric.ball x₀ r →
      correction ε z =
        -curl (fun y : Space =>
            (scaledTemporalCutoff η T ε z.1 * scaledSpatialCutoff θ x₀ ε y) •
              potential (z.1, y)) z.2
  /-- The zero-extended, periodized correction is globally smooth, including
  across the coordinate-chart seam; `paper/sections/03-torus.tex:188,212`. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (correction ε)
  /-- The physical lift of the correction is unit-periodic in space;
  `paper/sections/03-torus.tex:188,212`. -/
  correction_periodic : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NavierStokes.ProblemStatement.UnitSpatialPeriodsOn univ (correction ε)
  /-- The correction is divergence free because it is a curl;
  `paper/sections/03-torus.tex:188,212`. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t : ℝ, ∀ x : Space,
      BlowupDensity.Contracts.V1.spatialDivergence (correction ε) t x = 0
  /-- In one torus copy, `w_eps` is supported in the scaled coordinate ball,
  and its time support lies in `(T-2 eps^2,T+2 eps^2)`;
  `paper/sections/03-torus.tex:188-189,212`. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ
        periodicCopies (Metric.ball x₀ (ε * θRadius))
  /-- `eq:bgzero`: during the active interval, `v + w_eps` vanishes on an
  open neighborhood of the periodized packet support;
  `paper/sections/03-torus.tex:190-193,214-215`. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x : Space => localizedVelocity ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, v (t, x) + correction ε (t, x) = 0

/-- Exact quantifier order of draft A.

First fix the reference, coordinate ball, compact packet set and the already
scaled packet family.  Assume only the local smoothness and incompressibility
used by the radial construction, spatial periodicity of the reference, and the
known scaled support of the packet.  Then choose the two cutoffs, the positive
small-scale threshold, the radial potential, and one correction family carrying
all conclusions of `LocalDivergenceFreeCutoffAPI`.

This is Lemma `lem:potential`,
`paper/sections/03-torus.tex:163-216`, with the coordinate-ball condition from
`paper/sections/03-torus.tex:22-23` and the scaled support from
`paper/sections/03-torus.tex:101-120` made explicit.
-/
def localDivergenceFreeCutoffStatement : Prop :=
  ∀ (T δ r : ℝ) (v : VelocityField) (x₀ : Space)
    (cubeOrigin : NavierStokes.PeriodicIntegration.Coords) (Kstar : Set Space)
    (localizedVelocity : ℝ → VelocityField),
    0 < T → 0 < δ → 0 < r →
    Metric.closedBall x₀ r ⊆ fundamentalCubeInterior cubeOrigin →
    IsCompact Kstar →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
    NavierStokes.ProblemStatement.UnitSpatialPeriodsOn (Ioo (0 : ℝ) (T + δ)) v →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      BlowupDensity.Contracts.V1.spatialDivergence v t x = 0) →
    (∀ ε : ℝ, 0 < ε → ∀ t ∈ Ico (T - ε ^ 2) T,
      tsupport (fun x : Space => localizedVelocity ε (t, x)) ⊆
        periodicCopies (scaledSpatialSet x₀ ε Kstar)) →
    ∃ (θ : Space → ℝ) (plateau : Set Space) (θRadius : ℝ)
      (η : ℝ → ℝ) (ε₀ : ℝ) (potential : VelocityField)
      (correction : ℝ → VelocityField),
      LocalDivergenceFreeCutoffAPI T δ r v x₀ Kstar localizedVelocity
        θ plateau θRadius η ε₀ potential correction

end BlowupDensity.Research.T16.DraftA
