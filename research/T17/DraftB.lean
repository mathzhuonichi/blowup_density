import Contracts.V1.Data
import Mathlib.Analysis.Fourier.AddCircleMulti
import Contracts.V1.Correction
import Contracts.V1.HomogeneousNorm

/-!
# T17 blind draft B: bounds for the periodic background correction

This statement-only draft specifies Lemma `lem:correction`
(`paper/sections/03-torus.tex:218-285`).  Physical torus fields remain
unit-periodic functions on `R^3`, while all torus norms use T10's quotient lift
and Fourier-data definitions.  T16 supplies the already constructed correction
`D.correction ε`; it is not reconstructed here.  T13's localization API is an
explicit input to the final `H^s(T^3)` estimate.

Research files are not importable Lean modules.  The declarations used below
are therefore copied into the draft namespaces requested by the lane brief and
are marked for deletion after their contracts are registered.
-/

noncomputable section

namespace BlowupDensity.T10.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators

-- copied from research/T10/Spec.lean:46-143; delete once registered

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the frequency lattice of the unit
three-torus. -/
abbrev PeriodicFrequency := Fin 3 → ℤ

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: Mathlib's unit additive three-torus. -/
abbrev PeriodicTorus := UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-90`: normalized Haar measure on the unit torus. -/
abbrev periodicTorusMeasure : Measure PeriodicTorus := volume

/-- `03-torus.tex:2-4` and the (P) representation fixed in
`collaboration/SECTION3_PLAN.md` §1: invariance under every positive unit
coordinate shift. Quantification over all `x` also supplies negative shifts. -/
def IsPeriodicSpatial {E : Type*} [Add E] (z : Space → E) : Prop :=
  ∀ x : Space, ∀ i : Fin 3, z (x + coordinateVector i) = z x

/-- `02-preliminaries.tex:28`: spatial periodicity on a specified set of times,
with time as the first spacetime coordinate. -/
def IsPeriodicOn {E : Type*} (I : Set ℝ) (z : SpaceTime → E) : Prop :=
  ∀ t ∈ I, ∀ x : Space, ∀ i : Fin 3,
    z (t, x + coordinateVector i) = z (t, x)

/-- `03-torus.tex:2-4`, `01-introduction.tex:89`, and `TorusCube.lean:25-26`: canonical realization
of the (P) field on Mathlib's unit torus, using representatives in `(0,1]^3`.
This is the local `NSFormalization.Paper1.torusLift` definition restated
verbatim, with its one-line `toSpace` map expanded. -/
def torusLift {E : Type*} (f : Space → E) (z : PeriodicTorus) : E :=
  f ((EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) z).val))

/-- `03-torus.tex:2-4` and `01-introduction.tex:89`: the coefficient
`ẑ(k) = ∫_T³ z(x) exp(-2π i k·x) dx`.  This is exactly the local
`NSFormalization.Paper1.periodicFourierCoeff`, restated so the eventual
contract needs no local implementation import. -/
def periodicFourierCoeff (f : Space → ℂ) (k : PeriodicFrequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-84`: the squared Bessel weight
`1 + 4π²|k|²` in the unit-period convention. -/
def periodicFrequencyWeight (k : PeriodicFrequency) : ℝ :=
  1 + 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `03-torus.tex:2-4`: scalar complete `ℓ²(Z³;ℂ)` coefficient data. -/
abbrev PeriodicScalarData := lp (fun _ : PeriodicFrequency ↦ ℂ) 2

/-- `03-torus.tex:2-4` and `01-introduction.tex:103`: three scalar coefficient sequences with the
Euclidean (`PiLp 2`) product norm. -/
abbrev PeriodicVectorData := WithLp 2 (Fin 3 → PeriodicScalarData)

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

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the complete real three-vector Sobolev datum
at order `s`.  An element is the *weighted* sequence
`(1+4π²|k|²)^(s/2) ẑ(k)` in `ℓ²`; `s` is a phantom index recording
the realization represented by that sequence. -/
abbrev PeriodicSobolev (_s : ℝ) := realPeriodicSubmodule

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

/-- `03-torus.tex:2-4` and `01-introduction.tex:83-103`: the total `H^s(T³)` extended norm of a
physical field, defined as the infimum of the norms of all representing data.
The empty infimum is `⊤`. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicDatum s z A}, ‖A.1‖ₑ

-- copied from research/T10/Spec.lean:148-211; delete once registered

/-- `03-torus.tex:395-401`: the normalized spatial mean of a real vector
field on the unit torus. -/
def meanT (z : SpatialField) : Space :=
  ∫ y : PeriodicTorus, torusLift z y ∂periodicTorusMeasure

/-- `03-torus.tex:395-401`: `z - ∫_T³ z`, the mean-free part of a periodic
field. -/
def meanZeroPartT (z : SpatialField) : SpatialField := fun x ↦ z x - meanT z

/-- `03-torus.tex:395-411`: a physical field has zero normalized torus mean. -/
def IsMeanZeroT (z : SpatialField) : Prop := meanT z = 0

/-- `01-introduction.tex:105-107`: the squared angular frequency
`|2πk|² = 4π²|k|²` in the unit-period convention. -/
def periodicAngularFrequencySq (k : PeriodicFrequency) : ℝ :=
  4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- `01-introduction.tex:105-107`: the homogeneous multiplier
`|2πk|^s = (4π²|k|²)^(s/2)`.  The omitted zero mode is represented by zero,
so every homogeneous datum has `A(0)=0`. -/
def homogeneousDatumWeight (s : ℝ) (k : PeriodicFrequency) : ℝ :=
  if k = 0 then 0 else Real.rpow (periodicAngularFrequencySq k) (s / 2)

/-- `01-introduction.tex:105-109`: `A` is the order-`s` homogeneous datum of a
mean-zero real periodic field.  Exact quantifier order: periodicity,
Haar integrability of the lift (lead amendment, `RECONCILIATION.md` §5: the
same junk-value reason as `IsPeriodicDatum`; it also makes `IsMeanZeroT` an
honest Haar-integral statement), zero mean, then
`∀ i : Fin 3, ∀ k : PeriodicFrequency`.  The zero-frequency equation forces
`A_i(0)=0`, as the manuscript's homogeneous convention requires. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicSobolev s) : Prop :=
  IsPeriodicSpatial z ∧ Integrable (torusLift z) periodicTorusMeasure ∧ IsMeanZeroT z ∧
    ∀ (i : Fin 3) (k : PeriodicFrequency),
      A.1 i k = (homogeneousDatumWeight s k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k

/-- `01-introduction.tex:105-109`: the total homogeneous
`Ḣ^s(T³)` extended norm of a mean-zero physical field.  It is the infimum over
homogeneous real data and is `⊤` when no datum exists. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicSobolev s // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

-- copied from research/T10/Spec.lean:255-268; delete once registered

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

-- copied from research/T10/Spec.lean:393-411; delete once registered

/-- `01-introduction.tex:143-150` eq:Enorm: the periodic
`L∞(0,T;L²(T³))` extended norm, on the open time interval. -/
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

namespace BlowupDensity.T16.Draft

open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open Set MeasureTheory
open scoped ContDiff Topology

-- copied from research/T16/Spec.lean:53-336; delete once registered

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

namespace BlowupDensity.T13.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open BlowupDensity.T10.Draft
open scoped ContDiff ENNReal BigOperators Topology

-- copied from research/T13/Spec.lean:168-312; delete once registered

/-! ## Fixed chart, support, and periodization -/

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

/-- `03-torus.tex:80-89`: the nonzero-lattice tail used in the proof of the
localization estimate.  Its bounds are proof lemmas, not API fields. -/
def latticeTail (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : {n : PeriodicFrequency // n ≠ 0},
    fractionalRadialKernel s (h + latticeVector n.1)

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

end BlowupDensity.T13.Draft

namespace BlowupDensity.T17.DraftB

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.T10.Draft
open BlowupDensity.T16.Draft
open scoped ContDiff ENNReal Topology BigOperators

/-! ## Torus mixed norms and the exact rescaled profiles -/

/-- `01-introduction.tex:134` and `03-torus.tex:235-237`: a measurable
`L^p(T³)`-valued path representing a periodic physical field on nonnegative
times.  The normalized Haar measure is the one fixed by T10.

Non-vacuity: the `Lp` carrier and the almost-everywhere realization exclude the
junk values that a bare iterated lower integral could produce. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField)
    (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x => f (t, x))

/-- `01-introduction.tex:134` and `03-torus.tex:235-237`: the periodic
`L^q(0,∞;L^p(T³))` extended norm, in the same measurable-path form as T10's
`forceSobolevENormT`.

Non-vacuity: an absent measurable `Lp` realization gives `⊤`, never a
spuriously small norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `03-torus.tex:130-131,235-237`:
`α(p,q)=-3+3/p+2/q`, with `1/∞=0` supplied by `ENNReal.toReal`.
The correction exponent in `eq:Hmixed` is arithmetically
`-2+3/p+2/q = correctionAlpha p q + 1`. -/
def correctionAlpha (p q : ℝ≥0∞) : ℝ :=
  -3 + 3 / p.toReal + 2 / q.toReal

/-- `03-torus.tex:245-260`: the fixed rescaled support cylinder
`[-2,2] × closedBall(0,R_*)` containing
`tsupport η × tsupport θ` at every admissible scale. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) D.θRadius

/-- `03-torus.tex:245,262-263`: the reference velocity in parabolic
coordinates, `V_ε(z,σ)=v(x₀+εz,T+ε²σ)`, written in time-first order. -/
def rescaledReference (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z => v (T + ε ^ 2 * z.1, x₀ + ε • z.2)

/-- `03-torus.tex:247-253`: the amplitude-one radial-potential profile
`𝒜_ε(z,σ)=∫₀¹ r v(x₀+εrz,T+ε²σ)×z dr`. -/
def rescaledPotential (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z => ∫ ρ in (0 : ℝ)..1,
    ρ • cross (v (T + ε ^ 2 * z.1, x₀ + ε • (ρ • z.2))) z.2

/-- `03-torus.tex:256-259`: the exact amplitude-one correction profile
`W_ε=-curl_z(η(σ)θ(z)𝒜_ε)`.

Non-vacuity: this is a concrete formula from T16's stored cutoffs and the
rescaled radial potential, not an unconstrained profile parameter. -/
def rescaledCorrectionProfile (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (D : CutoffData) : SpaceTimeField :=
  fun z => -curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotential v x₀ T ε (z.1, y)) z.2

/-- `03-torus.tex:219-223`, equation `eq:H`: the correction force belonging
to T16's concrete correction `D.correction ε`, with the displayed signs and
transport order
`∂ₜw-νΔw+(v·∇)w+(w·∇)v+(w·∇)w`. -/
def correctionForce (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  fun z =>
    temporalDerivative (D.correction ε) z.1 z.2 -
      ν • spatialLaplacian (D.correction ε) z.1 z.2 +
      spatialDerivative (D.correction ε) z.1 z.2 (v z) +
      spatialDerivative v z.1 z.2 (D.correction ε z) +
      advection (D.correction ε) z.1 z.2

/-- `03-torus.tex:264-272`: the bracketed amplitude-one force profile in
rescaled coordinates.  The five terms have exactly the powers and signs of the
paper: `∂σW-νΔzW+ε(V·∇z)W+ε²(W·∇x)v+ε(W·∇z)W`. -/
def rescaledForceProfile (ν : ℝ) (v : SpaceTimeField) (x₀ : Space)
    (T ε : ℝ) (D : CutoffData) : SpaceTimeField :=
  let W := rescaledCorrectionProfile v x₀ T ε D
  let V := rescaledReference v x₀ T ε
  fun z =>
    temporalDerivative W z.1 z.2 - ν • spatialLaplacian W z.1 z.2 +
      ε • spatialDerivative W z.1 z.2 (V z) +
      (ε ^ 2) • spatialDerivative v (T + ε ^ 2 * z.1)
        (x₀ + ε • z.2) (W z) +
      ε • advection W z.1 z.2

/-- `03-torus.tex:225,275`: lift a periodic spacetime field to
`ℝ × T³`, so support volumes are measured once on the torus rather than over
all lattice translates in `ℝ³`. -/
def torusSpaceTimeLift (f : SpaceTimeField) : ℝ × PeriodicTorus → Space :=
  fun z => torusLift (fun x => f (z.1, x)) z.2

/-- `03-torus.tex:225`: the spatial projection of a periodic spacetime
support, measured on one normalized torus copy. -/
def torusSpatialSupport (f : SpaceTimeField) : Set PeriodicTorus :=
  Prod.snd '' tsupport (torusSpaceTimeLift f)

/-- `03-torus.tex:225`: the temporal projection of the same torus support. -/
def torusTemporalSupport (f : SpaceTimeField) : Set ℝ :=
  Prod.fst '' tsupport (torusSpaceTimeLift f)

/-! ## Lemma `lem:correction` -/

/-- The clauses of `lem:correction`, `paper/sections/03-torus.tex:218-285`,
for T16's already chosen correction family and T13's localization theorem.

This record is `Type`-valued: the constants are data selected once before the
scale `ε`, following the registered A03/A05/I02 house style.  The profile
fields spell out the proof's only analytic input: `W_ε` and its exact force
profile are smooth, supported in the fixed cylinder
`[-2,2] × closedBall(0,D.θRadius)`, and every fixed derivative order is bounded
there uniformly in `ε`.  No T15 packet field is used.

The explicit `MemLp` fields make the energy and mixed Lebesgue norms honest.
For `eq:HHs`, finiteness of T10's infimum-over-integrable-data norm supplies the
corresponding no-junk guarantee. -/
structure CorrectionAPI (ν : ℝ) (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData)
    (_potential : LocalPotentialAPI v U K x₀ r T δ D)
    (_localization : BlowupDensity.T13.Draft.LocalizationAPI) : Type where
  /-- The ambient viscosity is positive; context for Lemma `lem:correction`,
  `paper/sections/03-torus.tex:103,218-223`. -/
  viscosity_pos : 0 < ν
  /-- A harmless normalization of “sufficiently small”; it lets the fixed
  profile bounds use one compact scale interval, `03-torus.tex:242,245-260`. -/
  eps_le_one : D.ε₀ ≤ 1

  /-- `03-torus.tex:245-260`: each exact correction profile is smooth on the
  fixed rescaled cylinder. -/
  correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile v x₀ T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:256-260`: all correction profiles have support in the same
  fixed cylinder. -/
  correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile v x₀ T ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:254-260`: for every fixed full derivative order, one
  nonnegative bound works for all small scales and all points of the fixed
  cylinder. -/
  correctionProfileConst : ℕ → ℝ
  /-- Nonnegativity of the uniform correction-profile constants;
  `paper/sections/03-torus.tex:254-260`. -/
  correctionProfileConst_nonneg : ∀ k, 0 ≤ correctionProfileConst k
  /-- The uniform derivative bounds expressing “uniformly smooth family”
  exactly on the fixed cylinder, `paper/sections/03-torus.tex:254-260`. -/
  correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v x₀ T ε D) z‖ ≤
        correctionProfileConst k

  /-- `03-torus.tex:262-273`: the exact bracketed force profile is smooth on
  the same fixed cylinder. -/
  force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν v x₀ T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:262-273`: the force profile is supported wherever the
  cutoff correction profile is supported. -/
  force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν v x₀ T ε D) ⊆ fixedProfileCylinder D
  /-- Constants for uniform smoothness of the exact force profile;
  `paper/sections/03-torus.tex:262-273`. -/
  forceProfileConst : ℕ → ℝ
  /-- Nonnegativity of the force-profile constants;
  `paper/sections/03-torus.tex:262-273`. -/
  forceProfileConst_nonneg : ∀ k, 0 ≤ forceProfileConst k
  /-- Every fixed derivative of the force profile is uniformly bounded on the
  fixed cylinder, `paper/sections/03-torus.tex:262-273`. -/
  force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v x₀ T ε D) z‖ ≤
        forceProfileConst k
  /-- `03-torus.tex:247-260`: T16's physical correction is exactly the
  amplitude-one rescaled profile on its fixed support cylinder. -/
  correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (T + ε ^ 2 * z.1, x₀ + ε • z.2) =
        rescaledCorrectionProfile v x₀ T ε D z
  /-- `03-torus.tex:264-272`: the physical correction force is exactly
  `ε⁻²` times the displayed rescaled force profile. -/
  force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (T + ε ^ 2 * z.1, x₀ + ε • z.2) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z

  /-- “`H_ε` is smooth across `T` and extends by zero outside its cutoff
  support”, `paper/sections/03-torus.tex:225`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν v D ε)
  /-- The correction force is a unit-periodic physical lift, as required for
  every torus norm below; `paper/sections/03-torus.tex:225,235-240`. -/
  force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν v D ε)
  /-- The physical support is the periodic lift of the `O(ε)` spatial ball
  during the `O(ε²)` cutoff window, `paper/sections/03-torus.tex:225`. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν v D ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.closedBall x₀ (ε * D.θRadius))
  /-- Constant in the spatial support-volume estimate;
  `paper/sections/03-torus.tex:225`. -/
  spatialVolumeConst : ℝ
  /-- The volume constant is nonnegative; `paper/sections/03-torus.tex:225`. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- “Its spatial support has volume `O(ε³)`”, measured once on normalized
  `T³`, `paper/sections/03-torus.tex:225`. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- “Its temporal support has length `O(ε²)`”; the displayed cutoff window
  has length `4ε²`, `paper/sections/03-torus.tex:225`. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2)

  /-- Constants `C_{β,j}` for the first estimate in
  `eq:derivativebounds`, `paper/sections/03-torus.tex:225-230`.  `m=|β|`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- Nonnegativity of `C_{β,j}`, `paper/sections/03-torus.tex:225-230`. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `|∂ₜʲ∂ₓᵝw_ε| ≤ C_{β,j} ε^{-2j-|β|}`.  Arbitrary unit spatial
  directions imply each coordinate multi-index case,
  `paper/sections/03-torus.tex:225-230`. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)
  /-- Constants `C_β` for the force estimate in `eq:derivativebounds`,
  `paper/sections/03-torus.tex:225-230`. -/
  forceDerivConst : ℕ → ℝ
  /-- Nonnegativity of `C_β`, `paper/sections/03-torus.tex:225-230`. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `|∂ₓᵝH_ε| ≤ C_β ε^{-2-|β|}`, including the amplitude case
  `m=0`, `paper/sections/03-torus.tex:225-230`. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (ε⁻¹) ^ (2 + m)

  /-- Each torus slice of `w_ε` is an honest `L²` function, preventing a
  junk-value energy bound; implicit in `eq:wE`,
  `paper/sections/03-torus.tex:232-234,275-280`. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction ε (t, x))) 2 periodicTorusMeasure
  /-- Each full spatial-gradient slice of `w_ε` is honestly in `L²`, the
  second part of `E_T`, `paper/sections/03-torus.tex:232-234,275-280`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction ε) t x)) 2
      periodicTorusMeasure
  /-- The finite scale-independent constant in `eq:wE`,
  `paper/sections/03-torus.tex:232-234,242`. -/
  energyConst : ℝ≥0∞
  /-- Finiteness of the energy constant rules out `⊤` as a vacuous witness;
  `paper/sections/03-torus.tex:232-234,242`. -/
  energyConst_finite : energyConst < ⊤
  /-- `‖w_ε‖_{E_T} ≤ C ε^{3/2}`, with T10's periodic energy norm,
  `paper/sections/03-torus.tex:232-234,275-280`. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT T (D.correction ε) ≤
      energyConst * ENNReal.ofReal (ε ^ ((3 : ℝ) / 2))

  /-- Every torus slice of `H_ε` has an honest `L^p` realization, including
  `p=∞`; implicit in `eq:Hmixed`, `paper/sections/03-torus.tex:235-237,281-282`. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v D ε (t, x))) p
        periodicTorusMeasure
  /-- The constants `C_{p,q}` of `eq:Hmixed`, chosen before `ε`,
  `paper/sections/03-torus.tex:235-237,242`. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞
  /-- Each `C_{p,q}` is finite throughout `1≤p,q≤∞`, so the norm estimate is
  non-vacuous; `paper/sections/03-torus.tex:235-237,242`. -/
  mixedConst_finite : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    mixedConst p q < ⊤
  /-- `‖H_ε‖_{L^q(0,∞;L^p(T³))} ≤ C_{p,q} ε^{-2+3/p+2/q}` for
  every `1≤p,q≤∞`, including both essential-supremum endpoints.  By the
  explicit definition of `correctionAlpha`, this is arithmetically
  `-2+3/p+2/q`, exactly the equality in `eq:Hmixed`;
  `paper/sections/03-torus.tex:235-237,281-282`. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        mixedConst p q * ENNReal.ofReal
          (ε ^ (correctionAlpha p q + 1))

  /-- Constants `C_s` in `eq:HHs`, chosen before `ε`,
  `paper/sections/03-torus.tex:238-242,284`. -/
  sobolevConst : ℝ → ℝ≥0∞
  /-- `C_s` is finite for every `0≤s≤1`, preventing a vacuous top-valued
  Sobolev bound; `paper/sections/03-torus.tex:238-242,284`. -/
  sobolevConst_finite : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → sobolevConst s < ⊤
  /-- `‖H_ε‖_{L¹(0,∞;H^s(T³))} ≤
  C_s(ε^{3/2}+ε^{3/2-s})` for `0≤s≤1`.  The T13 localization witness is an
  explicit parameter of this record; `paper/sections/03-torus.tex:238-240,284`. -/
  force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
        sobolevConst s *
          (ENNReal.ofReal (ε ^ ((3 : ℝ) / 2)) +
            ENNReal.ofReal (ε ^ ((3 : ℝ) / 2 - s)))

end BlowupDensity.T17.DraftB
