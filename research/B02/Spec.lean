import Contracts.V1.Data

/-!
# B02 draft specification: homogeneous `Ḣ^{-1}` approximation

Task `collaboration/tasks/B02.md`, graph node `B02` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:322-329`, consumed by `R46`
(`research/section4/STATEMENTS.md:831-836`).

This file is a *specification draft only*.  It contains `def`s and one
obligation record.  It proves nothing with mathematical content, assumes
nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects of `Contracts.V1.Data`.

## What is specified

The `L²(0,∞;Ḣ^{-1}(R³))` clause of Proposition 4.6 (`prop:Renergy`,
`paper/sections/04-whole-space.tex:218-229`), whose proof is the paragraph at
`04-whole-space.tex:241-249` followed by the Bochner paragraph at `:251-260`.
Paragraph `:241` is one long source line carrying stages 1-2 and the
announcement of the split; the align block is `:242-248` with the label
`eq:Rnegative-cutoff` at `:247`; `:249` carries stages 3's justification, 4
and 5.
The homogeneous realization is the manuscript's own,
`02-preliminaries.tex:58-69` eq:homogeneous-realization, fixed in Lean as
`Data.lean.IsHomogeneousDatum` (`verification/Contracts/V1/Data.lean:324`):
`ĥ = |ξ|^{-s} G` with `G ∈ L²`, so at `s = -1` literally `ĥ = |ξ| G`.

The stages, in the manuscript's order.

1. `04-whole-space.tex:241` — "For `h ∈ Ḣ^{-1}`, instead approximate
   `G = |ξ|^{-1}ĥ` in `L²` by smooth compactly supported `G_n` supported away
   from `0`.  One first restricts to `1/n < |ξ| < n`, with `L²` error tending to
   zero, and then smooths each restricted function with a sufficiently small
   mollification radius and a slightly larger annular cutoff."  Fields
   `annularRestriction` and `annularSmoothing`; the path-level reading of the
   same truncation is `annularPathApprox`.
2. `04-whole-space.tex:241` — "Set `ĥ_n = |ξ|G_n`.  Again `h_n` is Schwartz
   and `h_n → h` in `Ḣ^{-1}`."  Field `annularSchwartz`; the convergence is the
   `L²` datum estimate of stage 1, because `Data.lean:338` `homogeneousENorm`
   *is* the datum norm.
3. `04-whole-space.tex:241-248` eq:Rnegative-cutoff (the align block is
   `:242-248`, the label at `:247`) — the low/high-frequency
   split `‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²` for `k ∈ L¹ ∩ L²`.  Fields
   `lowFrequencyIntegrable`, `lowFrequencyIntegral`, `fourierSupBound`,
   `lowHighSplit`, and the realization bridge `lebesgueHomogeneousDatum` /
   `homogeneousDatumSub` without
   which the split does not reach the datum norm that the conclusion uses.
4. `04-whole-space.tex:249` — "Since `(1−χ_R)h_n → 0` in both `L¹` and
   `L²`, eq:Rnegative-cutoff proves `χ_Rh_n → h_n` in `Ḣ^{-1}`.  A diagonal
   choice gives compact-smooth density in this realization, without a dual
   Sobolev-embedding assumption."  Fields `cutoffLebesgue` and the combined
   `spatialApproxHomogeneous`.
5. `04-whole-space.tex:249` — "take real parts of each component of the
   approximants"; conjugation is an isometry because the weight `|ξ|^{2s}` is
   real and even.  This stage is invisible in Lean, exactly as in `B01`:
   `RealVectorSobolev s` *is* the conjugate-reflection subspace
   (`02-preliminaries.tex:72`, `Data.lean` §2, §4).
6. `04-whole-space.tex:251-260` — the Bochner stage, **shared verbatim with
   `B01`**: `temporalApprox` / `SeparatedTemporalDense`, and the packaging
   `separatedAssembly`.

## Which `s` the argument covers

The manuscript states and uses only `Ḣ^{-1}` (`04-whole-space.tex:219,226,241`).
Its argument generalises, but **not** to every real `s`, unlike the
inhomogeneous stages of `B01` (`04-whole-space.tex:231,239`, "for every real
`s`").  The exact range is

  `-3/2 < s ≤ 0`,

and every field below that mentions the split carries those two hypotheses.
Where each half comes from:

* **`-3/2 < s`** is needed twice, and for the same reason both times: the
  low-frequency integral `∫_{|ξ|<1}|ξ|^{2s}dξ` converges exactly when
  `2s > -3`.  The manuscript says it once — "The integral at the origin is
  finite in dimension three" (`04-whole-space.tex:249`) — and once more in the
  temperedness estimate of `02-preliminaries.tex:66-69` that makes
  `IsHomogeneousDatum` a *realization* at all.  It is the hypothesis `hs` of the
  in-tree `homogeneous_low_frequency_integrable`
  (`Paper3/SobolevWeights.lean:54`).
* **`s ≤ 0`** is needed for the high-frequency half: the manuscript drops
  `|ξ|^{-2} ≤ 1` on `|ξ| ≥ 1` (`04-whole-space.tex:246-247`), which for general
  `s` is `|ξ|^{2s} ≤ 1`, i.e. `s ≤ 0`.  It is the hypothesis `hs0` of
  `homogeneous_energy_le_bound_add_L2` (`Paper3/HomogeneousTime.lean:14`).

Stages 1, 2 and 6 need neither hypothesis: the annular approximation of an `L²`
datum and the Bochner step are insensitive to `s`, and `ĥ_n = |ξ|^{-s}G_n` is
Schwartz for every real `s` once `G_n ∈ C_c^∞(R³∖{0})`.

For `0 ≤ s < 3/2` the *conclusion* is still true but by a different route,
which this contract deliberately does **not** state: there
`|ξ|^{2s} ≤ (1+|ξ|²)^s`, so `‖z‖_{Ḣ^s} ≤ ‖z‖_{H^s}` and the cutoff stage is
`B01`'s `cutoffApprox` unchanged.  For `s ≤ -3/2` the realization itself fails
(`02-preliminaries.tex:70`, `Data.lean:313-321`).  So the honest summary is:
`B02`'s argument covers `-3/2 < s ≤ 0`, `B01`'s covers every real `s`, they
overlap nowhere in method, and `s = -1` — the only case `R46` consumes — lies in
the interior of `B02`'s range.

## Relation to `B01`

`research/B01/COMPARISON.md` §3 fixes the interface and this file follows it.

* `SeparatedTemporalDense`, `separatedField` and `separatedPath` are the *same*
  objects as in `research/B01/Spec.lean`.  They are **restated** here rather
  than imported only because `research/` is not on the Lake module path
  (`verification` is the package root); when both drafts are promoted to
  `verification/Contracts/V1/`, exactly one copy must survive.  The restatements
  below are character-for-character the `B01` ones.
* `separatedAssembly` differs from `B01`'s in exactly one conjunct:
  `IsHomogeneousPath s` replaces `IsSobolevPath s`.
* `B01`'s `schwartzApprox`, `cutoffApprox` and `spatialApprox` have **no**
  `Ḣ^{-1}` analogue and are not reused; stages 1-4 above replace them.
* `compactSubsetForceR` (`forceClassCompact ⊆ forceClassR`) is an input to
  `B02`, not an obligation of it — `02-preliminaries.tex:17` eq:Rclasses uses
  `H^m` and never `Ḣ^s`.  It is `B01`'s field of the same name.

## Conventions

* Time is the first spacetime coordinate; `Space = EuclideanSpace ℝ (Fin 3)`
  (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:30,33`).
* Force norms use `(0,∞)`: `forceTimeMeasure = volume.restrict (Ioi 0)`
  (`01-introduction.tex:140`, `Data.lean:115-118`).
* Fourier: the manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx` (`01-introduction.tex:91`), in Lean
  `NSFormalization.Source.angularFourier`.  Every constant below is the one this
  normalization produces; in particular the manuscript's unnamed `C` of
  eq:Rnegative-cutoff is `(2π)^{-3}`, the square of the `L¹ → L^∞` constant of
  this transform, and is written out in `fourierSupBound` and `lowHighSplit`.
* `F_c = C_c^∞(R³ × (0,∞);R³)` is `Data.lean.MemForceCompact`
  (`04-whole-space.tex:185`).
* Every norm is the `ℝ≥0∞`-valued one of `Data.lean`, so nothing has to be
  assumed finite in order to be written.
-/

noncomputable section

namespace BlowupDensity.B02.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Named objects of the homogeneous approximation -/

/-- `04-whole-space.tex:241`, "`1/n < |ξ| < n`": the open frequency annulus on
which the manuscript's first truncation lives.  `δ` is the inner radius and `R`
the outer one; "supported away from `0`" is `0 < δ`. -/
def frequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ < ‖ξ‖ ∧ ‖ξ‖ < R}

/-- `04-whole-space.tex:241`, "a slightly larger annular cutoff": the closed
annulus that contains the support of the mollified datum.  It is compact for
every `δ, R`, so `tsupport g ⊆ closedFrequencyAnnulus δ R` already gives
`HasCompactSupport g`. -/
def closedFrequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R}

/-- `04-whole-space.tex:241`: `Z` is an order-`s` datum whose three
components are (a.e.) smooth functions supported in the closed annulus
`δ ≤ |ξ| ≤ R`, i.e. one of the manuscript's `G_n ∈ C_c^∞(R³∖{0})`.

Stated through an explicit representative rather than through a multiplication
operator on `RealVectorSobolev s`, because a datum is an `L²` class: there is no
`def` producing "the annular truncation of `Z`" without first proving that the
truncation still lies in the conjugate-reflection subspace, and this file proves
nothing. -/
def IsAnnularDatum {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∃ g : Fin 3 → Space → ℂ,
    (∀ i, ContDiff ℝ ∞ (g i)) ∧
    (∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R) ∧
    (∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i)

/-- `04-whole-space.tex:241`: `Z` is the restriction of the datum `A` to the
open annulus `δ < |ξ| < R`, the first of the manuscript's two truncation
sub-steps.  No smoothness; that is `IsAnnularDatum`. -/
def IsAnnularRestriction {s : ℝ} (δ R : ℝ) (A Z : RealVectorSobolev s) : Prop :=
  ∀ i, ((Z i : FourierData) : Space → ℂ)
    =ᵐ[volume] (frequencyAnnulus δ R).indicator ((A i : FourierData) : Space → ℂ)

/-- `04-whole-space.tex:241`: the datum of `Z` vanishes a.e. off the open
annulus `δ < |ξ| < R`.  This is the hypothesis the mollification step consumes —
`IsAnnularRestriction δ R A Z` implies it for every `A` — and it is what makes
"a slightly larger annular cutoff" (`:241`) possible without touching the
origin. -/
def IsAnnularSupported {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, ∀ᵐ ξ : Space ∂volume,
    ξ ∉ frequencyAnnulus δ R → ((Z i : FourierData) : Space → ℂ) ξ = 0

/-- `04-whole-space.tex:235`, `χ_R(x) = χ(x/R)`: the dilated spatial cutoff.
The manuscript introduces `χ` once, at `:235`, and reuses it verbatim in the
homogeneous paragraph at `:248`.  Written with `R⁻¹ • x` so that no positivity
of `R` is needed to form the expression; `cutoffLebesgue` takes `R → ∞`.
Same object as `research/B01/Spec.lean`'s `scaledCutoff`. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) : Space → ℝ := fun x => χ (R⁻¹ • x)

/-- The real Euclidean three-vector field assembled from three real scalar
components.  `04-whole-space.tex:249` "take real parts of **each component** of
the approximants": the manuscript's stage 2 is componentwise, and Mathlib has no
finite-product assembly of `SchwartzMap`.  Same object as
`research/B01/Spec.lean`'s `schwartzVector`. -/
def schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) : SpatialField :=
  fun x => WithLp.toLp 2 (fun i => ψ i x)

/-- `04-whole-space.tex:260`, "the finite sum `Σ_j φ_j(t) h_j(x)`".  Same object
as `research/B01/Spec.lean`'s `separatedField`; the Bochner stage is shared. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- The order-`s` datum path of `separatedField φ h`.  Same object as
`research/B01/Spec.lean`'s `separatedPath`; only the *realization* asserted of
it by `separatedAssembly` differs (`IsHomogeneousPath` here,
`IsSobolevPath` there). -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-- `04-whole-space.tex:246-247` eq:Rnegative-cutoff, the constant made
explicit.  The manuscript writes
`≤ C‖k‖₁²∫_{|ξ|<1}|ξ|^{-2}dξ + ‖k‖₂² ≤ C'‖k‖₁² + ‖k‖₂²`, leaving `C` unnamed;
`C` is the square of the `L¹ → L^∞` constant of the manuscript's unitary angular
transform (`01-introduction.tex:91`), namely `(2π)^{-3/2}`, so `C = (2π)^{-3}`
and `C'` is this expression.  At `s = -1` in dimension three
`∫_{|ξ|<1}|ξ|^{-2}dξ = 4π` (field `lowFrequencyIntegral`), hence
`C' = (2π)^{-3}·4π = 1/(2π²)`. -/
def lowHighConstant (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ)) * ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)

/-- `04-whole-space.tex:241,246,249`: the range of orders on which the
manuscript's homogeneous argument runs, `-3/2 < s ≤ 0`.  See the module
docstring for where each half is used; `s = -1` is the manuscript's case. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-! ## 2. The contract -/

/-- Every obligation that the homogeneous clause of Proposition 4.6
(`prop:Renergy`, `paper/sections/04-whole-space.tex:218-229`, homogeneous proof
paragraph at `:241-249`, Bochner paragraph at `:251-260`) places on the
completed force space `L²(0,∞;Ḣ^{-1}(R³))`, in the form `R46` consumes
(`research/section4/STATEMENTS.md:831-836`).

Layout of the fields.

* `χ … chi_range`: the fixed cutoff of `04-whole-space.tex:235`, reused by the
  homogeneous paragraph at `:249`.  Identical to `B01`'s five fields.
* `annularRestriction`, `annularSmoothing`, `annularSchwartz`: stages 1-2.
* `annularPathApprox`: the path-level reading of stage 1, in the
  `L²(0,∞;Ḣ^{-1})` norm itself.
* `lowFrequencyIntegrable`, `lowFrequencyIntegral`, `fourierSupBound`,
  `lowHighSplit`: stage 3, eq:Rnegative-cutoff, with its constants written out.
* `lebesgueHomogeneousDatum`, `homogeneousDatumSub`: the realization bridge.
  Without them stage 3 controls `homogeneousFourierENorm`, a Fourier integral,
  while the conclusion speaks of `‖·‖ₑ` of an `IsHomogeneousSliceDatum`; nothing
  in the tree connects the two (`research/I03/COMPARISON.md` U7c).
* `cutoffLebesgue`, `spatialApproxHomogeneous`: stage 4 and its diagonal
  conclusion.
* `temporalApprox`, `separatedAssembly`: stage 6, shared with `B01`.
* `approxCompactHomogeneous`: the conclusion, in `Data.lean`'s
  `CompletedDenseHomogeneous`.

Deliberately absent, because `research/B01/COMPARISON.md` §3 assigns them to
`B01`: `forceClassCompact ⊆ forceClassR`, and the identification of the
datum-path completion with the bundled Bochner space `Lp (RealVectorSobolev s) q
forceTimeMeasure`.  Both are realization-independent — they mention no
`IsSobolevPath` and no `IsHomogeneousPath` — so `B02` consumes `B01`'s.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder. -/
structure HomogeneousApproxAPI where
  -- ### The fixed spatial cutoff, `04-whole-space.tex:235`, reused at `:249`
  /-- `χ ∈ C_c^∞`, "equal to one on the unit ball and zero outside the ball of
  radius two, with `0 ≤ χ ≤ 1`", `paper/sections/04-whole-space.tex:235`. -/
  χ : Space → ℝ
  /-- `χ` is smooth, `04-whole-space.tex:235`. -/
  chi_smooth : ContDiff ℝ ∞ χ
  /-- `χ = 1` on the closed unit ball, `04-whole-space.tex:235`. -/
  chi_one : ∀ x : Space, ‖x‖ ≤ 1 → χ x = 1
  /-- `χ = 0` outside the ball of radius two, `04-whole-space.tex:235`.  With
  `chi_smooth` this gives `HasCompactSupport χ`. -/
  chi_vanishes : ∀ x : Space, 2 ≤ ‖x‖ → χ x = 0
  /-- `0 ≤ χ ≤ 1`, `04-whole-space.tex:235`. -/
  chi_range : ∀ x : Space, χ x ∈ Icc (0 : ℝ) 1

  -- ### Stage 1a: restriction to a compact annulus
  /-- `04-whole-space.tex:241`.  "One first restricts to `1/n < |ξ| < n`, with
  `L²` error tending to zero."

  Stated on the datum, because `Data.lean:338` `homogeneousENorm` *is* the `L²`
  norm of the datum: the manuscript's `G = |ξ|^{-1}ĥ` is literally the element
  of `RealVectorSobolev s` that `IsHomogeneousDatum` quantifies over
  (`Data.lean:324`), and `02-preliminaries.tex:63` is the statement that this
  identification is an isometric bijection onto `L²`.

  Every real `s` is covered: the step is a property of `L²`, not of the weight.
  The inner radius is positive, which is the manuscript's "supported away from
  `0`". -/
  annularRestriction : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (δ R : ℝ) (Z : RealVectorSobolev s),
      0 < δ ∧ δ < R ∧ IsAnnularRestriction δ R A Z ∧ ‖Z - A‖ₑ < η

  -- ### Stage 1b: mollification inside a slightly larger annulus
  /-- `04-whole-space.tex:241`.  "… and then smooths each restricted
  function with a sufficiently small mollification radius and a slightly larger
  annular cutoff."

  The conclusion is the manuscript's `G_n ∈ C_c^∞(R³∖{0})`: an
  `IsAnnularDatum δ' R'` with `0 < δ' < δ` and `R < R'`, so that the enlarged
  annulus still avoids the origin.  Every real `s`. -/
  annularSmoothing : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
      ∀ (Z : RealVectorSobolev s), IsAnnularSupported δ R Z →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (δ' R' : ℝ) (W : RealVectorSobolev s),
      0 < δ' ∧ δ' < δ ∧ R < R' ∧ IsAnnularDatum δ' R' W ∧ ‖W - Z‖ₑ < η

  -- ### Stage 1, path level
  /-- `04-whole-space.tex:241` read directly in the norm of the completed
  space `L^q(0,∞;Ḣ^s(R³))` rather than in its fibre: a single annulus
  `δ < |ξ| < R` truncates a whole datum path to within `η`.

  This is the statement the task card names ("for a homogeneous datum path,
  truncation away from `|ξ| < δ` and beyond `|ξ| > R` approximates in
  `L²_tḢ^{-1}`").  It is *not* a step of the manuscript's own proof, which
  performs the Bochner reduction **first** (`04-whole-space.tex:251`) and only
  then approximates the finitely many values `b_j ∈ X`; it is recorded because
  it is the shape a path-first implementation would use, and because it is the
  only field in which the annular truncation is visible in the manuscript's
  displayed norm.  A single `(δ,R)` suffices for a whole path by dominated
  convergence, the truncation being a contraction on each fibre — but no
  smoothness of the truncated datum is available uniformly in `t`, which is why
  the conclusion is an `IsAnnularRestriction` and not an `IsAnnularDatum`, and
  why `approxCompactHomogeneous` does not route through this field. -/
  annularPathApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
      (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (δ R : ℝ) (D : ℝ → RealVectorSobolev s),
      0 < δ ∧ δ < R ∧ (∀ t : ℝ, IsAnnularRestriction δ R (b t) (D t)) ∧
        MemBochnerDatum q s D ∧ bochnerDatumENorm q s (D - b) < η

  -- ### Stage 2: `ĥ_n = |ξ|^{-s}G_n` is Schwartz
  /-- `04-whole-space.tex:241`.  "Set `ĥ_n = |ξ|G_n`.  Again `h_n` is
  Schwartz and `h_n → h` in `Ḣ^{-1}`."

  `IsHomogeneousDatum s G u` says `û = |ξ|^{-s}G` (`Data.lean:324`), so at
  `s = -1` this field is exactly the manuscript's `ĥ_n = |ξ|G_n`: from an
  annular smooth compactly supported datum `W`, the field it realizes is a real
  vector Schwartz field.  Smoothness of `|ξ|^{-s}` away from the origin is why
  the inner radius must be positive; `04-whole-space.tex:235` is the same
  integration-by-parts argument one order up.

  The convergence half of the manuscript's sentence is *not* a separate
  obligation: `‖h_n − h‖_{Ḣ^s} = ‖W − A‖` by `02-preliminaries.tex:63`, which is
  the estimate already delivered by `annularRestriction` and
  `annularSmoothing`.

  Every real `s`; reality of `h_n` is automatic from `RealVectorSobolev s`
  being the conjugate-reflection subspace, which is the manuscript's
  `04-whole-space.tex:249`. -/
  annularSchwartz : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
      ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
    ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W

  -- ### Stage 3: eq:Rnegative-cutoff
  /-- `04-whole-space.tex:249`, "The integral at the origin is finite in
  dimension three": the low-frequency weight is integrable on the unit ball
  exactly when `2s > -3`.  This is the `-3/2 < s` half of `SplitRange`. -/
  lowFrequencyIntegrable : ∀ s : ℝ, -3 / 2 < s →
    IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s)) (Metric.ball (0 : Space) 1) volume

  /-- `04-whole-space.tex:246`, the factor `∫_{|ξ|<1}|ξ|^{-2}dξ` of
  eq:Rnegative-cutoff evaluated in dimension three at the manuscript's order
  `s = -1`: `∫_0^1 r^{-2}·4πr²dr = 4π`.  This is what turns the manuscript's
  unnamed `C'` into the explicit `(2π)^{-3}·4π = 1/(2π²)`
  (`lowHighConstant (-1)`). -/
  lowFrequencyIntegral :
    (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * (-1 : ℝ))) = 4 * Real.pi

  /-- `04-whole-space.tex:246`, the manuscript's `C`: the `L¹ → L^∞` bound for
  the unitary angular transform of `01-introduction.tex:91`,
  `|ẑ(ξ)| ≤ (2π)^{-3/2}‖z‖₁`.  Squaring it is what produces `C = (2π)^{-3}` in
  `lowHighConstant`.

  Stated in the **vector** form `(Σ_i|ẑ_i(ξ)|²)^{1/2} ≤ (2π)^{-3/2}∫‖z‖`, i.e.
  the triangle inequality for the vector-valued integral, and not componentwise:
  `01-introduction.tex:103` sums the squared component norms, so a componentwise
  bound by `∫‖z‖` would cost a spurious factor `3` and the constant of
  `lowHighSplit` would no longer be the manuscript's.

  The hypothesis is the manuscript's own, `k ∈ L¹` (`MemLp k 1 volume`, which
  is `Integrable k`), so that `angularFourier` — a pointwise Bochner integral —
  is honest and `∫‖k‖` is not a totalized `0`.  On such `k` that integral is
  `eLpNorm k 1 volume`, which is the spelling `lowHighSplit` uses because that
  inequality lives in `ℝ≥0∞`. -/
  fourierSupBound : ∀ k : SpatialField, MemLp k 1 volume →
    ∀ ξ : Space,
      Real.sqrt (∑ i : Fin 3, ‖angularFourier (fun x : Space => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2) ≤
        (2 * Real.pi) ^ (-(3 : ℝ) / 2) * ∫ x : Space, ‖k x‖

  /-- `04-whole-space.tex:241-248` eq:Rnegative-cutoff, in full:
  `‖k‖²_{Ḣ^{-1}} = ∫_{|ξ|<1}|ξ|^{-2}|k̂|² + ∫_{|ξ|≥1}|ξ|^{-2}|k̂|²`
  `≤ C‖k‖₁²∫_{|ξ|<1}|ξ|^{-2}dξ + ‖k‖₂² ≤ C'‖k‖₁² + ‖k‖₂²`, at every order of
  `SplitRange` and under the manuscript's own hypothesis `k ∈ L¹ ∩ L²`.

  That hypothesis is `L¹ ∩ L²` and **not** "smooth with compact support", and
  the difference is load-bearing: the field this inequality is applied to at
  `04-whole-space.tex:249` is `(1−χ_R)h_n`, which is Schwartz but has
  *unbounded* support.  A compactly supported version of this field would not
  close the diagonal argument.

  The left-hand side is `Data.lean:410` `homogeneousFourierENorm`, the literal
  Fourier integral, which its own docstring certifies as faithful on `L¹ ∩ L²`
  fields.  The constant is `lowHighConstant s`, i.e. the manuscript's `C'`
  written out; the high-frequency term carries the coefficient `1`, exactly as
  in the display.

  This is ledger item `⟪D01:lowHighSplit⟫`
  (`research/section4/STATEMENTS.md:806-807`). -/
  lowHighSplit : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
      MemLp k 1 volume → MemLp k 2 volume →
    homogeneousFourierENorm s k ^ (2 : ℝ) ≤
      ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
        eLpNorm k 2 volume ^ (2 : ℝ)

  -- ### The realization bridge
  /-- `02-preliminaries.tex:58-69` eq:homogeneous-realization applied to a
  smooth compactly supported real vector field: it *has* an order-`s`
  homogeneous datum, and the datum's `L²` norm is the Fourier quantity that
  eq:Rnegative-cutoff bounds.

  This field is what makes `lowHighSplit` usable.  `Data.lean` deliberately
  keeps two homogeneous objects apart: `homogeneousFourierENorm`
  (`:410`, a literal integral, the only thing an estimate can produce) and the
  datum infimum behind `IsHomogeneousSliceDatum` / `forceHomogeneousENorm`
  (`:367,390`, what `CompletedDenseHomogeneous` measures distance in).  Nothing
  in the tree connects them: `research/I03/COMPARISON.md:223,284` records that
  `IsHomogeneousDatum` and `forceHomogeneousENorm` have **zero** users outside
  `Contracts/V1/Data.lean`, and that since `forceHomogeneousENorm` is an
  infimum with `⨅ ∅ = ⊤` the two are unprovable until some witness exists.  This
  is that witness at the spatial level, and it is unit `U7c`'s core.

  Two clauses, both needed.  *Existence* is the witness; the *norm* clause says
  every datum of `k` has the same `ℝ≥0∞` norm, namely the Fourier quantity, and
  is what lets the diagonal argument bound `‖H − W‖ₑ` by `lowHighSplit` without
  first proving the datum unique.

  `-3/2 < s` is the temperedness range of `02-preliminaries.tex:66-69`; `s ≤ 0`
  is not needed for the *existence* of the datum but is carried so that the
  field composes with `lowHighSplit` without a second case split.  Hypothesis
  `L¹ ∩ L²` rather than compact support, for the reason recorded in
  `lowHighSplit`. -/
  lebesgueHomogeneousDatum : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
      MemLp k 1 volume → MemLp k 2 volume →
    (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
      ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
        ‖G‖ₑ = homogeneousFourierENorm s k

  /-- Linearity of the homogeneous realization in the one instance the diagonal
  argument needs (`04-whole-space.tex:249`, "`χ_Rh_n → h_n` in `Ḣ^{-1}`"): the
  difference of two fields carries the difference of their data, **with the
  physical-pairing integrability of `z` and `w` against Schwartz tests as side
  conditions**.

  ⚠ *The original statement of this field (no integrability hypotheses) was
  refuted* by lane 068's review (`research/B02/REVIEW_U6.md` §4, machine-checked;
  restated in the `NSFormalization.Section4.B02.LebesgueDatum` docstring).  Under
  `Data.lean:298`'s totalizing Bochner convention, a field pairing non-integrably
  with every Schwartz test satisfies `IsSliceDistribution z 0` vacuously and so
  carries the *zero* homogeneous datum at every order.  Taking
  `f = Σ_n 2^{-n}|x−q_n|^{-3}·1_{0<|x−q_n|<2^{-n}}` over an enumeration of `ℚ³`
  (a.e. finite by Borel–Cantelli, yet `∫_B f = ∞` on every ball, so `∫ ψ·f`
  totalizes to `0`) and `c` a nonzero real Schwartz function, `z := (f,0,0)`,
  `w := (f − c,0,0)` both carry `Z = W = 0` while `z − w = (c,0,0)` has a nonzero
  datum: a counterexample to the unhypothesised field.  No temperate-growth
  argument can recover it, because the existence of the distribution does not
  force `z` to be locally integrable when the pairing totalizes.

  The corrected field is the integrability-carrying form actually proved,
  `NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable`
  (= `D01.Homogeneous.isHomogeneousSliceDatum_sub`).  The two side conditions are
  `Integrable.mul_bdd` facts, discharged at the diagonal's single call site by
  `Section4/B02/Cutoff.lean`'s `integrable_schwartzVector` /
  `integrable_cutoffCompl_schwartzVector`; `Cutoff.lean`'s
  `spatialApproxHomogeneous_of` has been rewired to this form.  Together with the
  norm clause of `lebesgueHomogeneousDatum` this still replaces a uniqueness
  lemma: the *norm* of every datum of a given field is pinned, so `H − W` being
  *a* datum of `χ_Rh_n − h_n` suffices and no injectivity is invoked. -/
  homogeneousDatumSub : ∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
    IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume) →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ)) volume) →
      IsHomogeneousSliceDatum s (z - w) (Z - W)

  -- ### Stage 4: the physical cutoff, in `L¹` and `L²`
  /-- `04-whole-space.tex:249`.  "Since `(1−χ_R)h_n → 0` in both `L¹` and
  `L²`, eq:Rnegative-cutoff proves `χ_Rh_n → h_n` in `Ḣ^{-1}`."

  Both Lebesgue norms are asserted, for a Schwartz field, as `R → ∞`.  This is
  where `B02` parts company with `B01`: `B01`'s `cutoffApprox`
  (`04-whole-space.tex:237`) is a Leibniz estimate in `H^m`, which for `s < 0`
  bounds the wrong side — `(1+|ξ|²)^s ≤ |ξ|^{2s}`, so `‖z‖_{H^s} ≤ ‖z‖_{Ḣ^s}`
  and not the reverse — and the manuscript replaces it here by the pair
  `L¹`, `L²` fed through eq:Rnegative-cutoff.  No order `s` occurs in this
  field at all.

  `(1 − χ_R)h_n` is smooth but *not* compactly supported, so its Lebesgue norms
  are the genuine ones of a Schwartz field; the compactly supported half of the
  splitting is `χ_R h_n`, which `spatialApproxHomogeneous` returns. -/
  cutoffLebesgue : ∀ ψ : Fin 3 → SchwartzMap Space ℝ,
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff χ R x) • schwartzVector ψ x) 1 volume)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff χ R x) • schwartzVector ψ x) 2 volume)
      Filter.atTop (nhds 0)

  -- ### Stages 1-5 combined: real compact smooth spatial density in `Ḣ^s`
  /-- `04-whole-space.tex:249`.  "A diagonal choice gives compact-smooth
  density in this realization, without a dual Sobolev-embedding assumption.
  These constructions also prove the real vector-valued versions: take real
  parts of each component of the approximants."

  Physical `C_c^∞(R³;R³)` real vector fields are dense in `Ḣ^s(R³;R³)` for every
  `s` in `SplitRange`, measured by the datum norm — the homogeneous counterpart
  of `B01`'s `spatialApprox`, and the only spatial input
  `approxCompactHomogeneous` uses.  It is the conjunction of
  `annularRestriction`, `annularSmoothing`, `annularSchwartz`, `lowHighSplit`,
  `lebesgueHomogeneousDatum`, `homogeneousDatumSub` and `cutoffLebesgue`.

  The parenthesis "without a dual Sobolev-embedding assumption" is a claim about
  the *proof*, not about the statement: no hypothesis relating `Ḣ^s` to any
  `H^{s'}` occurs anywhere in this structure. -/
  spatialApproxHomogeneous : ∀ s : ℝ, SplitRange s →
      ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η

  -- ### Stage 6: the Bochner step, shared verbatim with `B01`
  /-- `04-whole-space.tex:251-260`.  "Write `X` for any of the preceding
  separable Hilbert spaces and `1 ≤ q < ∞`.  Given `b ∈ L^q((0,∞);X)`, first
  restrict it to `[1/N,N]` … strongly measurable functions can be approximated
  in `L^q` by finite simple functions `Σ_j 1_{E_j} b_j` … Each measurable
  `E_j ⊂ [1/N,N]` can be approximated in measure by a finite union of intervals
  lying in a fixed compact subset of `(0,∞)` … Smoothing their indicators by
  convolution gives `φ_j ∈ C_c^∞((0,∞))`."

  This is `research/B01/Spec.lean`'s field `temporalApprox`, restated with no
  change: `04-whole-space.tex:251` writes the step for "any of the preceding
  separable Hilbert spaces", `Data.lean:193-205` records that
  `bochnerDatumENorm` is literally one expression for both realizations, and
  `Data.lean:367-378` that `IsHomogeneousPath s` reads a force into the same
  `RealVectorSobolev s` that `IsSobolevPath s` does.  The ledger's instruction
  "formalise it once (B01/B02 share it)"
  (`research/section4/STATEMENTS.md:903-904`) is satisfied by one `def`;
  the duplication here is a Lake module-path artefact, not a second
  obligation. -/
  temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
      (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

  -- ### Packaging a separated sum as an element of `F_c`, homogeneously
  /-- `04-whole-space.tex:260`.  "Thus the finite sum `Σ_j φ_j(t)h_j(x)`
  approximates `b` and is jointly smooth with compact support strictly inside
  `R³ × (0,∞)`."

  `research/B01/Spec.lean`'s `separatedAssembly` with exactly one substitution,
  the one `research/B01/COMPARISON.md` §3 names: the datum-path conjunct is
  `IsHomogeneousPath s` instead of `IsSobolevPath s`, and the per-profile
  hypothesis is `IsHomogeneousSliceDatum` instead of `IsSobolevDatum`.
  `MemForceCompact` and the strong measurability are word-for-word the same and
  are proved once.

  ⚠ **Proved only on `-3/2 < s`, not the stated `∀ (s : ℝ)`** (lane 103; finding
  5-A of `research/B02/REVIEW_APPROX_COMPACT.md`).  The tree has
  `NSFormalization.Section4.B02.separatedAssembly` (`Section4/B02/SeparatedAssembly.lean:211`),
  which carries an extra hypothesis `hs : -3 / 2 < s` (needed by the uniqueness
  route through `D01`'s compact-datum constructor `homogeneousVectorDatum`, finite
  only at `s > -3/2`).  The verbatim `∀ s : ℝ` field is **not** proved and is
  near-vacuous for `s ≤ -3/2`.  No consumer is affected:
  `approxCompactHomogeneous` (`:607`) feeds it `SplitRange.1 = -3/2 < s` only.  A
  V2 contract should register `separatedAssembly` with the honest hypothesis
  `-3/2 < s` (lane 103's recommendation, `REMAINING_SPLIT.md` row 6), not `∀ s`. -/
  separatedAssembly : ∀ (s : ℝ) (J : ℕ) (φ : Fin J → ℝ → ℝ)
      (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
      (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
      (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) →
    MemForceCompact (separatedField φ h) ∧
      IsHomogeneousPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure

  -- ### The conclusion
  /-- `04-whole-space.tex:219` prop:Renergy, homogeneous clause: smooth compact
  forces are dense in the full Bochner space `L²(0,∞;Ḣ^{-1}(R³))`, stripped of
  the breakdown condition `T^ν_{max,R}(a,f) ≤ T` (which `R46` supplies from
  `R41D` by the two-radius argument of `04-whole-space.tex:262`).

  Stated at every `q ∈ [1,∞)` and every `s` in `SplitRange`, which is the exact
  range the manuscript's argument covers; `manuscriptHomogeneousApproximation`
  below is the single instance `R46` consumes, `q = 2`, `s = -1`.

  `04-whole-space.tex:228` — "The homogeneous norm here is a norm of the compact
  difference; the background itself need not belong to that homogeneous force
  space" — is respected by `Data.lean:732` `CompletedDenseVia`: the target
  ranges over the completion (`MemBochnerDatum`) while `S` stays a set of
  physical fields, and no membership is asserted of anything else. -/
  approxCompactHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, SplitRange s →
    CompletedDenseHomogeneous q s forceClassCompact

/-! ## 3. Derived statements -/

/-- The exact instance of `approxCompactHomogeneous` that `R46` consumes
(`research/section4/STATEMENTS.md:771-774, 831-836`): the manuscript's own
homogeneous clause, `q = 2` and `s = -1`, in `Data.lean`'s predicate.

Unlike `B01`'s `manuscriptApproximation` there is no threshold hypothesis to
carry: `s = -1 < -1/2 = s_2` holds outright, and
`research/section4/STATEMENTS.md:917-919` records that the homogeneous density
claim is a separate proof from the inhomogeneous one at the same `q`. -/
def manuscriptHomogeneousApproximation : Prop :=
  CompletedDenseHomogeneous 2 (-1) forceClassCompact

/-- The stage-6 predicate in isolation.  **This is
`BlowupDensity.B01.Draft.SeparatedTemporalDense` restated**, not a second
statement: `research/B01/Spec.lean` carries the same `def` and
`research/B01/COMPARISON.md` §3 asks `B02` to import rather than restate it.
Restating is forced here only because `research/` is not on the Lake module
path; at promotion time one of the two copies must be deleted, and the promoted
copy belongs next to `Data.lean`, not in either lane.

It mentions no realization, hence applies unchanged at `X = Ḣ^s(R³;R³)`
(`04-whole-space.tex:251`, "any of the preceding separable Hilbert spaces"). -/
def SeparatedTemporalDense (q : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

/-- The `B02` export shape asked for by `research/section4/STATEMENTS.md:831-836`
("exactly the same conclusion for `X = Ḣ^{-1}(R³;R³)`"): the homogeneous twin of
`B01`'s `SeparatedCompactDense`, exposing the separated sum
`Σ_{j≤J} φ_j(t)h_j(x)` that `R46`'s two-radius argument
(`04-whole-space.tex:262`) may inspect, together with its *homogeneous* datum
path.

It is a consequence of three fields and not an extra assumption:
`temporalApprox` supplies `J`, `φ` and coefficients `A' j`,
`spatialApproxHomogeneous` replaces each `A' j` by the homogeneous datum `A j`
of a physical `h j ∈ C_c^∞(R³;R³)`, and `separatedAssembly` turns the pair into
the member of `F_c`.  Stated as a `def` rather than a field for exactly that
reason. -/
def SeparatedCompactHomogeneousDense (q : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
      (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      (∀ j, ContDiff ℝ ∞ (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) ∧
      MemForceCompact (separatedField φ h) ∧
      IsHomogeneousPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

/-- `04-whole-space.tex:246-247` eq:Rnegative-cutoff at the manuscript's own
order, with both constants evaluated: `C = (2π)^{-3}` from `fourierSupBound` and
`∫_{|ξ|<1}|ξ|^{-2}dξ = 4π` from `lowFrequencyIntegral`, so the manuscript's `C'`
is `(2π)^{-3}·4π = 1/(2π²)`.  Recorded as a `def` so that the numeric claim is
checkable against `lowHighConstant (-1)` rather than buried in a docstring. -/
def rnegativeCutoffConstant : ℝ := 1 / (2 * Real.pi ^ 2)

/-- The existential form of the contract, the object a later
`verification/Contracts/V1/HomogeneousApprox.lean` would register. -/
def homogeneousApproxStatement : Prop := Nonempty HomogeneousApproxAPI

end BlowupDensity.B02.Draft
