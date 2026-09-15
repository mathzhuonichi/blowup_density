import Contracts.V1.Data
import Contracts.V1.BochnerPartial

/-! Stable specification for the **proved part** of the homogeneous
`L²(0,∞;Ḣ^{-1}(R³))` approximation clause of Proposition 4.6.

Task `collaboration/tasks/B02.md`, graph node `B02`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:322-329`), consumed by `R46`
(`research/section4/STATEMENTS.md:831-836`).  Version 1 fixes the fields of
`research/B02/Spec.lean`'s `HomogeneousApproxAPI` (`:274-608`) that are **proved**
in the tree by the eight modules
`formalization/NSFormalization/Section4/B02/{LowFrequency,Annular,LowHigh,Cutoff,
LebesgueDatum,AnnularSchwartz,AnnularReal,Remaining}.lean`, dropping the three
obligations that are not yet proved (see "Out of scope" below).  The mathematics
is the homogeneous half of `prop:Renergy`
(`paper/sections/04-whole-space.tex:218-229`, homogeneous proof paragraph at
`:241-249`, Bochner paragraph at `:251-260`): smooth compact forces `F_c` are
dense in the completed force space `L²(0,∞;Ḣ^{-1}(R³))`, in the realization
`ĥ = |ξ|^{-s} G` of `02-preliminaries.tex:58-69`.  The manuscript's argument runs
on `-3/2 < s ≤ 0` (`SplitRange`), with `s = -1` the case `R46` consumes; see
`research/B02/Spec.lean`'s "Which `s` the argument covers".

## What is fixed (the 16 proved fields)

* `χ … chi_range`: the fixed spatial cutoff of `04-whole-space.tex:235`, reused
  by the homogeneous paragraph at `:249`; one on the unit ball, zero outside the
  ball of radius two, `0 ≤ χ ≤ 1`.  Bound to the **same** vendor cutoff
  `NavierStokesR3.ComparisonCutoffs.baseCutoff` as `B01.bochner_partial`
  (`Bindings/BochnerPartial.lean:66`), so a joint consumer (`R46`) sees one
  cutoff across `B01` and `B02`.
* `annularRestriction`, `annularSmoothing`: stage 1, `04-whole-space.tex:241`,
  restrict to `1/n < |ξ| < n` then mollify inside a slightly larger annulus.
* `annularSchwartz`: stage 2, `04-whole-space.tex:241`, `ĥ_n = |ξ|^{-s}G_n` is
  a real vector Schwartz field.
* `lowFrequencyIntegrable`, `lowFrequencyIntegral`, `fourierSupBound`,
  `lowHighSplit`: stage 3, eq:Rnegative-cutoff (`04-whole-space.tex:241-248`,
  label `:247`), the low/high split `‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²` with its
  constant `(2π)^{-3}·∫_{|ξ|<1}|ξ|^{2s}` written out.
* `lebesgueHomogeneousDatum`, `homogeneousDatumSub`: the realization bridge
  connecting the Fourier quantity `homogeneousFourierENorm` that the estimate
  produces to the datum norm `‖·‖ₑ` of an `IsHomogeneousSliceDatum` that the
  conclusion measures distance in (`research/I03/COMPARISON.md` U7c).
* `cutoffLebesgue`, `spatialApproxHomogeneous`: stage 4
  (`04-whole-space.tex:249`), the physical cutoff `(1-χ_R)h_n → 0` in `L¹` and
  `L²`, and the diagonal conclusion: physical `C_c^∞(R³;R³)` fields are dense in
  `Ḣ^s` for `s ∈ SplitRange`, the only spatial input the conclusion uses.
* `temporalApprox`: stage 6 (`04-whole-space.tex:251-260`), the Bochner step,
  **shared verbatim with `B01`** — this is `B01.bochner_partial`'s
  `temporalApprox` field on the same datum carrier `RealVectorSobolev s`, so the
  spec-local separated datum path is `Contracts.V1.BochnerPartial.separatedPath`,
  reused rather than restated.

## ⚠ The `homogeneousDatumSub` caveat (do not weaken to the hypothesis-free form)

`homogeneousDatumSub` is registered **only** in its integrability-carrying form,
copied token-for-token from the amended spec field
(`research/B02/Spec.lean:490-496`).  Its two side conditions — that `z` and `w`
pair integrably against every Schwartz test — are essential, not decoration.

*The original statement of this field (no integrability hypotheses) was refuted*
by lane 068's review (`research/B02/REVIEW_U6.md` §4, machine-checked; restated
in the `NSFormalization.Section4.B02.LebesgueDatum` docstring).  Under
`Data.lean:298`'s totalizing Bochner convention, a field pairing non-integrably
with every Schwartz test satisfies `IsSliceDistribution z 0` vacuously and so
carries the *zero* homogeneous datum at every order.  Taking
`f = Σ_n 2^{-n}|x−q_n|^{-3}·1_{0<|x−q_n|<2^{-n}}` over an enumeration of `ℚ³`
(a.e. finite by Borel–Cantelli, yet `∫_B f = ∞` on every ball, so `∫ ψ·f`
totalizes to `0`) and `c` a nonzero real Schwartz function, `z := (f,0,0)`,
`w := (f − c,0,0)` both carry `Z = W = 0` while `z − w = (c,0,0)` has a nonzero
datum: a counterexample to the unhypothesised field.  No temperate-growth
argument recovers it.  The corrected field is discharged by
`NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable`; its two
side conditions are met at the diagonal's single call site by `Cutoff.lean`'s
`integrable_schwartzVector` / `integrable_cutoffCompl_schwartzVector`.

## Out of scope, and asserted nowhere below

Three obligations of `research/B02/Spec.lean`'s `HomogeneousApproxAPI` are
**deliberately absent** (the `M` rows of `research/B02/REMAINING_SPLIT.md`, none
proved in the tree on this branch):

* `separatedAssembly` (`Spec.lean:582`): packaging a finite separated sum as a
  member of `F_c` with an `IsHomogeneousPath` datum path.  Its
  realization-dependent conjunct is the homogeneous twin of
  `Section4/B01/Separated.lean:182 isSobolevPath_separated`, which needs a
  scalar-`smul`/finite-`sum` additivity combinator for `IsHomogeneousSliceDatum`
  that does not exist (only `isHomogeneousSliceDatum_sub`, the difference of two,
  `HomogeneousWitness.lean:585`).
* `annularPathApprox` (`Spec.lean:337`): the path-level reading of stage 1.  It
  is **not** a step of the manuscript's own proof — which performs the Bochner
  reduction first (`04-whole-space.tex:251`) and truncates the finitely many
  fibre values afterwards — feeds nothing, and needs a measurable-in-`t`
  selection of the annular truncation plus a path-level dominated-convergence
  argument, neither of which exists.
* `approxCompactHomogeneous` (`Spec.lean:607`): the conclusion,
  `Data.CompletedDenseHomogeneous`.  It depends on `separatedAssembly`, and
  `B01`'s `approxCompact` is monolithic (it applies the source density theorem
  directly and does **not** glue `temporalApprox` + `spatialApprox` +
  `separatedAssembly`), with no homogeneous analogue of that source theorem, so
  it cannot be reused or parametrized and must be assembled fresh.

Also deliberately absent, because `research/B01/COMPARISON.md` §3 assigns them to
`B01` and they are realization-independent: `forceClassCompact ⊆ forceClassR`,
and the identification of the datum-path completion with the bundled Bochner
space.  `B02` consumes `B01.bochner_partial`'s `compactSubsetForceR` and
`completion*` fields.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder.

## Conventions

* Time is the first spacetime coordinate; `Space = EuclideanSpace ℝ (Fin 3)`.
* Fourier is the manuscript's unitary angular transform
  `ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx`, in Lean `NSFormalization.Source.angularFourier`.
* `F_c` is `Data.MemForceCompact`; every norm is the `ℝ≥0∞`-valued one of `Data.lean`.

`Contracts.V1.Data` supplies `SpatialField`, `IsHomogeneousSliceDatum`,
`IsHomogeneousPath`, `homogeneousFourierENorm`, `MemBochnerDatum`,
`bochnerDatumENorm`, `MemForceCompact`, `forceClassCompact` and `forceTimeMeasure`
directly, and `Contracts.V1.BochnerPartial` supplies the spec-local
`separatedPath` (shared with `B01`, reused not restated).  The nine other
spec-local objects `frequencyAnnulus`, `closedFrequencyAnnulus`, `IsAnnularDatum`,
`IsAnnularRestriction`, `IsAnnularSupported`, `scaledCutoff`, `schwartzVector`,
`lowHighConstant`, `SplitRange` (`research/B02/Spec.lean:155-237`) — which have no
`Data.lean` declaration — are restated verbatim below; `Bindings.HomogeneousPartial`
records by `rfl` that each is the implementation's. -/

noncomputable section

namespace BlowupDensity.Contracts.V1.HomogeneousPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev (FourierData)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Spec-local objects (`research/B02/Spec.lean:155-237`) -/

/-- `research/B02/Spec.lean:155`, `04-whole-space.tex:241` "`1/n < |ξ| < n`": the
open frequency annulus on which the manuscript's first truncation lives. -/
def frequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ < ‖ξ‖ ∧ ‖ξ‖ < R}

/-- `research/B02/Spec.lean:161`, `04-whole-space.tex:241` "a slightly larger
annular cutoff": the closed annulus containing the support of the mollified
datum. -/
def closedFrequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R}

/-- `research/B02/Spec.lean:172`, `04-whole-space.tex:241`: `Z` is an order-`s`
datum whose three components are (a.e.) smooth functions supported in the closed
annulus `δ ≤ |ξ| ≤ R`, i.e. one of the manuscript's `G_n ∈ C_c^∞(R³∖{0})`. -/
def IsAnnularDatum {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∃ g : Fin 3 → Space → ℂ,
    (∀ i, ContDiff ℝ ∞ (g i)) ∧
    (∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R) ∧
    (∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i)

/-- `research/B02/Spec.lean:181`, `04-whole-space.tex:241`: `Z` is the restriction
of the datum `A` to the open annulus `δ < |ξ| < R`. -/
def IsAnnularRestriction {s : ℝ} (δ R : ℝ) (A Z : RealVectorSobolev s) : Prop :=
  ∀ i, ((Z i : FourierData) : Space → ℂ)
    =ᵐ[volume] (frequencyAnnulus δ R).indicator ((A i : FourierData) : Space → ℂ)

/-- `research/B02/Spec.lean:190`, `04-whole-space.tex:241`: the datum of `Z`
vanishes a.e. off the open annulus `δ < |ξ| < R`; the hypothesis the
mollification step consumes. -/
def IsAnnularSupported {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, ∀ᵐ ξ : Space ∂volume,
    ξ ∉ frequencyAnnulus δ R → ((Z i : FourierData) : Space → ℂ) ξ = 0

/-- `research/B02/Spec.lean:199`, `04-whole-space.tex:235` `χ_R(x) = χ(x/R)`: the
dilated spatial cutoff, `R⁻¹ • x` so that no positivity of `R` is needed to form
the expression; `cutoffLebesgue` takes `R → ∞`.  Same object as
`research/B01/Spec.lean`'s `scaledCutoff`. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) : Space → ℝ := fun x => χ (R⁻¹ • x)

/-- `research/B02/Spec.lean:206`, `04-whole-space.tex:249` "take real parts of each
component": the real Euclidean three-vector field assembled componentwise from
three real scalar Schwartz components.  Same object as
`research/B01/Spec.lean`'s `schwartzVector`. -/
def schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) : SpatialField :=
  fun x => WithLp.toLp 2 (fun i => ψ i x)

/-- `research/B02/Spec.lean:231`, `04-whole-space.tex:246-247` eq:Rnegative-cutoff,
the constant made explicit: `C·∫_{|ξ|<1}|ξ|^{2s}dξ` with `C = (2π)^{-3}` the
square of the `L¹ → L^∞` constant of the unitary angular transform.  At `s = -1`
in dimension three `∫_{|ξ|<1}|ξ|^{-2}dξ = 4π`, so `lowHighConstant (-1) = 1/(2π²)`. -/
def lowHighConstant (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ)) * ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)

/-- `research/B02/Spec.lean:237`, `04-whole-space.tex:241,246,249`: the range of
orders on which the manuscript's homogeneous argument runs, `-3/2 < s ≤ 0`;
`s = -1` is the manuscript's case. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-! ## 2. The contract -/

/-- The **proved** fields of the homogeneous clause of Proposition 4.6
(`prop:Renergy`, `paper/sections/04-whole-space.tex:218-229`, homogeneous proof
paragraph at `:241-249`, Bochner paragraph at `:251-260`) on the completed force
space `L²(0,∞;Ḣ^{-1}(R³))`, in the form `R46` consumes
(`research/section4/STATEMENTS.md:831-836`).

This is `research/B02/Spec.lean`'s `HomogeneousApproxAPI` with the three not-yet
-proved obligations `separatedAssembly`, `annularPathApprox` and
`approxCompactHomogeneous` removed; see the module docstring for each reason.
The `homogeneousDatumSub` field is present **only** in its integrability-carrying
form — the hypothesis-free form is false (see the ⚠ note in the module
docstring).  No field is a hypothesis about an unspecified proposition, and no
field is `True`, `∃ x, True` or any similar placeholder. -/
structure HomogeneousApproxPartialAPI where
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

  -- ### Stage 1a: restriction to a compact annulus (`04-whole-space.tex:241`)
  /-- `research/B02/Spec.lean:302`.  "One first restricts to `1/n < |ξ| < n`, with
  `L²` error tending to zero."  Every real `s`; the inner radius is positive,
  the manuscript's "supported away from `0`". -/
  annularRestriction : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (δ R : ℝ) (Z : RealVectorSobolev s),
      0 < δ ∧ δ < R ∧ IsAnnularRestriction δ R A Z ∧ ‖Z - A‖ₑ < η

  -- ### Stage 1b: mollification inside a slightly larger annulus
  /-- `research/B02/Spec.lean:314`.  "… and then smooths each restricted function
  with a sufficiently small mollification radius and a slightly larger annular
  cutoff."  The conclusion is `G_n ∈ C_c^∞(R³∖{0})`, an `IsAnnularDatum δ' R'`
  with `0 < δ' < δ` and `R < R'`.  Every real `s`. -/
  annularSmoothing : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
      ∀ (Z : RealVectorSobolev s), IsAnnularSupported δ R Z →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (δ' R' : ℝ) (W : RealVectorSobolev s),
      0 < δ' ∧ δ' < δ ∧ R < R' ∧ IsAnnularDatum δ' R' W ∧ ‖W - Z‖ₑ < η

  -- ### Stage 2: `ĥ_n = |ξ|^{-s}G_n` is Schwartz (`04-whole-space.tex:241`)
  /-- `research/B02/Spec.lean:362`.  "Set `ĥ_n = |ξ|G_n`.  Again `h_n` is Schwartz
  and `h_n → h` in `Ḣ^{-1}`."  From an annular smooth compactly supported datum
  `W`, the field it realizes is a real vector Schwartz field.  Every real `s`;
  reality is automatic from `RealVectorSobolev s` being the conjugate-reflection
  subspace (`04-whole-space.tex:249`). -/
  annularSchwartz : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
      ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
    ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W

  -- ### Stage 3: eq:Rnegative-cutoff (`04-whole-space.tex:241-248`)
  /-- `research/B02/Spec.lean:370`, `04-whole-space.tex:249` "The integral at the
  origin is finite in dimension three": the low-frequency weight is integrable on
  the unit ball exactly when `2s > -3`.  This is the `-3/2 < s` half of
  `SplitRange`. -/
  lowFrequencyIntegrable : ∀ s : ℝ, -3 / 2 < s →
    IntegrableOn (fun ξ : Space => ‖ξ‖ ^ (2 * s)) (Metric.ball (0 : Space) 1) volume

  /-- `research/B02/Spec.lean:378`, `04-whole-space.tex:246`: the factor
  `∫_{|ξ|<1}|ξ|^{-2}dξ` of eq:Rnegative-cutoff evaluated in dimension three at the
  manuscript's order `s = -1`: `∫_0^1 r^{-2}·4πr²dr = 4π`.  Turns the unnamed `C'`
  into `(2π)^{-3}·4π = 1/(2π²)` (`lowHighConstant (-1)`). -/
  lowFrequencyIntegral :
    (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * (-1 : ℝ))) = 4 * Real.pi

  /-- `research/B02/Spec.lean:397`, `04-whole-space.tex:246`, the manuscript's `C`:
  the `L¹ → L^∞` bound `|ẑ(ξ)| ≤ (2π)^{-3/2}‖z‖₁` for the unitary angular
  transform of `01-introduction.tex:91`, in the vector form
  `(Σ_i|ẑ_i(ξ)|²)^{1/2} ≤ (2π)^{-3/2}∫‖z‖`.  Squaring it produces `C = (2π)^{-3}`
  in `lowHighConstant`.  Hypothesis `k ∈ L¹` so that `angularFourier` is an honest
  Bochner integral. -/
  fourierSupBound : ∀ k : SpatialField, MemLp k 1 volume →
    ∀ ξ : Space,
      Real.sqrt (∑ i : Fin 3, ‖angularFourier (fun x : Space => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2) ≤
        (2 * Real.pi) ^ (-(3 : ℝ) / 2) * ∫ x : Space, ‖k x‖

  /-- `research/B02/Spec.lean:421`, `04-whole-space.tex:241-248` eq:Rnegative-cutoff
  in full: `‖k‖²_{Ḣ^{-1}} ≤ C'‖k‖₁² + ‖k‖₂²` at every order of `SplitRange` under
  the manuscript's own hypothesis `k ∈ L¹ ∩ L²` (**not** compact support: the
  field it is applied to at `:249`, `(1−χ_R)h_n`, has unbounded support).  The
  left-hand side is `Data.homogeneousFourierENorm`, the literal Fourier integral;
  the constant is `lowHighConstant s`.  Ledger item `⟪D01:lowHighSplit⟫`
  (`research/section4/STATEMENTS.md:806-807`). -/
  lowHighSplit : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
      MemLp k 1 volume → MemLp k 2 volume →
    homogeneousFourierENorm s k ^ (2 : ℝ) ≤
      ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
        eLpNorm k 2 volume ^ (2 : ℝ)

  -- ### The realization bridge (`02-preliminaries.tex:58-69`)
  /-- `research/B02/Spec.lean:454`.  eq:homogeneous-realization applied to a smooth
  compactly supported real vector field: it *has* an order-`s` homogeneous datum,
  and every datum's `L²` norm is the Fourier quantity `homogeneousFourierENorm`
  that eq:Rnegative-cutoff bounds.  This is unit `U7c`, the witness that connects
  the two homogeneous objects `Data.lean` keeps apart.  `-3/2 < s` is the
  temperedness range; `s ≤ 0` is carried so the field composes with `lowHighSplit`
  without a second case split.  The Lean hypothesis is `MemLp k 1 ∧ MemLp k 2`
  (`L¹ ∩ L²`) with `SplitRange s`, **not** compact support: hypothesis `L¹ ∩ L²`
  rather than compact support, for the reason recorded in `lowHighSplit`
  (the field it is applied to at `04-whole-space.tex:249`, `(1−χ_R)h_n`, is
  Schwartz with unbounded support).  The smooth compactly supported vector field
  is only the manuscript's phrasing of eq:homogeneous-realization; the statement
  quantifies over every `L¹ ∩ L²` field. -/
  lebesgueHomogeneousDatum : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
      MemLp k 1 volume → MemLp k 2 volume →
    (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
      ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
        ‖G‖ₑ = homogeneousFourierENorm s k

  /-- `research/B02/Spec.lean:490`.  Linearity of the homogeneous realization in the
  one instance the diagonal argument needs (`04-whole-space.tex:249`,
  "`χ_Rh_n → h_n` in `Ḣ^{-1}`"): the difference of two fields carries the
  difference of their data, **with the physical-pairing integrability of `z` and
  `w` against Schwartz tests as side conditions**.

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
  argument recovers it.

  The corrected field is the integrability-carrying form actually proved,
  `NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable`; the two
  side conditions are `Integrable.mul_bdd` facts, discharged at the diagonal's
  single call site by `Section4/B02/Cutoff.lean`'s `integrable_schwartzVector` /
  `integrable_cutoffCompl_schwartzVector`.  Together with the norm clause of
  `lebesgueHomogeneousDatum` this replaces a uniqueness lemma.

  In this integrability-carrying form the field is the **same proposition** as the
  already-registered `D01.datum_lemmas` field `isHomogeneousSliceDatum_sub`
  (`Contracts/V1/DatumLemmas.lean:458` — same four hypotheses, same conclusion, same
  binder order; `Section4/B02/isHomogeneousSliceDatum_sub_of_integrable` is a
  one-line re-export of the same `Section4/D01/HomogeneousWitness.lean` lemma
  `D01.datum_lemmas` binds).  It is kept here because `research/B02/Spec.lean:490`
  lists it as a `B02` obligation and `REVIEW_REMAINING.md` §5's first hard
  requirement presupposes registering it — not as a new result — so a `B02`
  consumer need not also depend on `D01.datum_lemmas`. -/
  homogeneousDatumSub : ∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
    IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume) →
    (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable (fun x : Space => ψ x * ((w x i : ℝ) : ℂ)) volume) →
      IsHomogeneousSliceDatum s (z - w) (Z - W)

  -- ### Stage 4: the physical cutoff, in `L¹` and `L²` (`04-whole-space.tex:249`)
  /-- `research/B02/Spec.lean:513`.  "Since `(1−χ_R)h_n → 0` in both `L¹` and `L²`,
  eq:Rnegative-cutoff proves `χ_Rh_n → h_n` in `Ḣ^{-1}`."  Both Lebesgue norms are
  asserted, for a Schwartz field, as `R → ∞`.  `(1 − χ_R)h_n` is smooth but *not*
  compactly supported, so its Lebesgue norms are the genuine ones of a Schwartz
  field.  No order `s` occurs in this field. -/
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
  /-- `research/B02/Spec.lean:539`, `04-whole-space.tex:249`.  "A diagonal choice
  gives compact-smooth density in this realization, without a dual
  Sobolev-embedding assumption. … take real parts of each component."  Physical
  `C_c^∞(R³;R³)` fields are dense in `Ḣ^s(R³;R³)` for every `s` in `SplitRange`,
  measured by the datum norm — the homogeneous counterpart of `B01`'s
  `spatialApprox`, and the only spatial input `approxCompactHomogeneous` would
  use. -/
  spatialApproxHomogeneous : ∀ s : ℝ, SplitRange s →
      ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η

  -- ### Stage 6: the Bochner step, shared verbatim with `B01`
  /-- `research/B02/Spec.lean:563`, `04-whole-space.tex:251-260`.  "Write `X` for
  any of the preceding separable Hilbert spaces and `1 ≤ q < ∞`. …" — the Bochner
  step, stated on the datum carrier `RealVectorSobolev s`, not on a realization,
  so it is `B01.bochner_partial`'s `temporalApprox` **verbatim**, at
  `X = Ḣ^{-1}(R³;R³)`.  The separated datum path is
  `Contracts.V1.BochnerPartial.separatedPath`, shared with `B01` (the ledger's
  "formalise it once (B01/B02 share it)", `STATEMENTS.md:903-904`), reused here
  rather than restated. -/
  temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
      (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s
        (BlowupDensity.Contracts.V1.BochnerPartial.separatedPath φ A - b) < η

end BlowupDensity.Contracts.V1.HomogeneousPartial
