import Contracts.V1.Data

/-! Stable specification for the **proved part** of the compact-force Bochner
approximation of Proposition 4.6.

Task `collaboration/tasks/B01.md`, graph node `B01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:313-320`), consumed by `R46`
(`research/section4/STATEMENTS.md:823-838`).  Version 1 fixes the fields of
`research/B01/Spec.lean`'s `BochnerApproxAPI` (`:191-360`) that are **proved** in
the tree, dropping the two fidelity-only spatial displays that are not
(see "Out of scope" below).  The mathematics is the approximation half of
`prop:Renergy` (`paper/sections/04-whole-space.tex:218-229`, proof at `:231-260`):
smooth compact forces `F_c` are dense in each full Bochner space
`L^q(0,∞;H^s(R³;R³))`, `q ∈ [1,∞)`, `s ∈ ℝ`.

## What is fixed

* `χ … chi_range`: the fixed spatial cutoff of `04-whole-space.tex:235`, one on
  the unit ball, zero outside the ball of radius two, `0 ≤ χ ≤ 1`.
* `spatialApprox`: stages 1–3 combined (`04-whole-space.tex:231-239,249`), real
  compact smooth spatial density in `H^s`.
* `temporalApprox`: stage 4, the Bochner step (`04-whole-space.tex:251-260`),
  shared verbatim with `B02`.
* `separatedAssembly`: the packaging of a finite separated sum as a member of
  `F_c` with its datum path (`04-whole-space.tex:260`).
* `approxCompact`: the conclusion, in `Data.CompletedDense`
  (`04-whole-space.tex:219`).
* `completionRepresentative … completionCongr`: the identification of the
  datum-path completion with the bundled Bochner space `bochnerSpace q s`.
* `compactSubsetForceR`: `F_c ⊆ F_R` (`04-whole-space.tex:183`).

## Out of scope, and asserted nowhere below

The two **fidelity-only** intermediate spatial displays of
`research/B01/Spec.lean` — `schwartzApprox` (`:225`, stage 1, Fourier
truncation/mollification through the `H^s` isometry) and `cutoffApprox` (`:257`,
stage 2, the `‖(1−χ_R)h_n‖_{H^m} → 0` limit) — are **not** registered here:
they are the manuscript's own intermediate steps, not proved in the tree, and
`spatialApprox` is the only spatial input the conclusion `approxCompact` uses.
Their absence weakens nothing that a consumer of `approxCompact` needs.

The ledger's `B01` export shape `SeparatedCompactDense`
(`research/B01/Spec.lean:405`, unit 10 of `research/section4/STATEMENTS.md:825-830`)
is **derivable** from `temporalApprox` (supplies `J`, `φ`, coefficients `A' j`),
`spatialApprox` (replaces each `A' j` by the datum `A j` of a physical
`h j ∈ C_c^∞(R³;R³)`) and `separatedAssembly` (turns the pair into the member of
`F_c` with its datum path), and for that reason is **not** packaged as a field
here, exactly as `Spec.lean` states it as a `def` rather than a structure field.

## Conventions

* Time is the first spacetime coordinate; `Space = EuclideanSpace ℝ (Fin 3)`.
* Force norms use `(0,∞)`: `forceTimeMeasure = volume.restrict (Ioi 0)`.
* `F_c` is `Data.MemForceCompact`; `supp` is `tsupport`.
* Every norm is the `ℝ≥0∞`-valued one of `Data.lean`.

`Contracts.V1.Data` supplies `SpatialField`, `SpaceTimeField`, `IsSobolevDatum`,
`IsSobolevPath`, `MemForceCompact`, `MemBochnerDatum`, `bochnerDatumENorm`,
`CompletedDense`, `forceClassCompact`, `forceClassR` and `forceTimeMeasure`
directly.  Only the three spec-local objects `separatedField`, `separatedPath`
(`research/B01/Spec.lean:140,147`) and `bochnerSpace` (`:158`) — which have no
`Data.lean` declaration — are restated verbatim below; `Bindings.BochnerPartial`
records by `rfl` that each is the implementation's. -/

noncomputable section

namespace BlowupDensity.Contracts.V1.BochnerPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Spec-local objects (`research/B01/Spec.lean:140,147,158`) -/

/-- `research/B01/Spec.lean:140`: the physical spacetime field assembled from
smooth compactly supported time factors `φ` and spatial profiles `h`. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- `research/B01/Spec.lean:147`: the order-`s` datum path of `separatedField φ h`,
when `A j` is the datum of `h j`. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-- `research/B01/Spec.lean:158`: the full Bochner space `L^q(0,∞;H^s(R³;R³))` as
a bundled Banach space, the completion object of `prop:Renergy`. -/
abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) := Lp (RealVectorSobolev s) q forceTimeMeasure

/-! ## 2. The contract -/

/-- The **proved** fields of the approximation half of Proposition 4.6
(`prop:Renergy`, `paper/sections/04-whole-space.tex:218-229`, proof at
`:231-260`) on the inhomogeneous completed force space, in exactly the form `R46`
consumes (`research/section4/STATEMENTS.md:823-830`).

This is `research/B01/Spec.lean`'s `BochnerApproxAPI` with the two fidelity-only
spatial displays `schwartzApprox` and `cutoffApprox` removed; see the module
docstring.  No field is a hypothesis about an unspecified proposition, and no
field is `True`, `∃ x, True` or any similar placeholder. -/
structure BochnerPartialAPI where
  -- ### The fixed spatial cutoff, `04-whole-space.tex:235`
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

  -- ### Stages 1–3 combined: real compact smooth spatial density
  /-- `04-whole-space.tex:239` together with `:249`.  Physical `C_c^∞(R³;R³)` real
  vector fields are dense in `H^s(R³;R³)` for every real `s`; the only spatial
  input `approxCompact` uses. -/
  spatialApprox : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsSobolevDatum s h H ∧ ‖H - A‖ₑ < η

  -- ### Stage 4: the Bochner step, shared with `B02`
  /-- `04-whole-space.tex:251-260`.  Separated finite sums with `C_c^∞((0,∞))`
  time factors are dense in the datum-path Bochner space, on the datum carrier
  and not on a realization, so `B02` uses this field verbatim at
  `X = Ḣ^{-1}(R³;R³)`. -/
  temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
      (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

  -- ### Packaging a separated sum as an element of `F_c`
  /-- `04-whole-space.tex:260`.  Turns the pair (smooth compact time factors,
  smooth compact spatial profiles) into a single member of `F_c` whose `Data.lean`
  datum path is the corresponding finite sum, with the strong measurability that
  `CompletedDenseVia` requires. -/
  separatedAssembly : ∀ (s : ℝ) (J : ℕ) (φ : Fin J → ℝ → ℝ)
      (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
      (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
      (∀ j, IsSobolevDatum s (h j) (A j)) →
    MemForceCompact (separatedField φ h) ∧
      IsSobolevPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure

  -- ### The conclusion
  /-- `04-whole-space.tex:219` prop:Renergy, approximation half: smooth compact
  forces are dense in each full Bochner space `L^q(0,∞;H^s(R³))`, `q ∈ [1,∞)`,
  `s ∈ ℝ`. -/
  approxCompact : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ,
    CompletedDense q s forceClassCompact

  -- ### Identification of the completion object
  /-- Every element of the bundled Bochner space `L^q(0,∞;H^s(R³;R³))` is a datum
  path in the sense of `Data.MemBochnerDatum`. -/
  completionRepresentative : ∀ (q : ℝ≥0∞) (s : ℝ) (u : bochnerSpace q s),
    MemBochnerDatum q s (u : ℝ → RealVectorSobolev s)
  /-- Conversely every datum path is represented by an element of the bundled
  space, so quantifying `approxCompact` over paths misses no element of the
  completion. -/
  completionSurjective : ∀ (q : ℝ≥0∞) (s : ℝ) (b : ℝ → RealVectorSobolev s),
    MemBochnerDatum q s b →
      ∃ u : bochnerSpace q s, (u : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure] b
  /-- The two norms agree: `Data.bochnerDatumENorm` on a representative is the
  Banach norm of the class. -/
  completionNorm : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : ℝ) (u : bochnerSpace q s),
    bochnerDatumENorm q s (u : ℝ → RealVectorSobolev s) = ‖u‖ₑ
  /-- `bochnerDatumENorm` only sees the a.e. class.  Together with the two
  previous fields this is the full identification of the path model with
  `bochnerSpace q s`. -/
  completionCongr : ∀ (q : ℝ≥0∞) (s : ℝ) (b c : ℝ → RealVectorSobolev s),
    b =ᵐ[forceTimeMeasure] c → bochnerDatumENorm q s b = bochnerDatumENorm q s c

  -- ### `F_c ⊆ F_R`
  /-- `04-whole-space.tex:183`, "Define the following two subclasses of `F_R`":
  every `f ∈ F_c` satisfies `eq:Rclasses` (`02-preliminaries.tex:17`), which
  `cor:Rclasses` (`:194-196`) presupposes. -/
  compactSubsetForceR : forceClassCompact ⊆ forceClassR

end BlowupDensity.Contracts.V1.BochnerPartial
