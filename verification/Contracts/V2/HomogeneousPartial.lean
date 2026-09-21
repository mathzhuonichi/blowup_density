import Contracts.V1.HomogeneousPartial

/-! Version 2 of the **proved part of B02's homogeneous approximation interface**:
the version-one record `HomogeneousApproxPartialAPI`
(`Contracts/V1/HomogeneousPartial.lean`), extended by the two `Section4/B02`
theorems that lanes 103 and 110 added after version one was frozen.

Task `collaboration/tasks/B02.md`, graph node `B02`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:322-329`), consumed by `R46`
(`research/section4/STATEMENTS.md:831-836`).  `research/B02/Spec.lean` bundles the
whole obligation as `HomogeneousApproxAPI` (`:274-608`); version one registered its
16 proved fields and, in its "Out of scope" list, named the three then-unproved
obligations `separatedAssembly`, `annularPathApprox`, `approxCompactHomogeneous`.
Lanes 103 (`Section4/B02/SeparatedAssembly.lean`) and 110
(`Section4/B02/ApproxCompact.lean`) have since discharged two of the three, so
version two records them.

## Why a new version

`Contracts.V1.HomogeneousPartial` deliberately stops before the conclusion: its
module docstring lists `separatedAssembly` (`Spec.lean:593`), `annularPathApprox`
(`Spec.lean:337`) and `approxCompactHomogeneous` (`Spec.lean:618`) among the
excluded fields, "none proved in the tree on this branch".  That is no longer true
of two of them:

* `NSFormalization.Section4.B02.separatedAssembly` (`SeparatedAssembly.lean:211`,
  lane 103) packages a finite separated sum as a member of `F_c` with an
  `IsHomogeneousPath` datum path — the last spatial ingredient of the diagonal
  argument;
* `NSFormalization.Section4.B02.approxCompactHomogeneous` (`ApproxCompact.lean:229`,
  lane 110) glues stages together into the conclusion,
  `Data.CompletedDenseHomogeneous` — the last field on the manuscript's homogeneous
  critical chain.

`research/B02/REVIEW_APPROX_COMPACT.md` §5.3 confirms there is no technical blocker
to a V2 registering exactly these two.

## What changed, exactly

`HomogeneousApproxPartialV2API` extends
`Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI` unchanged and adds
**two** fields:

* `separatedAssembly` (`research/B02/Spec.lean:593`; `04-whole-space.tex:260`;
  `research/section4/STATEMENTS.md:831-836`).  It is `research/B01/Spec.lean`'s
  `separatedAssembly` with the one substitution `research/B01/COMPARISON.md` §3
  names — `IsHomogeneousPath`/`IsHomogeneousSliceDatum` for
  `IsSobolevPath`/`IsSobolevDatum` — and it reuses the **same** spec-local objects
  `separatedField`, `separatedPath` as `B01` (`Contracts.V1.BochnerPartial`; the
  ledger's "formalise it once", `STATEMENTS.md:903-904`), so nothing is restated.

  ⚠ **Registered on `-3/2 < s`, not the spec's `∀ (s : ℝ)`.**  The tree's theorem
  (`SeparatedAssembly.lean:211`) carries an extra hypothesis `hs : -3/2 < s`,
  needed by the uniqueness route through `D01`'s compact-datum constructor
  `homogeneousVectorDatum`, finite only at `s > -3/2`.  The verbatim `∀ s : ℝ`
  form of `Spec.lean:593` is **not proved** and is near-vacuous for `s ≤ -3/2`
  (`research/B02/REVIEW_APPROX_COMPACT.md` finding 5-A; lane 103's recommendation,
  `REMAINING_SPLIT.md` row 6).  This is the honest hypothesis and the one the
  theorem proves; no consumer is weakened, because `approxCompactHomogeneous` feeds
  it only `SplitRange.1 = -3/2 < s`.  Every other token matches `Spec.lean:593`.

* `approxCompactHomogeneous` (`research/B02/Spec.lean:618`; `04-whole-space.tex:219`
  prop:Renergy homogeneous clause, with `:228` the compact-difference caveat;
  `research/section4/STATEMENTS.md:831-836`).  The conclusion:
  `Data.CompletedDenseHomogeneous q s forceClassCompact` for every `q ∈ [1,∞)` and
  every `s` in `SplitRange`, `q = 2`/`s = -1` being the instance `R46` consumes.
  The tree's theorem (`ApproxCompact.lean:229`) is **definitionally equal** to
  `Spec.lean:618` — kernel-checked by `rfl` in `research/B02/axioms_approx_compact.lean`
  — modulo three benign token differences: the `CompletedDenseHomogeneous` `abbrev`
  (`Data.lean:752` for `CompletedDenseVia q s (IsHomogeneousPath s)`) and the two
  sanctioned `formalization/` restatements `SplitRange` and `forceClassCompact`.
  So it is registered here **verbatim** (`Spec.lean:618` token-for-token in the
  `Data`/`HomogeneousPartial` vocabulary), and the binding discharges it directly.

No version-one field is removed, weakened, renamed or restated; `extends` makes
that structural.  `Bindings.homogeneousPartial_of_v2` exports the version-one
record, and `Tests.checkedHomogeneousPartial` keeps running against the untouched
`Bindings.homogeneousPartial`.

## Still out of scope: `annularPathApprox`

`annularPathApprox` (`research/B02/Spec.lean:337`) remains **excluded** and is
asserted nowhere below: no proof exists anywhere in the tree
(`research/B02/REVIEW_APPROX_COMPACT.md` §5.1;
`Contracts/V1/HomogeneousPartial.lean:208-209` already names it unproved), it is
**not** a step of the manuscript's own proof — which performs the Bochner reduction
first (`04-whole-space.tex:251`) and truncates the finitely many fibre values
afterwards — it feeds nothing, and `approxCompactHomogeneous` does **not** route
through it (`research/B02/Spec.lean:330-337`).  It would need a measurable-in-`t`
selection of the annular truncation plus a path-level dominated-convergence
argument, neither of which exists.

## No new restated objects

Both new fields are stated entirely in vocabulary already fixed by version one and
its imports, so this file restates **nothing** and needs no new `rfl` bridge:
`Contracts.V1.Data` supplies `SpatialField`, `IsHomogeneousSliceDatum`,
`IsHomogeneousPath`, `MemForceCompact`, `forceTimeMeasure`, `forceClassCompact` and
the `CompletedDenseHomogeneous` `abbrev`; `Contracts.V1.BochnerPartial` supplies the
shared `separatedField`/`separatedPath` (`Bindings/BochnerPartial.lean:47-54`
records both `= NSFormalization.Section4.B01.·` by `rfl`);
`Contracts.V1.HomogeneousPartial` supplies `SplitRange`
(`Bindings/HomogeneousPartial.lean:97-99` records `= NSFormalization.Section4.B02.SplitRange`
by `rfl`).

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.HomogeneousPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-- **The proved part of B02's homogeneous approximation interface, version 2.**
Version one's `HomogeneousApproxPartialAPI` (16 proved fields of the homogeneous
clause of Proposition 4.6, `paper/sections/04-whole-space.tex:218-229`), together
with the separated-sum packaging and the density conclusion added by lanes 103 and
110 (`Section4/B02/{SeparatedAssembly,ApproxCompact}.lean`).

Every field of `Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI` is
inherited verbatim through `toHomogeneousApproxPartialAPI`; see
`Contracts/V1/HomogeneousPartial.lean` for their docstrings and manuscript
citations.  `annularPathApprox` stays excluded (see the module docstring).

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure HomogeneousApproxPartialV2API extends
    BlowupDensity.Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI where
  -- ### Packaging a separated sum as an element of `F_c`, homogeneously
  /-- `04-whole-space.tex:260`.  "Thus the finite sum `Σ_j φ_j(t)h_j(x)`
  approximates `b` and is jointly smooth with compact support strictly inside
  `R³ × (0,∞)`" (`research/section4/STATEMENTS.md:831-836`).

  `research/B01/Spec.lean`'s `separatedAssembly` (`Contracts/V1/BochnerPartial.lean:145`)
  with exactly the one substitution `research/B01/COMPARISON.md` §3 names: the
  datum-path conjunct is `IsHomogeneousPath s` instead of `IsSobolevPath s`, and the
  per-profile hypothesis is `IsHomogeneousSliceDatum` instead of `IsSobolevDatum`.
  `MemForceCompact`, the strong measurability, and the objects `separatedField`,
  `separatedPath` are word-for-word the shared `B01` ones (`Contracts.V1.BochnerPartial`).

  ⚠ **Proved only on `-3/2 < s`, not the spec's stated `∀ (s : ℝ)`.**
  `NSFormalization.Section4.B02.separatedAssembly` (`SeparatedAssembly.lean:211`)
  carries the extra hypothesis `hs : -3/2 < s`, needed by the uniqueness route
  through `D01`'s compact-datum constructor `homogeneousVectorDatum` (finite only
  at `s > -3/2`).  The verbatim `∀ s : ℝ` field of `research/B02/Spec.lean:593` is
  **not** proved and is near-vacuous for `s ≤ -3/2`
  (`research/B02/REVIEW_APPROX_COMPACT.md` finding 5-A; lane 103's recommendation,
  `REMAINING_SPLIT.md` row 6).  Registered here with the honest hypothesis
  `-3/2 < s`; no consumer is affected, `approxCompactHomogeneous` feeds it only
  `SplitRange.1 = -3/2 < s`.  Every other token matches `Spec.lean:593`. -/
  separatedAssembly : ∀ (s : ℝ), -3 / 2 < s → ∀ (J : ℕ) (φ : Fin J → ℝ → ℝ)
      (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
      (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
      (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) →
    MemForceCompact (BlowupDensity.Contracts.V1.BochnerPartial.separatedField φ h) ∧
      IsHomogeneousPath s (BlowupDensity.Contracts.V1.BochnerPartial.separatedField φ h)
        (BlowupDensity.Contracts.V1.BochnerPartial.separatedPath φ A) ∧
      AEStronglyMeasurable
        (BlowupDensity.Contracts.V1.BochnerPartial.separatedPath φ A) forceTimeMeasure

  -- ### The conclusion
  /-- `04-whole-space.tex:219` prop:Renergy, homogeneous clause: smooth compact
  forces are dense in the full Bochner space `L²(0,∞;Ḣ^{-1}(R³))`, stripped of the
  breakdown condition `T^ν_{max,R}(a,f) ≤ T` (which `R46` supplies from `R41D` by
  the two-radius argument of `04-whole-space.tex:262`).
  `research/section4/STATEMENTS.md:831-836`.

  Stated at every `q ∈ [1,∞)` and every `s` in `SplitRange`, the exact range the
  manuscript's argument covers; `q = 2`, `s = -1` is the single instance `R46`
  consumes.  `04-whole-space.tex:228` — "The homogeneous norm here is a norm of the
  compact difference; the background itself need not belong to that homogeneous
  force space" — is respected by `Data.CompletedDenseHomogeneous`
  (`Data.lean:752`, via `CompletedDenseVia`, `:732`): the target ranges over the
  completion (`MemBochnerDatum`) while `S` stays a set of physical fields, and no
  membership is asserted of anything else.

  Registered **verbatim** as `research/B02/Spec.lean:618`.  The proving theorem
  `NSFormalization.Section4.B02.approxCompactHomogeneous` (`ApproxCompact.lean:229`)
  is **definitionally equal** to this type — kernel-checked by `rfl` in
  `research/B02/axioms_approx_compact.lean` — modulo the three benign token
  differences the `CompletedDenseHomogeneous` `abbrev` and the sanctioned
  `SplitRange` / `forceClassCompact` restatements introduce. -/
  approxCompactHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ,
      BlowupDensity.Contracts.V1.HomogeneousPartial.SplitRange s →
    CompletedDenseHomogeneous q s forceClassCompact

end BlowupDensity.Contracts.V2.HomogeneousPartial
