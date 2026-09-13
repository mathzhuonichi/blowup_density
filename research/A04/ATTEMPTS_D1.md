# A04 unit D1 — attempts and findings (lane 053)

Unit D1 of `research/A04/COMPARISON.md` §4 (row ~line 211). Deliverable:
`WT/formalization/NSFormalization/Section4/A04/DerivNorm.lean`, conformance
`WT/research/A04/axioms_d1.lean`.

**What D1 is.** From the hypothesis `HasSmoothSobolevPath T u` (`Spec.lean:247`),
turn the `C^∞`-in-time datum path `G : ℝ → RealVectorSobolev m` into
(i) `HasDerivAt (fun r => ‖G r‖^2) (2⟪G t, G' t⟫) t` on `Ioo 0 T`, and
(ii) the identification `sobolevNormAt (m:ℝ) u r = ‖G r‖`, transported to the
`sobolevNormAt … ^ 2` shape that `energyIdentityHigh`'s LHS (`Spec.lean:429`)
consumes. Pure Hilbert-space calculus once the path is given.

## The one real obstacle: the inner product instance was missing

The template (`Source/OrdinaryViscousStability.lean:88`,
`Euler/OrdinaryEulerL2Stability.lean:79`) uses Mathlib's `HasDerivAt.norm_sq`
(`Mathlib/Analysis/InnerProductSpace/Calculus.lean:215`):
`HasDerivAt f f' t → HasDerivAt (‖f ·‖^2) (2 * ⟪f t, f'⟫) t`, which requires
`InnerProductSpace ℝ F` on the carrier. The task brief said "check
`Paper3/RealVectorSobolev*.lean` for the `InnerProductSpace ℝ` instance", but
**no such instance is registered.** A probe (`example : InnerProductSpace ℝ
(RealVectorSobolev (3:ℝ)) := inferInstance`) failed with
`failed to synthesize Inner ℝ (RealVectorSobolev 3)`.

Why: `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)
= PiLp 2 (fun _ : Fin 3 => RealSobolevHilbert s)`
(`Paper3/RealVectorPositiveDensity.lean:15`, `Source/FiniteHilbertBochner.lean:11`),
and `RealSobolevHilbert s = ↥(realSubspace s)` where `realSubspace s`
is a `ClosedSubmodule ℝ FourierData`, `FourierData = Lp ℂ 2`
(`Source/RealSobolev.lean:118,121`). The existing
`Paper3.realSobolevNormedAddCommGroup` (`Paper3/RealPositiveDensity.lean:14`)
gives only the `NormedAddCommGroup`, via
`inferInstanceAs (NormedAddCommGroup (realSubspace s).toSubmodule)`. No inner
product was ever declared, and `Inner`/`InnerProductSpace` do not fire through the
`ClosedSubmodule` `CoeSort` automatically.

### Positive finding — the instance IS derivable, cleanly

Probes (deleted scratch `research/A04/probe*.lean`) established, in order:

1. `example : InnerProductSpace ℝ FourierData := inferInstance` — succeeds
   (the only error was a missing `noncomputable`, i.e. synthesis went through,
   depending on `MeasureTheory.L2.innerProductSpace`). So the ambient `Lp ℂ 2`
   has a real inner product findable by instance search.
2. `instance (s) : InnerProductSpace ℝ (RealSobolevHilbert s) :=
   inferInstanceAs (InnerProductSpace ℝ (realSubspace s).toSubmodule)` — succeeds.
   This is `Submodule.innerProductSpace` on the *same* `Submodule` whose
   canonical `NormedAddCommGroup` is `realSobolevNormedAddCommGroup`, so the
   inner product's induced norm is defeq to the existing `‖·‖` — **no norm
   diamond**.
3. With that instance in scope, `PiLp.innerProductSpace` lifts to
   `InnerProductSpace ℝ (RealVectorSobolev s)` automatically.
4. Norm compatibility check: `example (x : RealVectorSobolev (3:ℝ)) :
   Real.sqrt (inner ℝ x x) = ‖x‖ := (norm_eq_sqrt_re_inner x).symm` — succeeds,
   confirming the `‖·‖` in `HasDerivAt.norm_sq`'s output is the *same* norm
   `sobolevNormAt`/`sobolevNormAt_eq` use.
5. `HasDerivAt.norm_sq` then delivers the D1 core verbatim.

The single-line instance is the whole fix. It was first written in `DerivNorm.lean`
and, per review finding 2, lifted to `Paper3/RealPositiveDensity.lean` as
`realSobolevInnerProductSpace` (next to `realSobolevNormedAddCommGroup` /
`realSobolevNormedSpace`) so any `Paper3` consumer — not only A04 — gets it and
no parallel lane declares a clashing copy. See "Review fixes" below.

## Calculus, once the instance exists

* `HasSmoothSobolevPath` restated token-for-token in §0 from `Spec.lean:247`
  (it lives on no local module yet).
* `ContDiffOn ℝ ∞ G (Ico 0 T)` → `HasDerivAt G (deriv G t) t` on `Ioo 0 T`:
  `ContDiffOn.differentiableOn (by simp : (∞:_) ≠ 0)` gives
  `DifferentiableOn`, then at an interior point `Ico 0 T ∈ 𝓝 t` (because
  `Ioo 0 T ⊆ Ico 0 T` and `Ioo_mem_nhds ht.1 ht.2`), so
  `DifferentiableWithinAt.differentiableAt` upgrades to `DifferentiableAt`,
  `.hasDerivAt`. `G' = deriv G`, matching "the derivative of the path".
* Transport `‖G r‖^2 ↦ sobolevNormAt (m:ℝ) u r ^ 2` on `Ioo 0 T`:
  `HasDerivAt.congr_of_eventuallyEq` with `filter_upwards [Ioo_mem_nhds …]` and
  `sobolevNormAt_eq` (lane 039, `Continuity.lean`) at each slice — the datum at
  time `r` is `G r` (from the `IsSobolevDatum` conjunct of
  `HasSmoothSobolevPath`), so `sobolevNormAt (m:ℝ) u r = ‖G r‖`.

## Small snags fixed while building

* `𝓝` unknown identifier → added `open scoped Topology`.
* `ContDiffOn.differentiableOn` takes `n ≠ 0` (not `1 ≤ n`); the existing
  codebase idiom `(by simp)` discharges `(∞ : WithTop ℕ∞) ≠ 0`.
* ~~`Ico_mem_nhds` does not exist in this Mathlib~~ **(corrected — review
  finding 3)**: `Ico_mem_nhds` **does** exist at this pin. It has no source
  declaration to grep for because it is auto-generated by the
  `@[to_dual (reorder := ha hb)]` attribute on `Ioc_mem_nhds`
  (`Mathlib/Topology/Order/OrderClosed.lean:614`); Mathlib uses it at
  `Analysis/Convex/Continuous.lean:332`. `hasDerivAt_datumPath` now uses
  `Ico_mem_nhds ht.1 ht.2` directly, replacing the earlier
  `Filter.mem_of_superset (Ioo_mem_nhds …) Ioo_subset_Ico_self` workaround.

## Conformance (`axioms_d1.lean`)

Restates `sobolevNormAt` (Spec:183) and `HasSmoothSobolevPath` (Spec:247)
token-for-token in the spec's `Data` vocabulary, bridges `ClassicalSolutionR`
with `toA02` (as `axioms_f1n1.lean`), and discharges the `energyIdentityHigh`
LHS `∃ d, HasDerivAt (fun r => sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t` by
`exact` on the library theorem. Works because `Data.IsSobolevDatum` /
`Data.sobolevENorm` are defeq to the `D01` restatements the library is stated
against (verbatim copies, per `SmoothDatum.lean:236` and `Forcing.lean §0`).
`#print axioms` = `propext, Classical.choice, Quot.sound` for all seven audited
declarations (five library + two spec-vocabulary).

## Commands

* `bash scripts/lean-install.sh` → `== OK` (seeded builds).
* `cd verification && lake build NSFormalization.Section4.A04.Continuity` →
  built (seeds the 039 closure).
* `cd verification && lake build NSFormalization.Section4.A04.DerivNorm` →
  `Build completed successfully`, no errors, no warnings on the module.
* `cd verification && lake env lean ../research/A04/axioms_d1.lean` → the seven
  `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`.

## What is NOT in scope (deliberately left to other units)

* The eq:Rhigh bound on `(1/2)d + ν‖∇u‖²_{H^m}` — unit **G1** (blocked behind
  D01 **L2**).
* The `ζ`-regularized `√(E+ζ²)` derivative — unit **Z1**.
* Producing `HasSmoothSobolevPath` itself — A01's `sobolev_smooth`
  (`REVIEW.md` finding 4); D1 consumes it as a hypothesis.

## New obligation booked: D2 (review finding 6)

D1 hands G1 the derivative value `d = 2⟪G t, deriv G t⟫`. To reach eq:Rhigh, G1
must read `⟪G t, deriv G t⟫` as `⟪u(t), ∂ₜu(t)⟫_{H^m}` and substitute the
momentum equation. **Nothing currently identifies `deriv G t` with the order-`m`
datum of `∂ₜu(t,·)`** — `HasSmoothSobolevPath` asserts only that *some*
`C^∞`-in-time path represents the *slices* `u(t,·)`, not that its time derivative
is the datum of the time-derivative field. Producing the path (A01's
`sobolev_smooth`) is not the same as identifying its derivative.

**Obligation D2** (nobody's today; book before G1 is scheduled): either
(a) strengthen `HasSmoothSobolevPath` with a third conjunct
`∀ t ∈ Ioo 0 T, IsSobolevDatum (m:ℝ) (fun x => ∂ₜu (t,x)) (deriv G t)` and push it
onto A01, or (b) open a small unit for the datum/time-derivative interchange.
Until then `d` is a number attached to an abstract path and eq:Rhigh's RHS is
unreachable. This is a spec-level gap, not a defect of D1.

## Review fixes (ACCEPT-WITH-NOTES, review `REVIEW_D1.md`)

Applied after the ACCEPT-WITH-NOTES verdict:

1. **Instance lifted to Paper3 (finding 2).** `instInnerProductSpaceRealSobolevHilbert`
   moved out of the A04 leaf into
   `formalization/NSFormalization/Paper3/RealPositiveDensity.lean` as
   `realSobolevInnerProductSpace`, immediately after `realSobolevNormedSpace`
   (lead-approved single-instance exception to "no edits to existing files"; the
   existing imports of `RealPositiveDensity` already supply
   `Submodule.innerProductSpace` and `InnerProductSpace ℝ (Lp ℂ 2)`, so no import
   was added). The `open NSFormalization.Source.RealSobolev (RealSobolevHilbert
   realSubspace)` line was dropped from `DerivNorm.lean`; `PiLp.innerProductSpace`
   now finds `InnerProductSpace ℝ (RealVectorSobolev s)` automatically for any
   consumer of `Paper3`. Downstream re-verified below.
2. **`Ico_mem_nhds` (finding 3).** Record corrected (above) and the workaround
   replaced by `Ico_mem_nhds ht.1 ht.2`.
3. **Cosmetics (findings 7, 8).** Dead `toA02` deleted from `axioms_d1.lean`;
   unused `open`s (`MeasureTheory`, `ENNReal`, and the five unused `A02`/three
   unused `D01` names) trimmed from `DerivNorm.lean` to just `Set`, `Space`,
   `RealVectorSobolev`, `ContDiff`, `RealInnerProductSpace`, `Topology`,
   `SpaceTimeField`, `IsSobolevDatum`; `hasDerivAt_datumNormSq_of_contDiffOn` now
   routes through `hasDerivAt_datumNormSq` instead of calling `.norm_sq` inline.
4. **D2 booked** (finding 6), section above.

Findings 1, 4, 5 were passes (no norm diamond, accurate snag record for
`ContDiffOn.differentiableOn`, statements match `energyIdentityHigh`'s LHS);
finding 9 (Section 4 leaves outside the default CI target) is pre-existing and
lead-level, not a lane-053 change.
