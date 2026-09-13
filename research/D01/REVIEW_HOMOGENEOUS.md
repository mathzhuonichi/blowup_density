# Lane 024 review — D01 homogeneous half (`Section4/D01/HomogeneousWitness.lean`)

Pass over `erenup/024-D01-homogeneous-witness` @ `d31a175`, base `erenup/integration`. Proof lane, no contract registration. Nothing modified; all scratch files deleted.

## Verdict: **ACCEPT-WITH-NOTES**

Builds clean, all 59 declarations axiom-clean, all seven requested definitional agreements with
`Contracts/V1/Data.lean` hold by `rfl`/`Iff.rfl`, the three headline theorems restate in pure contract
vocabulary, and all four mathematical claims (a)-(d) are **correct**. Notes: stale branch, owed
`Bindings` bridge, two verified reuse simplifications, three prose slips.

## Gates

| gate | result |
|---|---|
| `cd verification && lake build …HomogeneousWitness` | exit 0, `Build completed successfully (8815 jobs)` |
| warnings | **0 from this file, in every run.** The targeted build emits 10, all from replayed deps (`Source/FiniteHilbertBochner` ×3, `Source/RealSobolev` ×3, `Paper3/SpatiallyCompactTime` ×1 deprecated `ContinuousLinearMap.sub_apply`, `Paper3/RealPositiveDensity` ×4, `Paper3/RealVectorPositiveDensity` ×1); the wider `build_changed_lean.py` closure adds more dep warnings, none from this file |
| `lake env lean …/HomogeneousWitness.lean` (fresh elaborate, not cached) | exit 0, **zero bytes of output** |
| `make check` | exit 0 (4 checkers) |
| `build_changed_lean.py --base-ref erenup/integration` (`--dry-run` then real) | dry-run lists `NSFormalization.Section4.D01.HomogeneousWitness`; real run exit 0, `Build completed successfully (8815 jobs)` |
| hygiene grep `sorry\|admit\|axiom\|native_decide\|decide\|set_option\|unsafe\|partial\|nolint\|trust\|maxHeartbeats\|proof_wanted\|autoParam` | **0 hits, comments included**; **59** declarations in 704 lines (37 `theorem` + 3 `@[simp] theorem` + 15 `def` + 4 `abbrev`) |
| `#print axioms` × 59 | **all 59** exactly `[propext, Classical.choice, Quot.sound]`; none missing, none extra |

## Definitional agreement (scratch importing `Contracts.V1.Data` + the module; 27 `example`s, exit 0)

All seven requested pairs close by `rfl` at top level **and** `Iff.rfl`/`rfl` fully applied, as do
the six they ride on (`SpatialField`, `SpaceTimeField`, `VectorDistribution`, `forceTimeMeasure`,
`IsSliceDistribution`, `IsHomogeneousVectorDatum`) — i.e. all 13 names §5/§15 copies. Restated in
pure `BlowupDensity.Contracts.V1.Data` vocabulary and discharged by the module's theorem verbatim:
`exists_isHomogeneousSliceDatum`, `enorm_of_isHomogeneousSliceDatum`, `homogeneousDatum_unique`,
`isHomogeneousSliceDatum_compact`, `isHomogeneousPath_compact`,
`eLpNorm_slice_le_forceHomogeneousENorm`, and `C.homogeneousENorm s (φ : 𝓢') ≠ ⊤` — so
`Data.lean:338` is demonstrably no longer an empty infimum.

## Mathematical rulings

**(a) No `s < 3/2` upper bound is needed — CORRECT.** `|ξ|^s ẑ ∈ L²` for every `s > -3/2` with no
upper bound: near `0`, `∫_{|ξ|<1}|ξ|^{2s}dξ` converges iff `s > -3/2`; at infinity `ẑ` is Schwartz.
The `le_or_gt s 0` split covers exactly that — `s ≤ 0` via `schwartz_homogeneous_negative_integrable`,
`s > 0` via `|ξ|^{2s} = (‖ξ‖²)^s ≤ (1+‖ξ‖²)^s` into `schwartz_bessel_integrable` (every real `s`).
The `Integrable` temperedness clause also holds at every `s`, for the right reason:
`homogeneousDatum_weight_ae` gives `|ξ|^{-s}·G = ẑ` a.e. (`{0}` is null), so `φ·(|ξ|^{-s}G)` is a.e.
Schwartz×Schwartz and `Integrable` is a.e.-invariant (`:283`). The docstring's `2s < 3` is only a
*sufficient* Cauchy-Schwarz route for a general `L²` datum, and `Data.lean:313-315` already names
`G = |ξ|^{3/2}v̂, v ∈ H^∞` as a case holding without it — D01's witness is that family generalized.

**(b) Uniqueness at every real `s` — SOUND, no contradiction.** `h := |ξ|^{-s}(G-G')`; the two
`Integrable` clauses give `ψ·h ∈ L¹` for every Schwartz `ψ`; the two realization identities against
the same `angularFourierDistribution u` give `∫h·ψ = 0`; `locallyIntegrable_of_schwartz_mul` upgrades
the first to `LocallyIntegrable h` by taking, for compact `K ⊆ closedBall 0 R`, a `ContDiffBump 0`
with `rIn = max R 1` (so `b ≡ 1` on `K`) through `CompactSchwartz.ofCompactSupport`;
`ae_eq_zero_of_integral_schwartz_test_mul_eq_zero` gives `h =ᵐ 0`, and `|ξ|^{-s} ≠ 0` off `{0}` gives `G = G'`. No step touches `s`, and structurally none can: polynomial ambiguity arises exactly when
`|ξ|^{-s}ĥ` fails to be locally integrable, so the realization is defined only modulo distributions
supported at `{0}` — and `IsHomogeneousDatum` builds that integrability in, closing the escape by
fiat. Against `Data.lean:318-321` ("the **lower** bound `-3/2 < s` … appears as a hypothesis of unit
L7"): **not a contradiction**, the module proves a strictly stronger L7 than the docstring predicted —
but that sentence now misdescribes the tree. V1 is frozen; record for the lead or a V2 docstring.

**(c) B02's `homogeneousDatumSub` is false as stated — CORRECT; the counter-scenario is real.**
`Spec.lean:470` quantifies over all `z w` with no hypothesis, while `Data.lean:298` totalizes `∫ψ·z_i`
to `0` on a non-integrable integrand (its docstring defers to the `IsSobolevDatum` "Totalization
caveat", `Data.lean:148-155`, verbatim). Concrete witness: let `A ⊆ R³` be a Bernstein set
(non-measurable in every nonempty open set) and `g` a real `C_c^∞(R³;R³)` field with `g_1 ≢ 0`; put
`z := 1_A·e₁ + g`, `w := 1_A·e₁`. For every Schwartz `ψ`, `ψ·z_1` and `ψ·w_1` are not
`AEStronglyMeasurable`, so both integrals are `0`; hence `IsSliceDistribution z (0,g_2,g_3)` and
`IsSliceDistribution w 0` hold, and (using this module's witness on `g_2,g_3`) so do
`IsHomogeneousSliceDatum s z (0,G_2,G_3)` and `IsHomogeneousSliceDatum s w 0`. But `z-w = g` is
smooth compactly supported, its slice distribution is the honest one, and its unique datum has
`G_1 ≠ 0`: both hypotheses hold, the conclusion fails. B02's fields are obligations to discharge,
not axioms, so this is a real defect. `∀ i ψ, Integrable (ψ · z_i)` **is** a correct fix — exactly
what `isSliceDistribution_sub` needs to fire `integral_sub`, and `integrable_schwartz_mul_component`
discharges it for Schwartz-component fields. But for B02, `MemLp z 1 → MemLp w 1` is better: it
matches the sibling `lebesgueHomogeneousDatum` (`:454`), is automatic there (bounded × `L¹` is `L¹`),
is free at B02's call site, and keeps the spec's hypothesis class uniform.

**(d) The radius-1 finding — CORRECT.** `Paper3/HomogeneousTime.lean:14`
`homogeneous_energy_le_bound_add_L2 {s C} (hs : -3/2 < s) (hs0 : s ≤ 0) {φ : Space → ℂ}
(hφ : Measurable φ) (hC : 0 ≤ C) (hbound : ∀ ξ, ‖φ ξ‖ ≤ C) (hL2 : Integrable ‖φ‖²) :
∫‖ξ‖^{2s}‖φ‖² ≤ C²∫_{ball 0 1}‖ξ‖^{2s} + ∫‖φ‖²` is fully generic in `φ` — no Fourier transform in
statement or proof — so its `Metric.ball 0 1` is whatever variable `φ` is written in. Instantiating
`φ := angularFourier k` gives the manuscript's display in the **angular** unit ball directly, no
transport. The cycles radius `1/(2π)` enters only via the corollary
`homogeneousFourierNorm_le_physical` (`:47`), which hard-codes `φ := 𝓕 f`, so
`research/B02/COMPARISON.md:108` is right that transporting *that* is not a restatement. Range: the
lemma needs `s ≤ 0` and B02's `SplitRange s := -3/2 < s ∧ s ≤ 0` (`Spec.lean:237`) matches exactly.
ATTEMPTS §5's factor also checks:
`∫|ξ|^{2s}|angularFourier f|²dξ = (2π)^{-3}∫|2πη|^{2s}|𝓕f(η)|²(2π)³dη = (2π)^{2s}∫|η|^{2s}|𝓕f|²`.

## Reuse spot-check (8/8 confirmed; signatures match the use sites)

`AngularFourierDilation.lean:208` `schwartzAngularDilation_fourier_apply` (`rfl` bridge) → `:88`; `:218`
`angularFourierDistribution_schwartz_apply` → `:283`. `CompactFourier.lean:17`
`schwartz_homogeneous_negative_integrable` → `:97`; `:37` `schwartz_bessel_integrable` (returns
`Integrable (besselIntegrand s φ)`, unfolded at `:113`) → `:99`. `RealSobolev.lean:61`
`fourier_conjugate` → `:180`, and the `angularFourier_conj_neg` chain is correct.
`WeakFourierUniqueness.lean:40` `ae_eq_zero_of_integral_schwartz_test_mul_eq_zero` → `:339`;
and `Paper3.compact_spatial_slice` (`CompactFourierTime.lean:20`) is genuinely `ℂ`-only, so the copy at
`:641` is justified (issue 4). `CompactSchwartz.ofCompactSupport` (`R3/CompactSchwartz.lean:37`,
`coe_ofCompactSupport := rfl`) → `:302, :501`. No fabricated citations found.

## `ATTEMPTS_HOMOGENEOUS.md` accuracy

All three gap claims are **accurate**. (i) U7c's blocker really is
`AEStronglyMeasurable (compactHomogeneousPath …) forceTimeMeasure`: `Data.lean:390` puts it inside the
infimum's subtype, so the lower bound is unconditional while the upper bound needs an admissible path —
exactly `forceHomogeneousENorm_eq_of_aestronglyMeasurable`'s one hypothesis. (ii) The `L¹∩L²` class is
not reached: every existence theorem hypothesises Schwartz components, so B02's
`lebesgueHomogeneousDatum` as written is not dischargeable here; `(1-χ_R)h_n` being Schwartz is right
about the *mathematical* use but does not discharge the *field*. (iii) No scaling lemma exists (grep:
zero hits). §4's routes are plausible and correctly sourced. Prose slips: issues 3 and 5.

## Issues, ranked

1. **Branch is 22 commits behind `erenup/integration`** (merge-base `b197afe`; integration `a76eba8`).
   `research/B02/Spec.lean`, cited by the module docstring and throughout ATTEMPTS, does not exist in
   this worktree, and lanes 019-023 (including D01's own `Section4/D01/SmoothDatum.lean`) were absent
   from the build I verified. Mitigation checked: all six imported modules are byte-identical on
   integration and the added file collides with nothing, so the build carries over. Rebase and re-run
   both builds before merge.
2. **`verification/Bindings` `rfl` bridge owed.** §5/§15 restate 13 `Data.lean` declarations. I
   verified all 13 by `rfl` today, but nothing in CI guards them — the exact drift the contract-import
   rule exists to prevent, and CLAUDE.md's "每个重写的定义都要有桥" applies in spirit even though the
   rule is written for `Contracts/*`. Out of this lane's scope; first item of the follow-up lane.
3. **Header overclaim at `:13-16`**: "`Data.lean:338` … and `Data.lean:390` `forceHomogeneousENorm`
   were empty infima … This module builds the witness." True for `:338`; for `:390` only
   `IsHomogeneousPath` is inhabited — the subtype additionally demands `AEStronglyMeasurable`, so
   `forceHomogeneousENorm` is still not known `< ⊤`. §15's docstrings and ATTEMPTS §4(a)1 are correct;
   only the header overstates.
4. **Two reuse simplifications, both compiled by me.** `integrable_schwartz_mul_angularFourier`
   (`:254`, 12 lines) and `integrable_schwartz_mul_component` (`:591`, 20 lines) are both
   `Integrable.mul_bdd` (Mathlib `MeasureTheory/Function/L1Space/Integrable.lean:1073`) applied as
   `X.integrable.mul_bdd (c := SchwartzMap.seminorm ℝ 0 0 _) _.continuous.aestronglyMeasurable
   (.of_forall (SchwartzMap.norm_le_seminorm ℝ _))` — 4 and 6 lines, no hand-rolled `.mono'`/`calc`.
   And `Paper3.compact_spatial_slice` generalises verbatim in the codomain alone
   (`{M} [TopologicalSpace M] [Zero M] {F : ℝ × Space → M}`, same proof, compiles); doing that
   upstream removes the copy at `:641` instead of attributing it.
5. **ATTEMPTS says "56 declarations"; the file has 59.** The audit covered all 59 regardless.
   ATTEMPTS §6 also says `build_changed_lean.py --dry-run` reports `none` — true only while the file
   was untracked; now committed, it correctly reports the module. Both stale, harmless.
6. Nit: `ae_ne_zero` (`:155`) is fully generic yet sits in a D01 namespace, and
   `locallyIntegrable_of_schwartz_mul`'s inline bump duplicates `Paper1.exists_spatial_cutoff`
   (`Paper1/LocalCutoff.lean:11`) — importing `Paper1` here is not worth it; recorded so the next
   lane does not rebuild either a third time.

## What remains

* **I03 / U7c / `HomogeneousScalingAPI`** (`Contracts/V1/Scaling.lean:509-538`): one blocker,
  `AEStronglyMeasurable (compactHomogeneousPath …)`. D01's route (continuity via
  `isHomogeneousSliceDatum_sub` + `enorm_of_isHomogeneousSliceDatum` +
  `homogeneous_energy_le_bound_add_L2` at `φ := angularFourier k`) is sound per (d) but covers only
  `-3/2 < s ≤ 0`; `s > 0` needs Schwartz-seminorm continuity in `t`. The scaling identity is
  untouched — missing piece: the `∫⁻` form of `Paper3.homogeneous_energy_dilate` (`SobolevWeights:87`).
* **B02**: (i) fix `homogeneousDatumSub` per (c), preferring `MemLp z 1 → MemLp w 1`; (ii)
  `lebesgueHomogeneousDatum` is discharged only for Schwartz-component fields — either widen D01 to
  `L¹∩L²` (needs `angularFourierDistribution` of an `L¹∩L²` field, i.e. `Lp.toTemperedDistribution`)
  or narrow the spec field to Schwartz components, dischargeable today; (iii) prove `lowHighSplit`
  by re-applying the generic lemma in the angular variable, not by transport.
* **R46**: `CompletedDenseHomogeneous` (`Data.lean:752`) is no longer vacuous at the level of "the
  objects exist", but still needs the measurability witness above plus B02 stages 1-6 — unblocked, not closed.
