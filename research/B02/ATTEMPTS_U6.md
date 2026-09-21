# B02 unit 6 — `homogeneous_datum_of_lebesgue` — attempts and findings

Module: `formalization/NSFormalization/Section4/B02/LebesgueDatum.lean`
(namespace `NSFormalization.Section4.B02`). Conformance:
`research/B02/axioms_u6.lean`.

Discharges `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum` (both clauses).
The companion field `research/B02/Spec.lean:470` `homogeneousDatumSub` is **false**
as originally stated (lane 068 review, machine-checked counterexample); the honest
integrability-carrying form is provided instead, and lane 060's diagonal is
rewired to it. See §3 and §7.

## 1. What closed, and the route that worked

For a real `k : Space → Space` with `MemLp k 1` and `MemLp k 2`, order `-3/2 < s ≤ 0`.

Datum: `G_i := |ξ|^s · angularFourier k_i = D01.Homogeneous.homogeneousProfile s k_i`,
made an `L²` element.

* `angularFourierDistribution_lp_apply` — the multiplication formula
  `angularFourierDistribution ((toLp g):𝓢') ψ = ∫ ψ · angularFourier g` for
  `g ∈ L¹∩L²`. Proof chain: `angularFourierDistribution = angularDistributionDilation ∘ 𝓕`
  (def, by `change`) → `AFD:98 angularDistributionDilation_apply` (amplitude
  `frequencyUnit^{3/2}`, test precomposed with `angularFrequencyScale = frequencyUnit•·`)
  → `Mathlib Lp.fourier_toTemperedDistribution_eq` → lane 059's `l2_fourier_pairing`
  (`Section4/B02/LowHigh.lean`) → the `(2π)`-dilation change of variables
  `Measure.integral_comp_smul` (`|(c^3)⁻¹|`, `finrank ℝ Space = 3`) cancelling the
  amplitude to `frequencyUnit^{-3/2}`. This is the Schwartz-only
  `D01.Homogeneous.angularFourierDistribution_schwartz_apply` widened to `L¹∩L²`.
* `homogeneousProfile_memLp` — finiteness, the genuinely new low/high split at
  *angular* radius 1 for a single `L¹∩L²` component. Low: `norm_angularFourier_le`
  (`‖k̂‖ ≤ (2π)^{-3/2}∫‖k‖`, from `VectorFourier.norm_fourierIntegral_le_integral_norm`)
  × `Section4/B02/LowFrequency.lean lowFrequencyIntegrable` (`∫_{|ξ|<1}|ξ|^{2s}<∞`,
  needs `-3/2<s`). High: `|ξ|^{2s} ≤ 1` (needs `s ≤ 0`,
  `Real.rpow_le_one_of_one_le_of_nonpos`) × lane 059's
  `Section4/B02/LowHigh.lean angular_plancherel` (`∫|k̂|² = ‖k‖₂²`). The
  COMPARISON's `MSF:306 integral_norm_sq_fourier` is Schwartz-only and unusable
  here; lane 059's `L¹∩L²` Plancherel is exactly what the high half needs.
* `realSymmetry_lebesgueDatum` / `mem_realSubspace_lebesgueDatum` — reality
  (`04:249` "take real parts"): the weight is real and even, so `RS:60
  fourier_conjugate` via `D01.Homogeneous.angularFourier_conj_neg` gives
  `realSymmetry (datum) = datum`. Same proof as `D01`'s
  `realSymmetry_homogeneousDatum` with the Schwartz `MemLp` replaced by ours.
* `isHomogeneousSliceDatum_lebesgue` — the realization: witness `U_i` = the `L²`
  distribution of `k_i` (`Lp.toTemperedDistribution`), whose `IsSliceDistribution`
  clause is `Lp.toTemperedDistribution_apply` + `coeFn_toLp`, and whose
  `IsHomogeneousDatum` clause is `angularFourierDistribution_lp_apply` + the a.e.
  weight cancellation `lebesgueDatum_weight_ae` (`|ξ|^{-s}·|ξ|^s = 1` off `0`).
  Integrability clause: `Integrable.mul_bdd` (Schwartz × bounded `angularFourier`).
* `enorm_lebesgueVectorDatum` — norm of the constructed datum equals
  `homogeneousFourierENorm s k`; from `D01.Homogeneous.enorm_sq_piLp` +
  `enorm_lebesgueDatum_sq` (the single-component `enorm_homogeneousDatum_sq`).
* `lebesgueHomogeneousDatum` — the spec field. Existence = the constructed
  `lebesgueVectorDatum`. Norm clause for *every* datum via
  `D01.Homogeneous.isHomogeneousSliceDatum_unique` (valid at every real `s`): any
  datum equals the constructed one, so shares its norm.

## 2. Reuse of D01 (which lemmas, how widened)

`Section4/D01/HomogeneousWitness.lean` (`D01.Homogeneous`) already builds the
homogeneous datum for **Schwartz / compact-smooth** fields:
`exists_isHomogeneousSliceDatum` (:473), `enorm_of_isHomogeneousSliceDatum` (:486),
`isHomogeneousSliceDatum_compact` (:519). These take a Schwartz family (or
`ContDiff∞ ∧ HasCompactSupport`) as hypothesis; they do **not** cover general
`L¹∩L²` fields. The whole job of unit 6 was the passage Schwartz → `L¹∩L²`, in
`homogeneousProfile_memLp` (finiteness via 059's Plancherel, not the Schwartz
`integral_norm_sq_fourier`) and `angularFourierDistribution_lp_apply` (the
`L¹∩L²` multiplication formula, not the Schwartz `angularFourierDistribution_schwartz_apply`).

Reused *unchanged* from `D01.Homogeneous`: `homogeneousProfile`,
`norm_homogeneousProfile_sq`, `angularFourier_conj_neg`, `ae_ne_zero`,
`enorm_sq_piLp`, `isHomogeneousSliceDatum_unique`, `isHomogeneousVectorDatum_sub`,
`isHomogeneousSliceDatum_sub`. The `D01` predicates are definitionally equal to
lane 060's `Section4/B02/Cutoff.lean` restatements (this module is in the same
`B02` namespace and uses those); `B02.IsHomogeneousSliceDatum ↔
D01.Homogeneous.IsHomogeneousSliceDatum` is `Iff.rfl` (checked), so `D01`'s
theorems apply to `B02`'s predicates by defeq.

## 3. `homogeneousDatumSub` — the spec field is FALSE (review upgrade)

Spec (`research/B02/Spec.lean:470`, original), **no** integrability hypotheses:

```
∀ (s) (z w : SpatialField) (Z W : RealVectorSobolev s),
  IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
    IsHomogeneousSliceDatum s (z - w) (Z - W)
```

Lane 068's review (`research/B02/REVIEW_U6.md` §4, machine-checked) upgraded the
initial diagnosis: this field is **not merely underivable, it is false** under
`Data.lean:298`'s totalizing Bochner convention. The earlier version of this
section (calling it "true but pending a temperate-growth development") was
**wrong** and is corrected here.

Reduction (an *iff*, checked): with `U`, `V` the distributions of `z`, `w`, the
`IsHomogeneousVectorDatum` clause of the conclusion forces the witness for `z − w`
to be `U − V` (injectivity of `angularFourierDistribution`,
`AngularSobolevClass.lean:22`, `isHomogeneousVectorDatum_sub` for the linearity
half). The remaining `IsSliceDistribution (z − w) (U − V)` is, provably both ways,
exactly

```
(∫ x, ψ x * z_i x) − (∫ x, ψ x * w_i x) = ∫ x, ψ x * (z_i x − w_i x)
```

i.e. `MeasureTheory.integral_sub`.

Refutation: `IsSliceDistribution` totalizes the Bochner integral, so a field that
pairs non-integrably with *every* Schwartz test has all its pairings `= 0` and
satisfies `IsSliceDistribution z 0` vacuously — carrying the **zero** homogeneous
datum at every order (reviewer's `zero_datum`, no side conditions). Feeding the
spec field two such wild fields whose difference pairs non-trivially collapses it
(reviewer's `collapse`: instantiate at `s = -1`, `Z = W = 0`, use `0 − 0 = 0`,
and kill the returned witness with `angularFourierDistribution_injective`). The
explicit classical counterexample (`spec_field_false_of_wild_pair`, elaborated by
the reviewer):

> `{q_n}` enumerates `ℚ³`, `f = Σ_n 2^{-n} |x−q_n|^{-3} · 1_{0<|x−q_n|<2^{-n}}`.
> `f` is measurable and a.e. finite (Borel–Cantelli: `Σ vol B(q_n,2^{-n}) < ∞`,
> so a.e. `x` meets only finitely many balls), yet `∫_B f = ∞` for **every** ball
> `B` (each contains some `q_n` with `B(q_n,2^{-n}) ⊆ B`, and `∫_{|y|<r}|y|^{-3}`
> diverges logarithmically in `ℝ³`). Hence for every Schwartz `ψ ≢ 0`, `ψ·f` is
> non-integrable and the totalized pairing is `0` (`ψ ≡ 0` gives `0` too). With
> `c` a nonzero real Schwartz function, `z := (f,0,0)`, `w := (f − c,0,0)`: both
> satisfy the datum hypotheses with `U = V = 0`, `Z = W = 0`; but `(z − w)₀ = c`
> and `∫ c·c > 0`.

The prior claim — "physical integrability is true whenever a genuine distribution
`U` exists" — is the error: `U = 0` serves for any field that never pairs
integrably, so the existence of `U` does **not** force `z` to be locally
integrable. No temperate-growth development can prove the field.

Fix taken (all landed this lane): the honest theorem is `D01`'s
`isHomogeneousSliceDatum_sub` (two physical-pairing integrability side
conditions), re-exposed as `isHomogeneousSliceDatum_sub_of_integrable`. The side
conditions are `Integrable.mul_bdd` (bounded × integrable) facts;
`D01.Homogeneous.integrable_schwartz_mul_component` is **only** the special case
for a `ℂ`-valued Schwartz *family* and covers **neither** call-site field
literally (the first is real-valued; the second, `(1−χ_R)·schwartzVector ψ`, is
bounded×Schwartz, not a Schwartz family). They are discharged directly at lane
060's single call site by the new `Cutoff.lean` lemmas `integrable_schwartzVector`
/ `integrable_cutoffCompl_schwartzVector`. Lane 060's `spatialApproxHomogeneous_of`
took the false field verbatim, so was **uninstantiable** — unit 9's diagonal *was*
blocked, contrary to the earlier ATTEMPTS "the assembly is not blocked"; it has now
been rewired to the integrability-carrying `hDatumSub`, and
`spatialApproxHomogeneous_of_units` (`LebesgueDatum.lean`) instantiates it, leaving
only unit 2 (`annularSchwartz`). The spec field `research/B02/Spec.lean:470` is
amended to the integrability-carrying form with the counterexample in its docstring.

## 4. Bonus: unit-6 and unit-7 hypotheses of `spatialApproxHomogeneous_of`

Two `example`s at the end of the module discharge, verbatim in the shape lane
060's `Section4/B02/Cutoff.lean spatialApproxHomogeneous_of` expects:
- its unit-6 hypothesis, from `lebesgueHomogeneousDatum` (`SplitRange = ⟨hs, hs0⟩`);
- its unit-7 hypothesis, from lane 059's `lowHighSplit` (the LHS
  `homogeneousFourierENorm s k ^ 2` and constant `lowHighConstant s` match by
  `rfl`).
(`spatialApproxHomogeneous_of` still needs its unit-2 hypothesis and the
`homogeneousDatumSub` field of §3, which are not part of unit 6.)

## 5. Approaches tried that did not work / pitfalls

* `Continuous.const_smul` scalar inference gets stuck (`ContinuousConstSMul ?m ℂ`)
  when the composed function's smul target type is not pinned; fixed by an
  explicit `have h2 : Continuous (fun ξ => c • …) := h1.const_smul c` with the
  `fun ξ => c • …` ascription (rather than the point-free `c • f`), which forces
  the eta form `simp only [angularFourier]` then rewrites to. A stuck-instance
  error from such a later `have` was mis-reported by Lean at an earlier line, so
  isolate declarations when diagnosing.
* `Measure.integral_comp_smul` is under `MeasureTheory.Measure`, first explicit
  arg is the measure (`Measure.integral_comp_smul (volume) f c`), not the
  metavariable form.
* `lintegral_mono` leaves beta-redexes `(fun a => …) ξ`; a `dsimp only` before the
  `rw` is needed.
* Attempted the exact `homogeneousDatumSub` directly (see §3); the goal after
  `rw [(U−V)_i ψ = U_iψ − V_iψ, hU, hV]` is the `integral_sub` identity — the
  precise obstruction, recorded so the gap is not re-attempted blindly.

## 6. Commands run (from the worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

- `cd verification && lake build NSFormalization.Section4.B02.LebesgueDatum`
  → `Build completed successfully (8820 jobs)`, module built in 3.6 s, no
  warnings/errors in the module (only pre-existing upstream `RealPositiveDensity`
  / `RealVectorPositiveDensity` warnings).
- `cd verification && lake env lean ../research/B02/axioms_u6.lean` → exit 0; the
  two spec-typed `example`s typecheck against the frozen `Contracts.V1.Data`
  predicates, and `#print axioms` on `lebesgueHomogeneousDatum`,
  `isHomogeneousSliceDatum_lebesgue`, `angularFourierDistribution_lp_apply`,
  `homogeneousProfile_memLp`, `enorm_lebesgueVectorDatum` → each
  `[propext, Classical.choice, Quot.sound]`.

## 7. Review fixes (lane 068 verdict ACCEPT-WITH-NOTES + FALSE upgrade)

The reviewer (`research/B02/REVIEW_U6.md`) accepted `lebesgueHomogeneousDatum` in
full and upgraded the `homogeneousDatumSub` diagnosis from "underivable" to
"false" (counterexample above, §3). Applied fixes:

- **`Section4/B02/Cutoff.lean`** (lead-approved edit to a merged file):
  weakened the `hDatumSub` hypothesis of `spatialApproxHomogeneous_of` to the
  integrability-carrying form; added helper lemmas `integrable_schwartzVector`
  and `integrable_cutoffCompl_schwartzVector` (both `χ.integrable.mul_bdd` with
  `c := SchwartzMap.seminorm ℝ 0 0 (ψ i)`); discharged the two new side conditions
  at the single call site; updated the theorem docstring.
- **`Section4/B02/LebesgueDatum.lean`**: rewrote the module docstring
  §"companion field" (false, with the counterexample), corrected the
  `integrable_schwartz_mul_component` sentence, and added
  `spatialApproxHomogeneous_of_units` — the stage-4 diagonal with units 6/7 and
  the sub-field supplied, leaving only unit 2 (`annularSchwartz`).
- **`research/B02/Spec.lean`**: amended `homogeneousDatumSub` to the
  integrability-carrying form, docstring citing the review counterexample and
  recording that the original was refuted.
- **`research/B02/axioms_u6.lean`**: added `def SplitRange` (matching the sibling
  conformance files) and two more `#print axioms`
  (`isHomogeneousSliceDatum_sub_of_integrable`, `spatialApproxHomogeneous_of_units`).

Commands after the fixes (worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`,
no `-j`, lake from `WT/verification` only):

- `lake build NSFormalization.Section4.B02.Cutoff` → `Build completed successfully
  (8815 jobs)` (4.7 s), no diagnostics from the module.
- `lake build NSFormalization.Section4.B02.LebesgueDatum` → `Build completed
  successfully (8820 jobs)` (3.6 s), no diagnostics from the module.
- `lake env lean ../formalization/NSFormalization/Section4/B02/Cutoff.lean` → silent, `EXIT=0`.
- `lake env lean ../formalization/NSFormalization/Section4/B02/LebesgueDatum.lean` → silent, `EXIT=0`.
- `lake env lean ../research/B02/Spec.lean` → silent, `EXIT=0`.
- `lake env lean ../research/B02/axioms_u6.lean` → the 7 `#print axioms` all
  `[propext, Classical.choice, Quot.sound]`; both spec-typed `example`s elaborate.
- `make check` → `EXIT=0`.
