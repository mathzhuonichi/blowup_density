# B02 `separatedAssembly` — route as executed (lane 103)

Field: `research/B02/Spec.lean:582-600` `separatedAssembly` of `HomogeneousApproxAPI`.
Deliverable: `formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean`,
`theorem NSFormalization.Section4.B02.separatedAssembly`.
Conformance: `research/B02/axioms_separated.lean`.

## 1. Exact statement proved vs. the field

The spec field quantifies over **all** real `s`.  The theorem proved carries **one extra
hypothesis** `hs : -3 / 2 < s`, placed immediately after `s`; every other token is the field.
It is therefore **not** the verbatim field (see §4).

```
theorem separatedAssembly (s : ℝ) (hs : -3 / 2 < s) {J : ℕ} (φ : Fin J → ℝ → ℝ)
    (h : Fin J → Space → Space) (A : Fin J → RealVectorSobolev s)
    (hφs : ∀ j, ContDiff ℝ ∞ (φ j)) (hφc : ∀ j, HasCompactSupport (φ j))
    (hφpos : ∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ))
    (hhs : ∀ j, ContDiff ℝ ∞ (h j)) (hhc : ∀ j, HasCompactSupport (h j))
    (hA : ∀ j, IsHomogeneousSliceDatum s (h j) (A j)) :
    D01.MemForceCompact (B01.separatedField φ h) ∧
      IsHomogeneousPath s (B01.separatedField φ h) (B01.separatedPath φ A) ∧
      AEStronglyMeasurable (B01.separatedPath φ A) D01.forceTimeMeasure
```

The predicates are the local `Contracts.V1.Data` restatements (`MemForceCompact`,
`forceTimeMeasure` from `Section4/D01/ForceClass.lean`; `IsHomogeneousPath`,
`IsHomogeneousSliceDatum` from `Section4/D01/HomogeneousWitness.lean` §5,§15;
`separatedField`, `separatedPath` from `Section4/B01/Separated.lean`), each definitionally the
`Data.lean` one.  `research/B02/axioms_separated.lean` transcribes the field type in the
`Contracts.V1.Data` vocabulary (with the spec-local `separatedField`/`separatedPath` restated
verbatim) and inhabits it with this theorem; it typechecks, confirming the bridges.

## 2. Route as executed (the reviewer's F1 / task route (a)-(e))

Conjuncts 1 (`MemForceCompact`) and 3 (`AEStronglyMeasurable`) are realization-independent and
identical to `B01`: reused verbatim via `B01.memForceCompact_of_smooth_support` ∘
`B01.{contDiff, hasCompactSupport, tsupport_…}_separatedField` and
`B01.aestronglyMeasurable_separatedPath`.

Conjunct 2 (`IsHomogeneousPath`), the only new content, is a per-`t` `IsHomogeneousSliceDatum` of
the slice `x ↦ Σ_j φ_j(t) h_j(x)` carrying `Σ_j φ_j(t) • A_j`.  Proved once as the reusable core
`isHomogeneousSliceDatum_sum_smul` (a finite `ℝ`-combination version; the main theorem applies it
with `c := fun j => φ j t`, matching `separatedField`/`separatedPath` by `rfl`):

1. **Concrete linearity of the datum constructor** (no integrability side conditions, because every
   profile is Schwartz):
   * `schwartzAngularFourier_finsetSum_smul`: `D01`'s `schwartzAngularFourier` is
     `schwartzAngularDilation ∘ 𝓕`, a composition of two `ℂ`-CLMs, so it commutes with finite
     `ℝ`-combinations by `map_sum` + `ContinuousLinearMap.map_smul_of_tower`.  (`𝓕` on Schwartz maps
     is `SchwartzMap.fourierTransformCLM ℂ`, a CLM.)
   * `homogeneousProfile_finsetSum_smul_apply`: pointwise, `|ξ|^s ·` the above.
   * `homogeneousDatum_finsetSum_smul` (needs `-3/2 < s`): the `L²` datum
     `(memLp_homogeneousProfile hs φ).toLp` of the combination is the combination of the data, by
     `Lp.ext` + `homogeneousDatum_ae` + `Lp.coeFn_finsetSum` / `Lp.coeFn_smul` + the pointwise
     identity.  Lifted to the vector datum coordinate-wise inside
     `isHomogeneousSliceDatum_sum_smul` via `WithLp.ofLp_injective` + `Subtype.ext` +
     `homogeneousVectorDatum_coe` + `B01.coe_sum_smul_apply`, with the `i`-th slice component equal
     to `Σ_j c_j •` (`i`-th component of `h_j`) by `SchwartzMap.ext` + `B01.space_sum_apply`.
2. **Uniqueness** (`D01.isHomogeneousSliceDatum_unique`, unconditional in `s`): each given `A_j`
   equals the canonical datum `homogeneousVectorDatum` of `h_j`'s Schwartz components (via
   `D01.isHomogeneousSliceDatum_schwartz`).
3. **Existence for the slice** (`D01.isHomogeneousSliceDatum_schwartz`): the slice is smooth compact
   (`ContDiff.sum` of `const_smul`; `hasCompactSupport_sum_smul`, proved here since mathlib has no
   `HasCompactSupport.sum`), so its canonical datum is a homogeneous slice datum; by step 1 that
   datum is `Σ_j c_j • A_j`.

## 3. Where `-3/2 < s` enters

Only through `homogeneousDatum_finsetSum_smul` / the `homogeneousVectorDatum` constructor:
`D01.memLp_homogeneousProfile` needs `-3/2 < s` for `∫_{|ξ|<1} |ξ|^{2s} dξ < ∞`.  This is exactly
the range every consumer already lives in: `approxCompactHomogeneous` (`Spec.lean:607`) uses
`SplitRange s = (-3/2 < s ∧ s ≤ 0)`, which implies `-3/2 < s`.  So the restriction costs nothing
downstream; the contract lane decides whether the registered field keeps `∀ s : ℝ`.

## 4. Why the verbatim `∀ s : ℝ` field is NOT provable by this route

At `s ≤ -3/2` the constructor `homogeneousVectorDatum` does not exist (its `memLp` witness fails),
so steps 1 and 3 of the F1 route are unavailable.  The **given** hypothesis `hA j` still supplies a
datum for each `h_j` at any `s`, so the verbatim field is presumably true for all `s`; but reaching
it needs the **general-additivity route** (`REMAINING_SPLIT.md` row 6), which the reviewer's F1
deliberately avoids:

* a finite-`sum` + scalar-`smul` combinator for `IsHomogeneousDatum` (self-contained, unconditional
  in `s`, mirroring `D01.isHomogeneousDatum_sub`), lifted to `IsHomogeneousVectorDatum`;
* a finite-`sum` + scalar-`smul` combinator for `IsSliceDistribution`, which carries per-term
  integrability side conditions (the totalization caveat that refuted the hypothesis-free
  `homogeneousDatumSub`, `REVIEW_U6.md` §4) — dischargeable here because each `h_j` is smooth
  compact, via `B01.integrable_schwartz_mul`, exactly as `B01`'s `isSobolevPath_separated` `hRHS`;
* `angularFourierDistribution` linearity (`map_sum`/`map_smul`) and `𝓢'` / `VectorDistribution`
  sum-smul evaluation.

That route (`REMAINING_SPLIT.md` estimate 110-160 ln) would prove the field for all real `s`.  It
was **not** taken, per the task's instruction to follow the reviewer's shorter route and record the
trade-off for the contract lane.

## 5. Approaches that failed / needed adjustment during coding

* `HasCompactSupport.sum` — **does not exist** in this mathlib.  Replaced by
  `hasCompactSupport_sum_smul`, proved directly: `support (Σ_j c_j h_j) ⊆ ⋃_j tsupport (h_j)`
  (finite union of compacts), via `closure_minimal` + `image_eq_zero_of_notMem_tsupport`.
* `SchwartzMap.sum_apply` / `SchwartzMap.smul_apply` — **deprecated** (since 2026-06-10) in favour
  of the unqualified `sum_apply` / `smul_apply` (from the `IsAddApply` / `IsSMulApply` classes).
  Using the deprecated aliases left warnings; switched to the unqualified names so the module is
  silent under `lake env lean`.
* `push_neg` — **deprecated** in favour of `push Not`.  Rewrote the `hasCompactSupport_sum_smul`
  proof to derive the per-`j` non-membership directly from the negated `∃`, with no `push_neg`.
* Scratch files needed `open NavierStokes.ProblemStatement` for the `NormedAddCommGroup Space`
  instance; folded into the module opens.

No approach that was tried produced a wrong statement or an extra axiom; the only genuine
limitation is the `-3/2 < s` hypothesis of §3-4.

## 6. Commands run (from the worktree, `. scripts/lean-env.sh` first)

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.B02.SeparatedAssembly` | `Build completed successfully (9881 jobs)`, `✔ Built …SeparatedAssembly`; only pre-existing `Source.*`/`Paper3.*` dependency warnings |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean` | silent, exit 0 |
| `cd verification && lake env lean ../research/B02/axioms_separated.lean` | example typechecks; all 6 public decls exactly `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `make check` (worktree root) | architecture checks OK; `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items … consistent" |
