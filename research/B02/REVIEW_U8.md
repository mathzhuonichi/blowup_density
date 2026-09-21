# Review — lane 060, task B02, unit 8 (`Section4/B02/Cutoff.lean`)

Reviewer: independent opus reviewer. Worktree
`/data_8T/ping/blowup_density/.claude/worktrees/060-B02-unit-8` at commit `9ade37a`.
Read/build only; no code changed.

## Verdict: **ACCEPT-WITH-NOTES**

`cutoffLebesgue` is proved unconditionally and is the spec field verbatim at
`χ := baseCutoff`. `spatialApproxHomogeneous_of` concludes the spec field
`spatialApproxHomogeneous` from four hypotheses that are token-for-token the spec
fields `annularSchwartz`, `lebesgueHomogeneousDatum`, `homogeneousDatumSub`,
`lowHighSplit`. Both are on `[propext, Classical.choice, Quot.sound]`. Build,
conformance and `make check` all clean. Two LOW notes below; neither blocks the
merge and neither requires a change to this lane.

---

## 1. Commands and results

All from the worktree, after `bash scripts/lean-install.sh` (`== OK`),
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, one lake at a time.

| # | command (cwd) | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` (WT) | `== OK` |
| 2 | `lake build NSFormalization.Section4.B02.Cutoff` (WT/verification) | `Build completed successfully (8815 jobs).`  exit 0 |
| 3 | re-run of 2, full log captured | 13 warnings, **all** from pre-existing modules (`Paper3/RealPositiveDensity`, `Paper3/RealVectorPositiveDensity`, `Paper3/SpatiallyCompactTime`, `Source/FiniteHilbertBochner`, `Source/RealSobolev`). **Zero** lines mentioning any `Section4/B02/*.lean`. |
| 4 | `lake env lean ../research/B02/axioms_u8.lean` (WT/verification) | exit 0, no errors — both `example`s type-check — and exactly:<br>`'NSFormalization.Section4.B02.cutoffLebesgue' depends on axioms: [propext, Classical.choice, Quot.sound]`<br>`'NSFormalization.Section4.B02.spatialApproxHomogeneous_of' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| 5 | `grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" Cutoff.lean` | one hit, `Cutoff.lean:32`, the word "axioms" inside the module docstring (`research/B02/axioms_u8.lean`). Nothing outside comments. Same grep on `axioms_u8.lean`: no hits outside the `#print axioms` lines and the header comment. |
| 6 | `make check` (WT) | exit 0 — `check_formalization_plan --check`, `check_contracts`, `test_contract_policy` (13 tests OK), `check_work_queue` (`30 work items: ownership, contract registration and task cards consistent.`) |

Commit touches exactly three new files (`Cutoff.lean` 424 lines, `axioms_u8.lean`
112, `ATTEMPTS_U8.md` 96); no registry/plan edits, nothing deleted.

## 2. `cutoffLebesgue` vs `Spec.lean:489-497` — conforms

Whitespace-normalized comparison of `Spec.lean:489-497` against
`Cutoff.lean:221-233`: identical after the single substitution `χ → baseCutoff`.
Both `Filter.Tendsto … Filter.atTop (nhds 0)` conjuncts present, at `1` and at `2`
with `R : ℝ → ∞`, over `eLpNorm (fun x => (1 - scaledCutoff χ R x) • schwartzVector ψ x) p volume`.
`scaledCutoff` and `schwartzVector` are copied verbatim from `Spec.lean:199,206`.

The spec field is quantified over the structure's own field
`χ : Space → ℝ` (`Spec.lean:278`), constrained by `chi_smooth` (`:280`),
`chi_one` (`:282`, `‖x‖ ≤ 1 → χ x = 1`), `chi_vanishes` (`:285`, `2 ≤ ‖x‖ → χ x = 0`)
and `chi_range` (`:287`, `χ x ∈ Icc 0 1`) — the B01 pattern, as the layout comment
at `Spec.lean:249` says ("Identical to `B01`'s five fields"). So the API instance
picks `χ`, and instantiating at `baseCutoff` is the intended discharge **provided
`baseCutoff` meets those four**. It does, exactly, in the vendor file
`vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean`:
`baseCutoff_smooth` (:40), `baseCutoff_nonneg` (:42) + `baseCutoff_le_one` (:44)
for `chi_range`, `baseCutoff_eq_one {‖x‖ ≤ 1}` (:46), `baseCutoff_eq_zero {2 ≤ ‖x‖}` (:50).
So unit 9 can set `χ := baseCutoff` and close all four χ-fields from the vendor.
`Cutoff.lean:60` `scaledCutoff_baseCutoff : scaledCutoff baseCutoff R = cutoff R := rfl`
records the bridge; `ComparisonCutoffs.cutoff R x := baseCutoff (R⁻¹ • x)` (:32), so
`rfl` is honest.

## 3. The conditional diagonal — token-for-token, conforms

Mechanical whitespace-normalized diff of the four binders of
`spatialApproxHomogeneous_of` (`Cutoff.lean:295-314`) against the spec fields:

| binder | spec field | line | match |
|---|---|---|---|
| `hAnnularSchwartz` | `annularSchwartz` | `Spec.lean:362-364` | identical |
| `hLebesgueDatum` | `lebesgueHomogeneousDatum` | `Spec.lean:454-458` | identical |
| `hDatumSub` | `homogeneousDatumSub` | `Spec.lean:470-472` | identical |
| `hLowHighSplit` | `lowHighSplit` | `Spec.lean:421-425` | identical |
| conclusion | `spatialApproxHomogeneous` | `Spec.lean:515-518` | identical |

Nothing is weakened: `lebesgueHomogeneousDatum` keeps **both** clauses (existence
and the "every datum has the Fourier norm" clause); `lowHighSplit` keeps the
constant `lowHighConstant s` and the coefficient `1` on the `L²` term;
`homogeneousDatumSub` is the unrestricted form with no integrability side
condition; the conclusion keeps `ContDiff ℝ ∞ h ∧ HasCompactSupport h`.
No extra hypothesis has been smuggled in — the theorem has exactly these four
binders plus the conclusion's own `∀ s, SplitRange s → ∀ A η, 0 < η →`.

The conformance `example` at `axioms_u8.lean:86-110` is a real check, not a
tautology: the semantically loaded predicates in it (`SpatialField`,
`IsHomogeneousSliceDatum`, `homogeneousFourierENorm`, `MemLp`, `eLpNorm`) resolve
to the **frozen** `BlowupDensity.Contracts.V1.Data` copies via
`open BlowupDensity.Contracts.V1.Data` (`Contracts.V1.Data` is imported;
`NSFormalization.Section4.B02` is *not* opened, so there is no ambiguity), and
only the four Spec-only `def`s that have no home on the module path
(`closedFrequencyAnnulus`, `IsAnnularDatum`, `scaledCutoff`, `schwartzVector`,
`SplitRange`, `lowHighConstant`) are mirrored in `SpecMirror`. I checked each
mirror against its `Spec.lean` line (`:161, :172, :199, :206, :231, :237`) — all
verbatim. So the `example` genuinely certifies conformance to `Data.lean` for the
parts that matter, and to `Spec.lean` for the rest.

The proof body itself is a faithful reading of `04-whole-space.tex:249`: annular
restrict (`ε/4`) → annular smooth (`ε/4`) → `annularSchwartz` → pick `R ≥ 1` with
the low/high bound `< (ε/4)²` → `lebesgueHomogeneousDatum` + `homogeneousDatumSub`
give the datum `W − H_diff` of `χ_R h_n` → triangle inequality `< ε ≤ η`. The
`R ≥ 1` conjunct is genuinely used (`cutoff_hasCompactSupport` needs `0 < R`).

### Composition with lane 059's `lowHighSplit`

The two files cannot be imported together in this worktree (`LowHigh.lean` does
not exist here and I am not permitted to copy it in), so this is an **eye
comparison of the two types**, not a machine check.

059's theorem
(`/data_8T/ping/blowup_density/.claude/worktrees/059-B02-unit-7/formalization/NSFormalization/Section4/B02/LowHigh.lean:199`)
is stated with the **bodies written out** rather than through the named `def`s:

```
theorem lowHighSplit (s : ℝ) (hs : -3/2 < s) (hs0 : s ≤ 0)
    (k : Space → Space) (hk1 : MemLp k 1 volume) (hk2 : MemLp k 2 volume) :
    ((∑ i : Fin 3, ∫⁻ ξ : Space,
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
          ‖angularFourier (fun x => ((k x i : ℝ) : ℂ)) ξ‖ ^ 2)) ^ ((2:ℝ)⁻¹)) ^ (2:ℝ) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(3:ℝ)) * ∫ ξ in Metric.ball (0:Space) 1, ‖ξ‖ ^ (2*s))
        * eLpNorm k 1 volume ^ (2:ℝ) + eLpNorm k 2 volume ^ (2:ℝ)
```

Character-by-character, the left side is the body of `Cutoff.lean:263`
`homogeneousFourierENorm` applied to `k` and the constant is the body of
`Cutoff.lean:272` `lowHighConstant s`; `angularFourier` is the same constant in
both (`NSFormalization.Source`, via `FourierConvention`); `SpatialField` is the
`abbrev` for `Space → Space`. So the two **do** compose after merge, by
definitional unfolding of the two `def`s, with one cosmetic adapter for the
bundled range predicate:

```lean
example : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField, MemLp k 1 volume → MemLp k 2 volume →
    homogeneousFourierENorm s k ^ (2:ℝ) ≤
      ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2:ℝ) + eLpNorm k 2 volume ^ (2:ℝ) :=
  fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2
```

(the `hs.1 hs.2` is note 2 below). **Unverified by machine** — flagged as such.

## 4. Duplication — checked, **no same-namespace collision**

Every name declared in `Cutoff.lean` was cross-listed against every other file
that opens `namespace NSFormalization.Section4.B02` — `Annular.lean` and
`LowFrequency.lean` in this worktree, plus lane 059's `LowHigh.lean`:

* `Cutoff.lean` (20): `scaledCutoff`, `schwartzVector`, `scaledCutoff_baseCutoff`,
  `schwartzVector_apply`, `norm_le_sum_norm`, `schwartzVector_contDiff`,
  `schwartzVector_memLp`, `tendsto_eLpNorm_cutoff_compl`,
  `tendsto_eLpNorm_cutoff_compl_vector`, `cutoffLebesgue`, `SpatialField`,
  `VectorDistribution`, `IsSliceDistribution`, `IsHomogeneousDatum`,
  `IsHomogeneousVectorDatum`, `IsHomogeneousSliceDatum`, `homogeneousFourierENorm`,
  `SplitRange`, `lowHighConstant`, `spatialApproxHomogeneous_of`.
* `Annular.lean` (22): `frequencyAnnulus`, `closedFrequencyAnnulus`,
  `IsAnnularDatum`, `IsAnnularRestriction`, `IsAnnularSupported`,
  `measurableSet_frequencyAnnulus`, `isClosed_closedFrequencyAnnulus`,
  `neg_mem_frequencyAnnulus`, `enorm_sub_lt_of_forall_le`, `exists_real_le_enorm`,
  `tendsto_eLpNorm_annulus_compl`, `annularTruncLp`, `annularTruncLp_ae`,
  `annularTruncLp_mem`, `annularRestriction`, `annularCutoff`, `annularCutoff_smooth`,
  `annularCutoff_nonneg`, `annularCutoff_le_one`, `annularCutoff_eq_one`,
  `annularCutoff_support`, `annularSmoothing`.
* `LowFrequency.lean` (3): `lowFrequencyIntegrable`, `lowFrequencyIntegral`,
  `fourierSupBound`.
* 059 `LowHigh.lean` (10): `fourier_mul_formula`, `l2_fourier_pairing`,
  `coeFn_l2Fourier_ae`, `eLpNorm_fourierIntegral_eq`, `sq_eLpNorm_two`,
  `finrank_space_eq_three`, `lintegral_comp_const_smul`,
  `angular_lintegral_eq_cycles`, `angular_plancherel`, `lowHighSplit`.

**Pairwise intersection is empty.** In particular 059's `LowHigh.lean` restates
none of the datum chain — it writes the bodies out inline instead — so unit 9
importing `Cutoff` and `LowHigh` together will **not** hit
`environment already contains`. The MEDIUM hazard the brief anticipated is not
real. (`Cutoff.lean` imports `Annular.lean` and already builds, which is direct
evidence for that pair; the other two are read-off comparisons.)

See note 1 for the residual (non-blocking) copy hazard against `D01`.

## 5. Honesty of `ATTEMPTS_U8.md` — spot-checks pass

Four of the seven recorded snags checked against the actual Mathlib in
`verification/.lake/packages/mathlib`:

* **Snag 2** ("`tendsto_finset_sum` is deprecated → `tendsto_finsetSum`"):
  confirmed. `Mathlib/Topology/Algebra/Monoid.lean:951`:
  `@[deprecated (since := "2026-04-08")] alias tendsto_finset_sum := tendsto_finsetSum`.
* **Snag 3** ("`zero_le'` is deprecated"): confirmed.
  `Mathlib/Algebra/Order/IsBotOne.lean:41-42`:
  `@[deprecated (since := "2026-05-27")] alias zero_le' := zero_le`.
* **Snag 4** ("`SchwartzMap.coe_sub` does not exist"): confirmed. The only
  `coe_sub` in `Mathlib/Analysis/Distribution/` are deprecated aliases in the
  *other* namespaces `TestFunction` (`TestFunction.lean:206`) and
  `ContDiffMapSupportedIn` (`:232`). `SchwartzMap` has only a deprecated
  `sub_apply` (`SchwartzSpace/Basic.lean:368`). The recorded `rfl`-based
  workaround is what the file actually does (`Cutoff.lean:144-147`).
* **Snag 7** ("`FourierData` unknown until the `open` was added"): the
  `open NSFormalization.Source.RealSobolev (FourierData)` line is indeed present
  in `axioms_u8.lean` and is needed by the mirrored `IsAnnularDatum`.

The "Commands run" section of `ATTEMPTS_U8.md` reports `8815 jobs` and
"no warnings/errors in `Cutoff.lean`" — both reproduced exactly (rows 2 and 3
above). Also honest about what is *not* proved: the file states plainly that
`spatialApproxHomogeneous_of` is conditional on units 2/6/7. No overclaiming
found.

## 6. Findings

### Finding 1 — LOW. Third copy of the `Data.lean` datum chain in `NSFormalization`.
*Declarations:* `Cutoff.lean:235-265` — `SpatialField`, `VectorDistribution`,
`IsSliceDistribution`, `IsHomogeneousDatum`, `IsHomogeneousVectorDatum`,
`IsHomogeneousSliceDatum`, `homogeneousFourierENorm`.

*What:* the same seven declarations already exist twice in the tree — the
authoritative `verification/Contracts/V1/Data.lean:99,284,298,324,358,367,410`
and a first `NSFormalization`-side copy at
`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:226-265`
(namespace `NSFormalization.Section4.D01.Homogeneous`). `Cutoff.lean` makes a
third, in `NSFormalization.Section4.B02`. **Not** a build hazard: the namespaces
differ, so nothing collides now, and nothing in §4 collides for unit 9 either.

The module's justification is sound and I verified it: `verification/lakefile.toml`
has `[[require]] name = "NSFormalization" path = "../formalization"`, so
`NSFormalization` *cannot* import `Contracts.V1.Data` — the copy is forced if the
statements are to live in `NSFormalization`. The only available de-duplication is
to import `NSFormalization.Section4.D01.HomogeneousWitness` and `open` its
namespace (D01 imports only `Paper3.*`, `Source.*`, `NavierStokes.R3.*` — no cycle
with B02, and `Cutoff.lean` already imports `Paper3.AngularFourierDilation`).

*Fix (optional, for whoever writes unit 9 or a later cleanup, not for this lane):*
either import D01's copy and drop `Cutoff.lean:235-265`, or leave it and accept
three copies. Leaving it is defensible — the copies are byte-identical and the
conformance file proves defeq — but a future edit to `Data.lean` now has to be
mirrored in three places, so it is worth a tracked note.

*Related, worth passing to the unit 6 lane rather than this one:* D01 already has
`isHomogeneousSliceDatum_sub` (`HomogeneousWitness.lean:585`) and
`exists_isHomogeneousSliceDatum` / `enorm_of_isHomogeneousSliceDatum` (`:473`,
`:486`, the latter docstring literally citing `Spec.lean:454
lebesgueHomogeneousDatum`, second conjunct). They carry extra hypotheses (Schwartz
components; integrability side conditions), so they are not units 6 as stated —
but they are most of the work.

### Finding 2 — LOW (informational). `SplitRange` is bundled here, split in lane 059.
*Declarations:* `Cutoff.lean:295` `spatialApproxHomogeneous_of`, binder
`hLowHighSplit`, vs 059 `LowHigh.lean:199` `lowHighSplit`.

*What:* this lane's hypothesis takes `SplitRange s` (one argument, the spec's
spelling); 059 proves the same statement with `(hs : -3/2 < s) (hs0 : s ≤ 0)` as
two separate arguments. Not a defect on either side — the hypothesis here is
correct because it is the spec's — but the two do not compose by bare
application.

*Fix:* unit 9 writes `fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2`
(or `hs.left` / `hs.right`; `SplitRange` is a plain `def` conjunction so the
anonymous projections unfold). One line, no change needed in either lane.

## 7. Nothing else found

* No `sorry`/`admit`/`native_decide`/`axiom`/`set_option`/`maxHeartbeats`.
* No hypothesis of `spatialApproxHomogeneous_of` is stronger than its spec field,
  and none is missing.
* No warning attributable to any `Section4/B02` module.
* The commit adds three files and modifies none.
