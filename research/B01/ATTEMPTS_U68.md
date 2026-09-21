# B01 units 6 & 8 — attempts log (lane 048)

Worktree: `.claude/worktrees/048-B01-units-6-8`. Modules under
`formalization/NSFormalization/Section4/B01/`. Conformance: `research/B01/axioms_u68.lean`.
No `Defs.lean` was needed: units 6/8 use only `IsSobolevDatum`, `IsSobolevPath`,
`MemForceCompact`, `forceTimeMeasure` (restated in `Section4/D01/{ForceClass,SmoothDatum}.lean`,
which ARE on this branch) and `RealVectorSobolev`/`angularRealization` (Paper3). None of
`bochnerDatumENorm`/`CompletedDense`/`MemBochnerDatum`/`bochnerSpace` are used by these two units.

## Unit 6 `separatedAssembly` — DONE, builds clean, sorry-free

Module `Section4/B01/Separated.lean`. Theorem `separatedAssembly` (three conjuncts).

Key design decisions (positive results):
- `IsSobolevPath` proved by the DIRECT `map_sum` route recommended by COMPARISON, NOT by iterating
  `D01.isSobolevDatum_add` (which would need pairability of every partial sum). Helpers:
  - `coe_sum_smul_apply`: coordinate `i` of `∑ j, c j • A j` in `RealVectorSobolev s`, coerced to
    `FourierData`, via `coord i` (the FHB projection CLM) + `map_sum`; then `push_cast; simp[map_smul]; rfl`.
  - `space_sum_apply`: same for Euclidean `Space` via `(EuclideanSpace.proj i : Space →L[ℝ] ℝ)`.
  - `angReal_sum_smul`: `angularRealization s (∑ j, c j • x j) ψ = ∑ j, c j • …` via `map_sum, sum_apply`
    and `ContinuousLinearMap.map_smul_of_tower` (angularRealization is ℂ-linear; the scalars are ℝ, so
    plain `map_smul` FAILS — `map_smul_of_tower` is required).
  - `integrable_schwartz_mul`: `∫ ψ x * (h j x i)` integrable because `h j` continuous+compact-support ⇒
    `ψ · (component)` continuous with compact support. No `0 ≤ s` needed (contrast D01
    `schwartzPairable_of_isSobolevDatum`, which does need it).
  - Both sides collapse to `∑ j, φ j t • ∫ x, ψ x * (h j x i : ℂ)`; RHS via `integral_finsetSum` +
    `integral_const_mul` + `Complex.real_smul`.
- `MemForceCompact` via `D01.memForceCompact_of_smooth_support`:
  - smoothness: `ContDiff.sum` of `((hφ j).comp contDiff_fst).smul ((hh j).comp contDiff_snd)`.
  - compact support: `tsupport_finsetSum_subset` (Finset induction, `tsupport_add`) ⊆ finite union of
    single-term supports; each single term compact via `hasCompactSupport_sepTerm` (vector generalization
    of `PBD:54 separated_physical_hasCompactSupport`, `HasCompactSupport.of_support_subset_isCompact (ha.prod hb)`);
    `Set.Finite.isCompact_biUnion` + `IsCompact.of_isClosed_subset`.
  - `tsupport ⊆ Ioi 0 ×ˢ univ`: same union, each single term `tsupport_sepTerm_subset ⊆ Prod.fst⁻¹(tsupport φ j) ⊆ {0<z.1}` (`PPD:47-53` pattern).
- measurability: `separatedPath` is continuous (`continuous_finsetSum` of `(φ j).continuous.smul continuous_const`),
  `.aestronglyMeasurable`. NEEDED `have : SecondCountableTopologyEither ℝ (RealVectorSobolev s) := ⟨Or.inl inferInstance⟩`
  because `Continuous.aestronglyMeasurable`'s instance search TIMED OUT on that class (ℝ domain is 2nd-countable,
  so the left disjunct discharges it; supplying it explicitly avoids the timeout).

Failed/aborted approaches:
- `rw [map_smul]` on `angularRealization s (c • x)` with `c : ℝ`: FAILS (`MulActionHomClass … ℝ …`), because
  the CLM is ℂ-linear. Fix: `ContinuousLinearMap.map_smul_of_tower`.
- `PiLp.finset_sum_apply` / `PiLp.sum_apply`: DO NOT EXIST. Coordinate-of-sum must go through the projection CLM
  (`coord`/`EuclideanSpace.proj`) + `map_sum`.
- `Continuous.aestronglyMeasurable` bare: instance timeout (see above).

Conformance `axioms_u68.lean`: unit-6 `example` typechecks; `#print axioms separatedAssembly` =
`[propext, Classical.choice, Quot.sound]`.

## Unit 8 `spatialApprox` — DONE, builds clean, sorry-free

Module `Section4/B01/Spatial.lean` (imports `B01/Separated.lean` to reuse its `SpatialField`
abbrev — otherwise the two modules would each declare `SpatialField` in the same namespace and
clash when both are imported by the conformance file; the lead can dedupe at merge). Theorem
`spatialApprox`.

Construction (positive results):
- Spatial assembly `spatialVector g x = WithLp.toLp 2 (fun i => g i x)` (spatial analogue of
  `RVPD:18 physicalVector`), with `spatialVector_smooth` (`(contDiff_piLp 2).mpr`),
  `spatialVector_support` (copy of `RVPD:28`, needs `show g i x = 0` before
  `image_eq_zero_of_notMem_tsupport`), `spatialVector_compact`.
- `spatialCyclesVector s ψ := WithLp.toLp 2 (fun i => realProjectionTo s (weightedFourierLp s (ψ i)))`
  and `spatialDatum s ψ := cyclesToAngularRealVector s (spatialCyclesVector s ψ)`, with rfl-lemmas
  `spatialCyclesVector_apply`, `spatialDatum_eq` (introduced as top-level defs to AVOID `set`/`let`
  local-def unfolding, which caused `whnf`/`isDefEq` heartbeat TIMEOUTS in an earlier draft).
- `spatialDatum_isSobolevDatum`: the pairing, via `cyclesToAngularRealVector_apply`,
  `ARS:89 angularRealization_cyclesToAngularReal`, coe of `realProjectionTo` (`= realProjection`,
  rfl), `weightedFourierLp_realPart` (REVERSED: `realProjection (wFLp ψ) = wFLp (realPartSchwartz ψ)`),
  `CSR sobolevRealization_weightedFourierLp`, `SchwartzMap.coe_apply`, `realPartSchwartz_apply`.
  This route AVOIDS proving a "reality of compactFourierLp" lemma and AVOIDS realProjection
  idempotency — the physical field is `spatialVector (fun i x => (ψ i x).re)`.
- Density/norm: `dense_compact_weightedFourierLp s` + `Metric.mem_closure_iff` per component gives
  compact-smooth `ψ i` with `‖wFLp s (ψ i) - realSobolevInclusion s (A_c i)‖ < δ`
  (`A_c := (cyclesToAngularRealVector s).symm A`, the cycles reading). Then
  `‖spatialCyclesVector s ψ i - A_c i‖ ≤ δ` via `realProjectionTo_inclusion` + `map_sub` +
  `realProjectionTo_norm_le`; `norm_le_sum_coord` (proved from FHB `reconstruction` + `norm_sum_le`
  + `norm_insert`) gives `‖·‖ ≤ ∑ ≤ 3δ`; `cyclesToAngularRealVector_norm_le` gives the constant
  `frequencyUnit^|s|`. δ chosen `= η.toReal/(3*(frequencyUnit^|s|+1))` so
  `frequencyUnit^|s| * 3δ < η.toReal` strictly (nlinarith with `div_mul_cancel₀`), giving strict
  `< η` after `ofReal_norm` + `ENNReal.ofReal_lt_ofReal_iff_of_nonneg`. η = ⊤ branch: `ENNReal.ofReal_lt_top`.

Failed/aborted approaches and pitfalls:
- `set Hv := WithLp.toLp …` / `let`: caused `whnf`/`isDefEq` HEARTBEAT TIMEOUTS in the norm block
  (deep RealVectorSobolev/CLE defeq). Fix: top-level defs + rfl `_apply` lemmas, and file-level
  `set_option maxHeartbeats 2000000` (ARVB uses 800000, RPD 8000000 — heavy defeq is normal here).
- `set_option maxHeartbeats N in` placed between a `/-- -/` docstring and the theorem: PARSE ERROR
  ("expected 'lemma'") — the doc comment must directly precede the declaration. Fix: file-level
  `set_option` after `noncomputable section`.
- `rw [hAci]` where `hAci : A_c i = realProjectionTo s (realSobolevInclusion s (A_c i))` — `A_c i`
  occurs on BOTH sides ⇒ loops. Fix: rewrite the whole difference via
  `show … = realProjectionTo s (wFLp - incl) from by rw [map_sub, realProjectionTo_inclusion]`.
- `dist`/`norm`: `dense_compact_weightedFourierLp` + `Metric.mem_closure_iff` yields a `dist`; need
  `rw [norm_sub_rev, ← dist_eq_norm]` to match.
- Two modules each declaring `abbrev SpatialField` in `NSFormalization.Section4.B01`: import clash.
  Fix: Spatial imports Separated and reuses its `SpatialField`.
- `positivity` does NOT prove `0 < η.toReal` (only ≥ 0). Use `ENNReal.toReal_pos hη.ne' hηtop`.

Conformance `axioms_u68.lean`: both unit-6 and unit-8 `example`s typecheck;
`#print axioms {separatedAssembly, spatialApprox}` = `[propext, Classical.choice, Quot.sound]`.

## Commands and results (from WT/verification, after `. ../scripts/lean-env.sh`, LEAN_NUM_THREADS=6)

- `lake build NSFormalization.Section4.B01.Separated` — Build completed successfully (9878 jobs).
- `lake build NSFormalization.Section4.B01.Spatial` — Build completed successfully (9879 jobs).
- `lake env lean ../formalization/NSFormalization/Section4/B01/Separated.lean` — no output (clean).
- `lake env lean ../formalization/NSFormalization/Section4/B01/Spatial.lean` — no output (clean).
- `lake env lean ../research/B01/axioms_u68.lean` — both `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Review fixes (lane 048, ACCEPT-WITH-NOTES → applied)

Per `research/B01/REVIEW_U68.md`:

- **F1 (MEDIUM).** Deleted `Separated.lean`'s `abbrev SpaceTimeField := VelocityField` — lane 035's
  already-merged `B01/Compact.lean` declares the same name in the same namespace
  `NSFormalization.Section4.B01`, so unit 10 (which imports both) would hit
  `environment already contains 'NSFormalization.Section4.B01.SpaceTimeField'`. `separatedField`'s
  return type is now spelled `VelocityField` directly (the spelling `D01/ForceClass.lean` uses;
  `= Contracts.V1.Data.SpaceTimeField`). `SpaceTimeField` occurred only in `Separated.lean`;
  `Spatial.lean` never used it. `SpatialField` is NOT declared by 035, so it stays.
- **F2 (MEDIUM).** Deleted the file-level `set_option maxHeartbeats 2000000` from `Spatial.lean`
  and replaced it with a targeted `set_option maxHeartbeats 400000 in` immediately ABOVE the
  `spatialApprox` docstring (the `Section4/A03/RealAngularProduct.lean:111` idiom). Only
  `spatialApprox` needs the bump (reviewer bisected floor 350000; 400000 leaves headroom); every
  other declaration in the file compiles at the default. (Supersedes the earlier note that
  justified the file-level 2000000.)
- **F4 (NIT).** Stale `Spec.lean` line refs `:135,143` → `:140,147` in `Separated.lean` (§0 docstring,
  `:48`, and the two def docstrings) and `axioms_u68.lean` (`:16,29,34`).
- **F5 (NIT).** Removed the double blank line between `spatialVector_smooth` and
  `spatialVector_support` in `Spatial.lean`.

Rebuild + audit after fixes (from `WT/verification`, `. ../scripts/lean-env.sh`, LEAN_NUM_THREADS=6):
- `lake build NSFormalization.Section4.B01.Separated NSFormalization.Section4.B01.Spatial` — Build completed successfully (9879 jobs); no B01 warnings.
- `lake env lean ../formalization/NSFormalization/Section4/B01/Separated.lean` — no output (clean).
- `lake env lean ../formalization/NSFormalization/Section4/B01/Spatial.lean` — no output (clean).
- `lake env lean ../research/B01/axioms_u68.lean` — both `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- `make check` (from WT root) — exit 0.
