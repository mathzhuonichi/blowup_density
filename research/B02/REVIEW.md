# B02 review — homogeneous `Ḣ^{-1}` approximation (lane 022)

**Verdict: ACCEPT-WITH-NOTES.**  `Spec.lean` typechecks clean, is hygienic, and
all 20 fields are faithful to `prop:Renergy`'s `Ḣ^{-1}` paragraph.  Both
constants are correct and are the ones the manuscript's convention forces.  The
`s`-range, the two drafting corrections, the reuse table and the "realization
half is empty" claim all check out; every source line number sampled (24, Lean
and LaTeX, local and Mathlib) is exact.  The notes below are documentation and
sizing only — nothing blocks promotion.

## 1. Ranked issues

| # | Sev | Where | What differs | One-line fix |
|---|---|---|---|---|
| 1 | low | `COMPARISON.md:303` | §5 item 7 reads "`make check` — see below" but no `make check` result appears anywhere below; the "Failures and deviations" block never mentions it.  (`make` has a `check:` target, so the run was possible.) | Report the exit status, or drop item 7. |
| 2 | low | `COMPARISON.md:245-253` (unit table) | Sizing is optimistic in three rows.  Unit 6 (`homogeneous_datum_of_lebesgue`) is existence **+** the norm clause **+** `homogeneousDatumSub`, and is the first inhabitant of `Data.lean`'s homogeneous half — `L` understates it.  Unit 8 folds `cutoffLebesgue` *and* the diagonal consuming units 1, 2, 6, 7 into one `M`.  Unit 3's exact `= 4π` evaluation via `MHS:296` is rarely `S` in practice. | Unit 6 → `XL` (or split existence / norm / linearity); unit 8 → `L`; unit 3 → `S/M`. |
| 3 | info | `Spec.lean:98` ("`B01`'s covers every real `s`") | Sits one line after the `0 ≤ s < 3/2` sentence and can be misread as B01 covering *homogeneous* density at every real `s`; it means B01's inhomogeneous `H^s` clause (`04:239`). | "…`B01`'s **inhomogeneous** clause covers every real `s`". |
| 4 | info | `Spec.lean:344-346` (`annularSchwartz` docstring) | "`‖h_n − h‖_{Ḣ^s} = ‖W − A‖` by `02-preliminaries.tex:63`" — `Data.lean:338 homogeneousENorm` is an **infimum** over data, so that equality needs the norm clause of `lebesgueHomogeneousDatum` (or L7 uniqueness), not `:63` alone.  Harmless: no *field* is phrased with `homogeneousENorm`; the contract measures only `‖·‖ₑ` on `RealVectorSobolev s`, which is why `⨅ ∅ = ⊤` never bites. | Add "…once the norm clause of `lebesgueHomogeneousDatum` is available". |
| 5 | info | `COMPARISON.md:71-81` | Says "eleven homogeneous `Data.lean` names"; the bullet actually lists **twelve** (`IsSliceDistribution` included).  All twelve verified at 0 external users, so the claim holds a fortiori. | Say twelve. |

No mismatch was found between any field and the paper, and no over- or
under-statement of a quantifier, hypothesis or constant.
## 2. Constants, derived independently

Convention (`01-introduction.tex:91`): `ẑ(ξ) = (2π)^{-3/2}∫e^{-ix·ξ}z(x)dx`.

* **`L¹→L^∞`.** `|ẑ(ξ)| ≤ (2π)^{-3/2}‖z‖₁`; for a *vector* field, by the
  triangle inequality for the ℂ³-valued integral,
  `(Σ_i|ẑ_i(ξ)|²)^{1/2} ≤ (2π)^{-3/2}∫‖z(x)‖dx`, and `‖·‖₁` of a vector field
  **is** `∫(Σ|z_i|²)^{1/2}` by `01-introduction.tex:103-104`.  So
  `fourierSupBound` is **right**, vector form included, and squaring gives the
  manuscript's unnamed `C = (2π)^{-3}`. ✔
* **The origin integral.** `∫_{|ξ|<1}|ξ|^{2s}dξ = 4π∫_0^1 r^{2s+2}dr =
  4π/(2s+3)`, finite iff `s > -3/2`; at `s = -1` this is `4π` — **right**. ✔
* **`C'`.** `lowHighConstant s = (2π)^{-3}·4π/(2s+3) = 1/(2π²(2s+3))`; at
  `s = -1`, `1/(2π²) ≈ 0.05066`.  `lowHighConstant` and
  `rnegativeCutoffConstant = 1/(2π²)` are **both right**, and their equality at
  `s = -1` was proved in Lean (scratch check 6) from the `4π` field alone.
* **High half coefficient `1`.** `angularFourier` is unitary (`(2π)^{-3}·(2π)³
  = 1` after `ξ = 2πη`), so `+ eLpNorm k 2 volume ^ 2` is exact. ✔

## 3. `s`-range

`SplitRange s = -3/2 < s ∧ s ≤ 0` is **exactly** what the argument covers.
`-3/2 < s` is the convergence of `∫_{|ξ|<1}|ξ|^{2s}` (`04:249`; hypothesis `hs`
of `SW:54`); `s ≤ 0` is `|ξ|^{2s} ≤ 1` on `|ξ| ≥ 1` (`04:246-247`; hypothesis
`hs0` of `HT:14`).  Field-by-field the hypotheses are placed correctly:
`lowFrequencyIntegrable` carries only `-3/2 < s`; `lowHighSplit`,
`lebesgueHomogeneousDatum`, `spatialApproxHomogeneous`,
`approxCompactHomogeneous` carry both; the annular, Schwartz, cutoff, Bochner
and linearity fields carry none — correctly, since none touches the weight.
`s = -1` is interior.  Leaving `0 ≤ s < 3/2` to B01 is right and the caveat is
stated precisely: only the **cutoff stage** becomes `B01`'s `cutoffApprox`
(stages 1-2 are still needed there), which the docstring says and does not
overclaim.

## 4. The two drafting corrections — both load-bearing, both correct

1. **Vector, not componentwise.**  A componentwise `‖ẑ_i‖ ≤ (2π)^{-3/2}∫‖z‖`
   summed over `Fin 3` gives `3(2π)^{-3}‖k‖₁²` — `lowHighSplit`'s constant would
   stop being the manuscript's.  The vector form is the correct one. ✔
2. **`L¹∩L²`, not compact support.**  `04:249` applies eq:Rnegative-cutoff to
   `χ_Rh_n − h_n = −(1−χ_R)h_n`, which is Schwartz with **unbounded** support
   (verified in the source line).  `HR:17`'s `ContDiff ∞ + HasCompactSupport`
   hypothesis would not close the diagonal; `MemLp k 1 ∧ MemLp k 2` does, and
   `HT:14` never uses compactness (only `‖φ‖_∞ ≤ C` and `Integrable ‖φ‖²`), so
   the widening is free.  The companion `homogeneousDatumSub` is genuinely
   needed to move the estimate onto `‖H − W‖ₑ`. ✔

## 5. Reuse spot-check (all rows confirmed)

| Cited | Verified | Verdict |
|---|---|---|
| `Paper3/HomogeneousTime.lean:14` `homogeneous_energy_le_bound_add_L2` | line 14; hyps `-3/2<s`, `s≤0`, `hφ`, `‖φ‖≤C`, `Integrable ‖φ‖²`; scalar, `ℝ`, cycles | as described |
| `Paper3/SobolevWeights.lean:54` `homogeneous_low_frequency_integrable` | line 54; hyp `-3/2<s` | as described |
| `Paper3/HomogeneousRealization.lean:17` `compact_homogeneous_norm_bound` | line 17; one `exact` of `HT:47`; header disclaims a full `L²→𝓢'` multiplier; 26 lines | as described |
| `vendor/.../R3/SchwartzCompactApproximation.lean:169` `seminorm_truncate_sub_le` | line 169; real `R`, `0<R`, `1≤R` | as described |
| `vendor/.../R3/ComparisonCutoffs.lean:29` `baseCutoff` | line 29 + `:40,42,44,46,50`; `scaledCutoff baseCutoff R = cutoff R` **by `rfl`** (re-run) | as described |
| `Paper3/SeparatedBochnerDensity.lean:30` `dense_span_separatedLp` | line 30; carrier-generic `H`, any `μ` | as described |
| `Paper3/PositiveTemporalDensity.lean:73` `dense_positive_temporal_factors` | line 73; `tsupport ⊆ Ioi 0` | as described |
| `Source/FractionalRealization.lean:44` `realization` | line 44; `0<a<3/2`, cycles, into `Lp ℂ (ofReal (targetExponent a))` | as described — not usable at `s=-1` |
| `Source/RieszFrequencyCutoffs.lean:14,15` `low`/`high` | lines 14,15; indicators of the **symbol** `‖x‖^{-a}` | as described — not the integral split |
| `Source/FourierConvention.lean:15,23` `frequencyUnit`, `angularFourier` | lines 15,23; `(2π)^{-3/2}•𝓕f((2π)⁻¹•ξ)` | confirms `ξ = 2πη` |
| `ARVB:47,54,120`; `CS:37`; `MSA:82,97`; `MSF:51,279,306`; `MHS:296`; `SchwartzSpace/Basic.lean:1368`; `VolumeOfBalls.lean:311` | all exact | as described |

**Zero external users** — grep over `verification/`, `formalization/`,
`vendor/` excluding `Contracts/V1/Data.lean`: `IsHomogeneousDatum`,
`IsSliceDistribution`, `IsHomogeneousVectorDatum`, `IsHomogeneousSliceDatum`,
`IsHomogeneousPath`, `forceHomogeneousENorm`, `homogeneousENorm`,
`MemHomogeneous`, `MemDotHNegOne`, `homogeneousVectorENorm`,
`homogeneousFourierENorm`, `CompletedDenseHomogeneous` → **0 hits each**.  The
"realization half is empty" claim is **correct**.

**Shared defs** (diff vs `research/B01/Spec.lean`) — `scaledCutoff`,
`schwartzVector`, `separatedField`, `separatedPath`, `SeparatedTemporalDense`
byte-identical; `temporalApprox` identical too; `separatedAssembly` differs in
exactly the two substitutions claimed.

## 6. Gap assessment

* **Unit 6 vs I03 `U7c`.**  `I03/COMPARISON.md:284` says R46's `L²_tḢ^{-1}`
  clause "blocks on U7c specifically"; U7c is the *scaled-family* witness, unit
  6 the *spatial* `L¹∩L²` witness.  B02 words it exactly right ("unit `U7c`'s
  spatial core", `L^q_t` lift deferred to follow-up C).  **Same blocker,
  correctly scoped.**  (I03 cites `Data.lean:321`/`:387`; the current file has
  `:324`/`:390` — B02's numbers are the accurate ones.)
* **Cycles-vs-angular radius 1 is a real transport issue.**  `FC:23` gives
  `ξ = 2πη`, so the *norms* differ only by `(2π)^s` (D01 unit L8), but `HT:14`
  splits at **cycles** radius 1 = angular radius `2π`, while the manuscript
  splits at **angular** radius 1.  Transporting `HT:14` yields a valid but
  different (larger) constant; obtaining the manuscript's `C'` requires
  re-running the majorant argument at angular radius 1, as unit 7 says. ✔
* **`approxCompactHomogeneous`** is literally
  `CompletedDenseHomogeneous q s forceClassCompact`, which unfolds by `rfl`
  (re-run) to `CompletedDenseVia q s (IsHomogeneousPath s) forceClassCompact`.
  `04:228` is respected: the target ranges over `MemBochnerDatum` while `S`
  stays a set of physical fields.

## 7. Check log

1. `cd verification && lake env lean ../research/B02/Spec.lean` → **exit 0**,
   no output, 3.37 s user.
2. Hygiene: no `theorem`/`lemma`/`example`/`instance`/`axiom`/`abbrev`, no
   `sorry`/`admit`/`native_decide`/`opaque`, no `set_option`/`macro`/`unsafe`,
   no `:= by`, no `True` placeholder (only docstring hits); one import; 16
   `def`s; **20 structure fields**.
3. Scratch (`/tmp/b02rev/Scratch.lean`, `lake env lean` → exit 0, then deleted):
   `rfl` for `CompletedDenseHomogeneous = CompletedDenseVia … IsHomogeneousPath`,
   `bochnerDatumENorm = eLpNorm _ q forceTimeMeasure`,
   `forceTimeMeasure = volume.restrict (Ioi 0)`, `schwartzVector ψ x i = ψ i x`,
   `scaledCutoff baseCutoff R = ComparisonCutoffs.cutoff R`; plus
   `lowHighConstant (-1) = 1/(2π²)` from the `4π` hypothesis,
   `((2π)^{-3/2})² = (2π)^{-3}`, `IsHomogeneousDatum (-1)` weight `‖ξ‖^1`,
   `-3/2 < -1 ≤ 0`.
4. Carrier check: `RealVectorSobolev s = PiLp 2 (Fin 3 → realSubspace s)`,
   `realSubspace s ⊆ Lp ℂ 2 volume` the `realSymmetry h = h` subspace with the
   induced `L²` norm — so `‖G‖ₑ = (Σ_i‖G_i‖²)^{1/2}`, matching
   `01-introduction.tex:103` and `homogeneousFourierENorm`'s ℓ² sum.  The
   norm clause of `lebesgueHomogeneousDatum` is therefore the right statement.
5. LaTeX, all as cited: `prop:Renergy` `04:218-229`; `:235` the cutoff `χ`;
   `:241` stages 1-2 + the `k ∈ L¹∩L²` announcement; align `:242-248`, label at
   `:247`; `:249` finiteness + cutoff + diagonal + real parts; `:251-260`
   Bochner; `02-preliminaries.tex:58`; `01-introduction.tex:91,103,105`.
6. Ledger, all as cited: `STATEMENTS.md:803-807, 831-836, 901-905, 917-919`;
   `EXTERNAL_REUSE.md:38`; `DEPENDENCY_GRAPH.md:322-329`;
   `D01/RECONCILIATION.md:158 (L7), :159 (L8)`; `I03/COMPARISON.md:223,284`.

**Not verified:** `scripts/lean-install.sh`, `make check` and `lake build` of
the cited modules were not re-run (the `Spec.lean` typecheck succeeded against
the existing build).
