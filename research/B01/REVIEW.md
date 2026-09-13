# B01 review — Real positive-time Bochner approximation (lane 018)

**Verdict: ACCEPT-WITH-NOTES.**

`research/B01/Spec.lean` typechecks clean, is hygienic, and every field says what the
paper says. The `s`/`q` ranges, the `s < s_q` analysis, the `Data.lean` vocabulary and
the completion object are all correct, and every Lean reuse pointer I sampled is exact.
The notes are: a systematic drift in the *paper* line citations inside the proof of
`prop:Renergy` (quotes verbatim-correct, anchors 1–4 lines off, several landing on the
wrong sentence), one export shape the ledger asks for that is not a single proposition,
and two existing upstream results that `COMPARISON.md` does not credit. Nothing requires
restating a field's mathematical content.

## Ranked issues

| # | Sev | Field / location | What differs | One-line fix |
|---|---|---|---|---|
| 1 | MED | module docstring; `χ` block, `schwartzApprox`, `cutoffApprox`, `spatialApprox`, `temporalApprox`, `compactSubsetForceR`; `COMPARISON.md` §0, §1, §3 | Paper anchors inside the proof drift +1…+4. Actual lines: "Fix any real `s`" **231** (cited 233); `χ`, `χ_R` **235** (cited 238); `‖(1−χ_R)h_n‖_{H^m}→0` **237**; "for every real `s`" **239** (cited 243); "take real parts" **249** (cited 250-252); "Write `X` … `1≤q<∞`" **251** (cited 253); "Approximate each `b_j`" **252** (cited 256 — 256 is the *intervals* sentence); "Thus the finite sum" **260**; proof body **231-260** (cited 232-260). `cor:Rclasses` is **194-196** (quote at 195), not 185-193; `F_c ⊆ F_R` is asserted at **183** ("subclasses of `F_R`"); `F_c` itself at 185 ✓. `02-preliminaries.tex`: conjugate-reflection subspace **73** (cited 74, blank); `H^s` isometry **71-72** (cited 70-74); a.e. identification **62** ✓. `:262-264` for `cor:Rclasses` is one paragraph wide — 262 is right, 264 is the homogeneous insertion estimate. In `COMPARISON.md`: the `Ḣ^{-1}` stage is **241-249** (cited 244-252 / 245-250) and `eq:Rnegative-cutoff` **242-248** (cited 246-248). | Renumber; all quoted text is verbatim-correct, so only the digits change. |
| 2 | LOW | `approxCompact` / derived section | `STATEMENTS.md:825-830` asks B01 for **"finite sums `Σ_{j≤J} φ_j(t) h_j(x)`"** converging to `b`, with the sum in `F_c`. `approxCompact` yields only "some `f ∈ F_c`"; the separated shape is derivable from `temporalApprox`+`spatialApprox`+`separatedAssembly` but is never stated. | Add `def SeparatedCompactDense (q s) : Prop` composing the three, next to `SeparatedTemporalDense`. |
| 3 | LOW | `compactSubsetForceR` row of `COMPARISON.md` (unit 4/5 sizing) | Under-credits reuse. `Paper3/CompactForceAdmissibility.lean:14` `contDiff_compactVectorFourierLp` already does the `contDiff_piLp` vector transport, `:52` `compact_vector_force_sobolev_regular` bundles it with `MemLp … 1`/`2` at every `m`, and `Paper3/CompactAdmissibleForce.lean:44` `admissibleForce_compactForceDistribution` proves `MemForceR`'s *exact shape* (`∀ m, ∃ G, realization ∧ ContDiffOn ℝ ∞ G (Ici 0) ∧ MemLp G 1 ∧ MemLp G 2` on `positiveTimeMeasure`, `Paper3/AdmissibleForce.lean:30`) for every compact smooth `F` — at the complex-cycles level. The claim "the PiLp step … is a one-liner, but none is written" is wrong at that level. | Cite the two files; unit 5 is S–M, not M, and unit 4 has a written template. |
| 4 | LOW | `temporalApprox` row (unit 7 sizing) | `Paper3/SeparatedBochnerDensity.lean:69` `dense_span_physical_separated_sobolev` already composes `dense_span_separatedLp` with compact-smooth spatial coefficients *and* compact-smooth time factors over any `IsFiniteMeasureOnCompacts μ`. Unmentioned; it is the template for units 7+8 (scalar complex, and it uses `Lp.dense_hasCompactSupport_contDiff` rather than `PTD:73`'s `tsupport ⊆ Ioi 0` refinement). | Cite it as the pattern for unit 7. |
| 5 | LOW | `schwartzApprox`, `cutoffApprox` | Both demand a single `ψ : SchwartzMap Space Space`. The paper's stage 1 is componentwise and the source has three `SchwartzMap Space ℂ`. Confirmed: `Mathlib/Analysis/Distribution/SchwartzSpace/{Basic,Deriv,Fourier}.lean` contain no `pi`/`prod` assembly, so this bundling is the *only* reason unit 9 is L. | Restate with `ψ : Fin 3 → SchwartzMap Space ℝ` (unit 9 drops to M), or delete both fields. |
| 6 | INFO | `cutoffApprox` docstring | Says `sobolevENorm` is `⊤` with no datum; `Data.lean:145-155` also records a junk-`0` case. Harmless here — `(1−χ_R)ψ` is Schwartz, hence has a datum — but the stated justification is incomplete. | Add "…or `0` on a slice pairing integrably with no test; unreachable for Schwartz `ψ`". |

## Fidelity findings (all confirmed correct)

* **`s` arbitrary real, `q ∈ [1,∞)`.** `04:239` "for every real `s`"; `04:251` "`1 ≤ q < ∞`".
  `s < s_q` enters **only** at `04:262`, where `cor:Rclasses` supplies the *singular*
  compact force — exactly as the draft claims. `04:264` is the separate homogeneous
  insertion estimate. `manuscriptApproximation`'s unused threshold is the right call,
  and `criticalOrder q.toReal = 2/q − 3/2` matches `04:8`.
* **χ block** = `04:235` verbatim (smooth, `=1` on `‖x‖ ≤ 1`, `=0` on `2 ≤ ‖x‖`, `0 ≤ χ ≤ 1`).
* **Stages.** `schwartzApprox`↔231-235, `cutoffApprox`↔235-239, `spatialApprox`↔239+249,
  `temporalApprox`↔251-260, `separatedAssembly`↔260. Folding "take real parts" into the
  `RealVectorSobolev` carrier is legitimate (`RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)`,
  `RVPD:15`). Absorbing the `H^m→H^s` comparison into `cutoffApprox` is the joint content
  of `04:237`+`04:239`; the `H^m` display itself is no longer stated (acceptable, noted).
* **`approxCompact`** is literally `CompletedDense q s forceClassCompact` — `Data.lean:743`,
  unfolding to `CompletedDenseVia q s (IsSobolevPath s) forceClassCompact` (`:732`). No paraphrase.
* **`compactSubsetForceR`** = `forceClassCompact ⊆ forceClassR`, i.e. `04:183`'s "subclasses of `F_R`",
  which `cor:Rclasses` presupposes. `MemForceR` (`Data.lean:544`) additionally has the first
  conjunct `ContDiffOn ℝ ∞ f futureDomain`, immediate from `MemForceCompact`'s `ContDiff`;
  the docstring's "two clauses" reading is fair.
* **Completion object.** Datum-path primary + `bochnerSpace q s = Lp (RealVectorSobolev s) q forceTimeMeasure`
  secondary, tied by `completionRepresentative`/`Surjective`/`Norm`/`Congr`. Consistent with
  `CompletedDenseVia`, which quantifies the target over `MemBochnerDatum` paths, and with
  `⟪D01:BochnerLq q X⟫` (`STATEMENTS.md:812-814`) — `Lp` supplies strong measurability, a.e.
  identification, simple-function density and `eq:time-norms`. `Surjective`+`Congr` close the
  "misses no element" worry. Correct choice.

## Reuse spot-check (all verified in this worktree)

| Claim | Verified |
|---|---|
| `ARVB:120` `exists_angular_real_vector_positive_physical_approx` | ✓ line 120. `∀ s : ℝ`, `q : ℝ≥0∞` with `[Fact (1 ≤ q)]` and `hq : q ≠ ⊤`; gives `ContDiff ℝ ∞ F`, `HasCompactSupport F`, `tsupport F ⊆ {z \| 0 < z.1}`, real components `f i`, `‖b − …toLp…‖ < ε` on `positiveTimeMeasure`. Class/norm/time-domain/vector-ness all as claimed; **no threshold**. |
| `ARVB:54` `angularRealVectorSlice_pairing` = `IsSobolevDatum` | ✓ **proved** in scratch (e): `IsSobolevDatum s (fun x => F (t,x)) (angularRealVectorSlice s f hf hc t)` closes by `rw [pairing]; simp [hFi]`. |
| `ARVB:64` `memLp_angularRealVectorSlice` | ✓ line 64, every `q : ℝ≥0∞`, so `q = 1, 2` immediate. |
| `ARVB:15/24` `cyclesToAngularRealVector` a `≃L[ℝ]`, **not** an isometry | ✓ def :15; `cyclesToAngularRealVector_norm_le` :24 (doc :23) bounds by `frequencyUnit ^ \|s\|`. Every spec field is a density/limit, so this costs nothing — as `COMPARISON.md` says. |
| `CC` `baseCutoff` :29, `cutoff` :32, `_smooth` :40, `_nonneg` :42, `_le_one` :44, `_eq_one` :46, `_eq_zero` :50 | ✓ all exact. Path is `vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean` (as `COMPARISON.md` says), not `Paper3/`. |
| `SD:43` `denseRange_weightedFourierLp`, `:51` `weightedFourierLp_physicalCutoff_tendsto`, `:59` `dense_compact_weightedFourierLp` | ✓ all three, every real `s`, scalar complex cycles. |
| `SBD:30` `dense_span_separatedLp` | ✓ carrier-generic (`H` any real normed space, any `μ`), conclusion `Dense (Submodule.span …)` — the span-unwrapping cost is real. |
| `PTD:73` `dense_positive_temporal_factors` | ✓ `C_c^∞` factors with `tsupport ⊆ Ioi 0`, dense in `Lp ℝ q positiveTimeMeasure`. |
| `CST:18` `contDiff_compactSobolevTimeSlice` (+`:39`,`:47`) | ✓ scalar complex only. |
| Gap: no `ContDiff` for `realCompactSobolevTimeSlice` / `realVectorSlice` / `angularRealVectorSlice` | ✓ confirmed by grep over `Paper3/` and `Source/` — only `contDiff_compactSobolevTimeSlice` and `contDiff_compactVectorFourierLp` exist (see issue 3). |

## Scratch results (`/tmp/b01_review_scratch{,2}.lean`, both exit 0, deleted)

* `Lp (RealVectorSobolev s) q forceTimeMeasure = Lp … q positiveTimeMeasure` by `rfl` ✓;
  `forceTimeMeasure = positiveTimeMeasure = volume.restrict (Ioi 0)` by `rfl` ✓.
* Source's three clauses ⟹ `MemForceCompact`: `⟨h1, h2, fun z hz => ⟨h3 hz, mem_univ _⟩⟩` ✓,
  and the full existential from `ARVB:120` lands in `forceClassCompact` ✓.
* `scaledCutoff baseCutoff R = cutoff R` by `rfl` ✓; the five `χ` fields discharged from
  `CC:40,46,50,42,44` ✓. `Fact (1 ≤ (1:ℝ≥0∞))`, `Fact (1 ≤ (2:ℝ≥0∞))` by `inferInstance` ✓.
* **B02 interface**: `api.temporalApprox q h1 h2 s : SeparatedTemporalDense q s` typechecks by
  defeq ✓ — so the shared stage really is one predicate, not a paraphrase.
* `approxCompact ⟹ manuscriptApproximation` ✓ (threshold discarded).
* `#print axioms` on `BochnerApproxAPI`, `bochnerApproxStatement`, `manuscriptApproximation`,
  `SeparatedTemporalDense`, `bochnerSpace` → `[propext, Classical.choice, Quot.sound]` ✓.

## Interface note for B02

`SeparatedTemporalDense` **is** the right shared stage: it mentions no realization, and
`Data.lean:205/212` give one `bochnerDatumENorm`/`MemBochnerDatum` on the one carrier
`RealVectorSobolev s`, matching `04:251` ("any of the preceding separable Hilbert spaces").
The defeq check above makes "B02 imports the predicate" literal. One refinement: of
`separatedAssembly`'s three conjuncts B02 reuses `MemForceCompact` and
`AEStronglyMeasurable` verbatim and must swap only `IsSobolevPath → IsHomogeneousPath`;
splitting the path clause out would let B02 reuse two-thirds of the field as-is.

## Check log

1. `. scripts/lean-env.sh; LEAN_NUM_THREADS=6; cd verification && lake env lean ../research/B01/Spec.lean` → **exit 0, no output**, 3.5 s wall.
2. Hygiene: `grep -nE 'sorry|axiom|admit|native_decide|unsafe' Spec.lean` → one hit, in prose ("introduces no `axiom`, no `sorry`"). No `theorem`/`lemma`/`example`/`instance`/`opaque` declaration in the file (only 4 `def`s, 1 `abbrev`, 1 `structure`). 374 lines.
3. Paper reading: `04-whole-space.tex` 8, 177, 183-196, 218-266; `02-preliminaries.tex` 55-74.
4. Ledger: `STATEMENTS.md` (version 2, 2026-09-13) 805-838, 849-885.
5. `Data.lean` 140-260, 536-570, 690-755.
6. Sources: `AngularRealVectorBochner.lean`, `SobolevDensity.lean`, `SeparatedBochnerDensity.lean`, `PositiveTemporalDensity.lean`, `CompactSobolevTime.lean`, `CompactForceAdmissibility.lean`, `CompactAdmissibleForce.lean`, `AdmissibleForce.lean`, `ComparisonCutoffs.lean`.
7. Scratch: two `/tmp` files via `lake env lean`, both exit 0 (one cosmetic unused-binder warning from my own file), then deleted.

**Not verified.** That `SD:43/51/59`, `PTD:73`, `SBD:30`, `CST:18` *prove* their statements
(read as statements only); the paper's mathematics; any B02 draft (none exists);
`verification` was not rebuilt (the needed oleans were current).
