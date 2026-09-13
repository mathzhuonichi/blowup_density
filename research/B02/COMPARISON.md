# B02 — Homogeneous `Ḣ^{-1}` approximation: source-to-target comparison

Draft specification: [`research/B02/Spec.lean`](Spec.lean), namespace
`BlowupDensity.B02.Draft`, structure `HomogeneousApproxAPI` (20 fields, 653
lines, typechecks clean, no `sorry`, no `axiom`, no placeholder `Prop` field),
plus the definitions `frequencyAnnulus`, `closedFrequencyAnnulus`,
`IsAnnularDatum`, `IsAnnularRestriction`, `IsAnnularSupported`, `scaledCutoff`,
`schwartzVector`, `separatedField`, `separatedPath`, `lowHighConstant`,
`SplitRange`, and the derived statements `manuscriptHomogeneousApproximation`,
`SeparatedTemporalDense`, `SeparatedCompactHomogeneousDense`,
`rnegativeCutoffConstant`, `homogeneousApproxStatement`.

Target statement: the **`L²(0,∞;Ḣ^{-1}(R³))` clause** of Proposition 4.6
(`prop:Renergy`), `paper/sections/04-whole-space.tex:218-229`, whose proof is the
paragraph `:241-249` followed by the shared Bochner paragraph `:251-260`; the
ledger's `B02` export, `research/section4/STATEMENTS.md:831-836`; the realization
`⟪D01:dotHminus1⟫` (`STATEMENTS.md:803-805`) and the split
`⟪D01:lowHighSplit⟫` (`STATEMENTS.md:806-807`).

Out of scope, by the task card and by `research/B01/COMPARISON.md` §3: the
inhomogeneous `H^s` stages (`04-whole-space.tex:231-239`, node `B01`), the
singular-force half (`:262`, node `R41D`/`R45`), the four simultaneous
convergences (`:221-227`, part (B) of `R46`), and the `s = -1` insertion
estimates (`:264-271`, node `I03`).

Line numbers were read in this worktree and are current as of commit `4ba9f2b`.
Note that `04-whole-space.tex:241` is a single long source line carrying the
whole annular construction and the announcement of the split; the `align` block
is `:242-248` with the label `eq:Rnegative-cutoff` at `:247`; `:249` carries the
finiteness remark, the cutoff step, the diagonal choice and the real-parts
remark.

Short names:

* `DATA = verification/Contracts/V1/Data.lean`
* `HR   = formalization/NSFormalization/Paper3/HomogeneousRealization.lean`
* `HT   = formalization/NSFormalization/Paper3/HomogeneousTime.lean`
* `SW   = formalization/NSFormalization/Paper3/SobolevWeights.lean`
* `CF   = formalization/NSFormalization/Paper3/CompactFourier.lean`
* `AFD  = formalization/NSFormalization/Paper3/AngularFourierDilation.lean`
* `ASC  = formalization/NSFormalization/Paper3/AngularSobolevClass.lean`
* `ARVB = formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean`
* `SBD  = formalization/NSFormalization/Paper3/SeparatedBochnerDensity.lean`
* `PTD  = formalization/NSFormalization/Paper3/PositiveTemporalDensity.lean`
* `TNS  = formalization/NSFormalization/Source/TimeNormScaling.lean`
* `FC   = formalization/NSFormalization/Source/FourierConvention.lean`
* `RS   = formalization/NSFormalization/Source/RealSobolev.lean`
* `RFC  = formalization/NSFormalization/Source/RieszFrequencyCutoffs.lean`
* `FR   = formalization/NSFormalization/Source/FractionalRealization.lean`
* `CS   = vendor/NavierStokesAndEuler/NavierStokes/R3/CompactSchwartz.lean`
* `CC   = vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean`
* `SCA  = vendor/NavierStokesAndEuler/NavierStokes/R3/SchwartzCompactApproximation.lean`
* `MSA  = Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
* `MSF  = Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`
* `MHS  = Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`

## 0. The headline answer

`formalization/blueprint/EXTERNAL_REUSE.md:38` says of the "Completed force
density" row that the real angular positive-time Bochner approximation "is
already present" and asks to "finish the homogeneous H-minus-one variant".  The
honest measurement of "finish" is:

* **The estimate half is largely present**, one convention over.  `HT:14`
  `homogeneous_energy_le_bound_add_L2` is eq:Rnegative-cutoff's scalar core with
  the manuscript's own `|ξ|<1` / `|ξ|≥1` split; `SW:54`
  `homogeneous_low_frequency_integrable` is "the integral at the origin is
  finite in dimension three"; `HR:17` `compact_homogeneous_norm_bound` is the
  scalar compact-input consequence.  All three are stated in Mathlib's **cycles**
  convention on `Source.homogeneousFourierNorm` (`TNS:68`), are scalar, and
  return `ℝ` through `Real.sqrt`.
* **The realization half is absent.**  `DATA`'s homogeneous objects —
  `IsHomogeneousDatum` (`:324`), `IsSliceDistribution` (`:298`),
  `IsHomogeneousVectorDatum` (`:358`), `IsHomogeneousSliceDatum` (`:367`),
  `IsHomogeneousPath` (`:375`), `forceHomogeneousENorm` (`:390`),
  `homogeneousENorm` (`:338`), `MemHomogeneous` (`:332`), `MemDotHNegOne`
  (`:343`), `homogeneousVectorENorm` (`:352`), `homogeneousFourierENorm`
  (`:410`), `CompletedDenseHomogeneous` (`:752`) — have **zero** users anywhere
  in `verification/` or `formalization/` outside `Data.lean` itself (checked,
  §5 command 4).  No theorem in the tree exhibits a single `IsHomogeneousDatum`.
  Since `forceHomogeneousENorm` and `homogeneousENorm` are infima and `⨅ ∅ = ⊤`,
  every statement phrased with them is *unprovable* until the first witness
  exists.
* **The annular stage is absent outright.**  Nothing in the tree approximates an
  `L²` function by smooth functions supported away from the origin; the closest
  objects (`RFC:14,15` `low`/`high`) split the *symbol* `|ξ|^{-a}`, not the
  integral, and serve the Riesz potential, not this argument.
* **The Bochner stage is present and carrier-generic**, shared verbatim with
  `B01`: `SBD:30` `dense_span_separatedLp` and `PTD:73`
  `dense_positive_temporal_factors` mention no realization at all.

So: of the six stages of the manuscript's homogeneous paragraph, stage 3 is
present at the scalar cycles level, stage 6 is present and shared, and stages
1, 2, 4, 5 plus the realization bridge are new.

## 1. Field-by-field comparison

| Spec field | Paper location | Existing declaration (name, file:line, hypotheses, convention, realization) or gap | Mismatch |
|---|---|---|---|
| `χ`, `chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range` | `04:235`, reused at `:249` | **Present, verbatim.** `CC:29` `baseCutoff` with `CC:40` `baseCutoff_smooth`, `CC:46` `baseCutoff_eq_one (‖x‖ ≤ 1)`, `CC:50` `baseCutoff_eq_zero (2 ≤ ‖x‖)`, `CC:42,44` `baseCutoff_nonneg`/`_le_one`.  Real scalar on `Space`; no convention issue. | None.  `scaledCutoff baseCutoff R = CC:32 cutoff R` by `rfl` (checked by `B01`, re-checked here). |
| `annularRestriction` | `04:241` "One first restricts to `1/n<|ξ|<n`, with `L²` error tending to zero" | **Gap.**  Nothing in the tree restricts an `L²` datum to an annulus.  Mathlib supplies the ingredients: `eLpNorm` of an indicator, `EuclideanSpace.volume_ball` (`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:311`), dominated convergence. | The conclusion must land in `RealSobolevHilbert s`, i.e. must respect `RS:24` `realSymmetry`.  The annulus `δ<‖ξ‖<R` is symmetric under `ξ ↦ −ξ` and its indicator is real, so the truncation commutes with `RS:27` `realSymmetry_ae`; that lemma is present, the composite is not.  No convention issue: the datum space is convention-free `L²`. |
| `annularSmoothing` | `04:241` "smooths each restricted function with a sufficiently small mollification radius and a slightly larger annular cutoff" | **Partial.**  `MSA:97` `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` (and `MSA:82` `MemLp.exist_eLpNorm_sub_le`) give smooth compactly supported approximation in every `L^p`, `p ≠ ⊤`, on a finite-dimensional real normed space.  Nothing gives support **away from the origin**. | Two steps on top of Mathlib: (a) re-cut by `1 − χ(ξ/δ')` to clear a neighbourhood of `0`, the error being `‖·‖_∞ · volume(ball 0 2δ')^{1/2}`; (b) the same `realSymmetry` step as above.  Mathlib's approximant is complex/vector-valued but not symmetric, so (b) is not optional. |
| `annularPathApprox` | `04:241` read in the norm of `:226` (`L²_tḢ^{-1}`) | **Gap.**  Carrier-generic dominated convergence in `L^q(μ;X)`; Mathlib has `eLpNorm` monotone/dominated machinery but no packaged statement. | Not a manuscript step: `04:251` performs the Bochner reduction *first*.  Recorded because the task card names it and because it is the only field in which the truncation is visible in the manuscript's displayed norm.  A single `(δ,R)` does suffice for a whole path (the truncation is a fibrewise contraction), but no *smoothness* of the truncated datum is uniform in `t`, so the conclusion is an `IsAnnularRestriction`, not an `IsAnnularDatum`, and `approxCompactHomogeneous` does not route through it. |
| `annularSchwartz` | `04:241` "Set `ĥ_n = |ξ|G_n`.  Again `h_n` is Schwartz" | **Partial, scaffolding only.**  `CS:37` `NavierStokesR3.CompactSchwartz.ofCompactSupport` turns a smooth compactly supported function into a `SchwartzMap`; `MSF:51` `SchwartzMap.fourierTransformCLM` inverts; `AFD:172,176` `angularFourierDistribution`, `angularRealization` and `AFD:218` `angularFourierDistribution_schwartz_apply` connect a Schwartz field to its distributional angular transform. | **The composite is the gap.**  `|ξ|^{-s}G_n` is smooth only because `tsupport G_n` avoids `0`; no lemma in the tree multiplies by `‖ξ‖^{-s}` and keeps smoothness.  Then the conclusion is `DATA:367` `IsHomogeneousSliceDatum`, which no existing theorem produces.  Reality (`RS:60` `fourier_conjugate`, `RS:118` `realSubspace`) is what makes `h_n` a *real* field, i.e. discharges `04:249`'s "take real parts" — present as lemmas, not as this composite. |
| `lowFrequencyIntegrable` | `04:249` "The integral at the origin is finite in dimension three" | **Present.** `SW:54` `homogeneous_low_frequency_integrable`, hypotheses `-3/2 < s`, `φ` measurable, `0 ≤ C`, `∀ξ ‖φ ξ‖ ≤ C`; conclusion `IntegrableOn (fun ξ => ‖ξ‖^(2s)·‖φ ξ‖²) (ball 0 1)`.  The bare weight is the instance `φ ≡ 1`, `C = 1`, which is exactly how `HT:22` uses it. | None beyond that instantiation. |
| `lowFrequencyIntegral` (`∫_{\|ξ\|<1}\|ξ\|^{-2} = 4π`) | `04:246` (the displayed factor), `:249` | **Gap** (elementary).  `MHS:296` `MeasureTheory.integral_fun_norm_addHaar`: `∫ f(‖x‖) = dim E • μ.real (ball 0 1) • ∫_{Ioi 0} y^{dim E − 1} • f y`; with `EuclideanSpace.volume_ball` this is `3 · (4π/3) · ∫_0^1 y² y^{-2} dy = 4π`. | None mathematically.  Stated because it is what turns the manuscript's unnamed `C'` into an explicit number; see `lowHighConstant` below. |
| `fourierSupBound` (`(Σ_i\|ẑ_i(ξ)\|²)^{1/2} ≤ (2π)^{-3/2}∫‖z‖`) | `04:246`, the manuscript's unnamed `C` | **Partial.** `MSF:279` `SchwartzMap.norm_fourier_apply_le_toLp_one` is the cycles-convention scalar bound `‖𝓕f ξ‖ ≤ ‖f‖_{L¹}` (used at `HT:56`).  `FC:15,23` fix `frequencyUnit = 2π` and `angularFourier f ξ = (2π)^{-3/2} • 𝓕 f ((2π)⁻¹ • ξ)`. | Two: (a) the `(2π)^{-3/2}` amplitude, immediate from `FC:23`; (b) **vector, not componentwise** — `01-intro:103` sums squared components, so the bound must come from the triangle inequality for the vector-valued integral.  A componentwise transport would cost a factor `3` and the constant of `lowHighSplit` would stop being the manuscript's.  Hypothesis is `MemLp k 1 volume`, the manuscript's `k ∈ L¹`. |
| `lowHighSplit` (eq:Rnegative-cutoff) | `04:241-248`, label at `:247` | **Present at the scalar cycles level.** `HT:14` `homogeneous_energy_le_bound_add_L2`: hypotheses `-3/2 < s`, `s ≤ 0`, `φ` measurable, `‖φ‖ ≤ C`, `Integrable ‖φ‖²`; conclusion `∫ ‖ξ‖^{2s}‖φ ξ‖² ≤ C²·∫_{ball 0 1}‖ξ‖^{2s} + ∫‖φ‖²`.  Consequence for compact inputs: `HT:47` `homogeneousFourierNorm_le_physical`, re-exported as `HR:17` `compact_homogeneous_norm_bound`. | Four.  (a) **Scalar → real vector**, `PiLp 2` sum over `Fin 3`.  (b) **Cycles → angular is a restatement, not a transport**: the angular and cycles frequency variables differ by the dilation `ξ = 2πη` (`FC:23`), so the ball of radius `1` in the manuscript's variable is the ball of radius `1/(2π)` in Mathlib's; the source inequality splits at cycles-radius `1`, the manuscript at angular-radius `1`, and the two constants are *not* related by the `(2π)^s` factor of `RECONCILIATION.md` unit L8 alone.  (c) `ℝ`/`Real.sqrt` → `ℝ≥0∞`, since `DATA:410` `homogeneousFourierENorm` is `ℝ≥0∞`-valued.  (d) **Hypothesis class**: `HR:17` assumes `ContDiff ∞` + `HasCompactSupport`; the manuscript assumes `k ∈ L¹ ∩ L²` and *needs* the wider class, because the field it is applied to at `04:249` is `(1−χ_R)h_n`, Schwartz with unbounded support.  A compact-support-only version does not close the diagonal argument. |
| `lebesgueHomogeneousDatum` (existence + norm of the `Ḣ^s` datum of an `L¹∩L²` field) | `02-prelim:58-69` eq:homogeneous-realization applied inside `04:241-249` | **Gap — the central one.**  The only `L² → 𝓢'` homogeneous realization in the tree is `FR:44` `realization` with `FR:78` `realization_toDistribution` and `FR:96` `realization_norm_le_datum`, restricted to `0 < a < 3/2`, in the **cycles** convention, landing in `L^{p_a}` (the Appendix-B completion of `app-B:44,56-70`, i.e. `A05`'s object).  For `s = -1` — negative order, angular convention, `DATA:324` `IsHomogeneousDatum` — there is nothing.  `HR` says so in its own header: "A full `L² → 𝓢'` homogeneous multiplier is intentionally not introduced here." | This is `research/I03/COMPARISON.md`'s unit **U7c** at the spatial level, and `RECONCILIATION.md` unit **L7**'s negative half.  Available pieces: `ASC:22` `angularFourierDistribution_injective` (uniqueness, if wanted), `SW:68` `homogeneous_negative_integrable` (finiteness of the weighted square on `-3/2 < s ≤ 0`), `CF:17,28` its Schwartz/compact-Fourier instances, `MSF:306` `SchwartzMap.integral_norm_sq_fourier` (Plancherel).  The field is stated with **two** clauses — existence, and "every datum has norm `homogeneousFourierENorm s k`" — precisely so that the diagonal argument needs no injectivity lemma. |
| `homogeneousDatumSub` | `04:249` "`χ_Rh_n → h_n` in `Ḣ^{-1}`" | **Gap** (formal).  Linearity of `DATA:367` `IsHomogeneousSliceDatum` in the field; follows from linearity of `AFD:172` `angularFourierDistribution` and additivity of the Bochner pairing. | None mathematically.  Present as a field because without it the estimate on `(1−χ_R)h_n` does not reach `‖H − W‖ₑ`. |
| `cutoffLebesgue` (`‖(1−χ_R)h_n‖₁, ‖(1−χ_R)h_n‖₂ → 0`) | `04:249` | **Essentially present.** `SCA:169` `seminorm_truncate_sub_le`: every Schwartz seminorm of `truncate ψ R − ψ` is `≤ errorTailBound ψ k m / R`, real `R ≥ 1`; `SCA:25` `truncate ψ R = cutoff R · ψ` with `CC:32` `cutoff`.  Mathlib's `SchwartzMap.toLpCLM` (`Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1368`) is continuous `𝓢 → L^p` for `Fact (1 ≤ p)`. | Bookkeeping: (a) scalar complex → three real components via `schwartzVector`; (b) `ℕ`-sequence (`SCA:177` `approximate`) versus `Filter.atTop` on `ℝ` — `SCA:169` is already real-`R`; (c) `p = 1` and `p = 2` instances of `toLpCLM`.  **No convention issue**: these are physical-space Lebesgue norms, not Fourier norms.  Note this is `B01`'s `cutoffApprox` replaced, not reused: `B01` estimates `H^m` seminorms, which for `s < 0` bound the wrong side (`(1+|ξ|²)^s ≤ |ξ|^{2s}`). |
| `spatialApproxHomogeneous` | `04:249` "A diagonal choice gives compact-smooth density in this realization" | **Gap.** The combination of the six fields above.  The inhomogeneous analogue `SobolevDensity.lean:59` `dense_compact_weightedFourierLp` exists; there is no homogeneous counterpart. | The conclusion is `IsHomogeneousSliceDatum s h H` with `h` physical, smooth, compactly supported — i.e. it *consumes* `lebesgueHomogeneousDatum`.  The parenthesis "without a dual Sobolev-embedding assumption" is honoured: no hypothesis relating `Ḣ^s` to any `H^{s'}` occurs anywhere in `HomogeneousApproxAPI`. |
| `temporalApprox` | `04:251-260` | **Partial, and identical to `B01`'s.** `SBD:30` `dense_span_separatedLp` (dense coefficients × dense scalar time factors ⟹ dense separated span, any real normed `H`, any measure) and `PTD:73` `dense_positive_temporal_factors` (`C_c^∞` factors with `tsupport ⊆ Ioi 0` dense in `Lp ℝ q positiveTimeMeasure`).  Carrier-generic, hence **no convention and no realization issue**. | Exactly `B01`'s unit 7: unwrap `Submodule.span` into a finite `ℝ`-combination and move from the `Lp` quotient to representatives.  `B02` must not re-prove it. |
| `separatedAssembly` | `04:260` | **Partial.** `PhysicalBochnerDensity.lean:55` `separated_physical_hasCompactSupport` (single product) and `PositivePhysicalDensity.lean:37` `separatedLp_mem_positivePhysicalBochner` (the `tsupport ⊆ Ioi 0` pattern) are `B01`'s inputs and apply unchanged to the two conjuncts `MemForceCompact` and `AEStronglyMeasurable`. | One conjunct differs from `B01`'s: `IsHomogeneousPath s` in place of `IsSobolevPath s`, and the per-profile hypothesis is `IsHomogeneousSliceDatum`.  That conjunct needs additivity of the homogeneous datum over a finite sum, i.e. the finite-sum form of `homogeneousDatumSub`. |
| `approxCompactHomogeneous` | `04:219` second clause, `:226` | **Gap.**  `ARVB:120` `exists_angular_real_vector_positive_physical_approx` is the *inhomogeneous* twin and is **not** reusable: its conclusion is about `ARVB:47` `angularRealVectorSlice`, the `H^s` datum path, and `ARVB:54` `angularRealVectorSlice_pairing` is `DATA:160` `IsSobolevDatum` verbatim — a different realization predicate. | The structure of the assembly transfers (`temporalApprox` + `spatialApproxHomogeneous` + `separatedAssembly`), the theorem does not.  Stated at every `q ∈ [1,∞)` and every `s` in `SplitRange`; `manuscriptHomogeneousApproximation` is the `q = 2`, `s = -1` instance `R46` consumes. |

### The constants of eq:Rnegative-cutoff, written out

`Spec.lean`'s `lowHighConstant s = (2π)^{-3} · ∫_{|ξ|<1}|ξ|^{2s}dξ` is the
manuscript's `C'`, and the two factors are the two fields `fourierSupBound`
(giving `C = ((2π)^{-3/2})² = (2π)^{-3}`) and `lowFrequencyIntegral` (giving
`4π` at `s = -1`).  Hence `C' = (2π)^{-3}·4π = 1/(2π²) ≈ 0.05066`, recorded as
`rnegativeCutoffConstant`.  The manuscript leaves both unnamed
(`04:246-247`); nothing here is stronger than the display, only more explicit.

### Which `s` the argument covers

The manuscript states only `Ḣ^{-1}`.  Its argument runs on exactly
`-3/2 < s ≤ 0`, which `Spec.lean` names `SplitRange`:

* `-3/2 < s` is the convergence of `∫_{|ξ|<1}|ξ|^{2s}dξ` — the manuscript's "the
  integral at the origin is finite in dimension three" (`04:249`) — and also the
  temperedness range of the realization (`02-prelim:66-69`).  It is the
  hypothesis `hs` of `SW:54`.
* `s ≤ 0` is the high-frequency half, `|ξ|^{2s} ≤ 1` on `|ξ| ≥ 1`
  (`04:246-247`).  It is the hypothesis `hs0` of `HT:14`.

Stages 1, 2 and 6 (annular approximation, Schwartz realization, Bochner) need
neither and hold for every real `s`; only the split does.  For `0 ≤ s < 3/2` the
conclusion is still true by a *different* route — `|ξ|^{2s} ≤ (1+|ξ|²)^s`, so
`‖z‖_{Ḣ^s} ≤ ‖z‖_{H^s}` and `B01`'s `cutoffApprox` applies unchanged — which
this contract deliberately does not state.  For `s ≤ -3/2` the realization
itself fails (`02-prelim:70`).  So: `B01` covers every real `s` by the Leibniz
cutoff, `B02` covers `-3/2 < s ≤ 0` by eq:Rnegative-cutoff, the methods overlap
nowhere, and `s = -1` is interior to `B02`'s range.

## 2. How much homogeneous-realization machinery is missing

The task asks for this measured against the 26-line
`Paper3/HomogeneousRealization.lean` and the 143-line inhomogeneous analogue
`Paper3/AngularRealVectorBochner.lean`.  Both counts are exact (checked, §5
command 5).

`HR` (26 lines) contains **one** theorem, `compact_homogeneous_norm_bound`
(`:17`), whose proof is a single `exact` of `HT:47`
`homogeneousFourierNorm_le_physical`.  It is a *norm estimate on a scalar
cycles-convention Fourier integral*.  Its own header states the boundary: "This
is a norm estimate, not the completed tempered-distribution realization from the
manuscript", and "A full `L² → 𝓢'` homogeneous multiplier is intentionally not
introduced here."

`ARVB` (143 lines) contains the whole inhomogeneous stack that `DATA`'s Sobolev
side rests on:

| `ARVB` | role | homogeneous counterpart |
|---|---|---|
| `:15` `cyclesToAngularRealVector` (a `≃L[ℝ]` on `RealVectorSobolev s`) | convention transport on the datum carrier | **none needed** — the homogeneous datum carrier is the same `RealVectorSobolev s`, but nothing transports the *weight* `|ξ|^{-s}` |
| `:24` `cyclesToAngularRealVector_norm_le` | its bound `frequencyUnit ^ \|s\|` | **absent** |
| `:40` `angularRealization_cyclesToAngularRealVector` | component preservation | **absent** |
| `:47` `angularRealVectorSlice` | the `H^s` datum **path** of a compact smooth force | **absent** — no `Ḣ^s` datum path exists |
| `:54` `angularRealVectorSlice_pairing` | is `DATA:160` `IsSobolevDatum` verbatim | **absent** — no theorem anywhere produces `DATA:367` `IsHomogeneousSliceDatum` |
| `:64` `memLp_angularRealVectorSlice` | `MemLp` at every `q` | **absent** (the closest, `HT:108` `memLp_homogeneousFourier_time`, is `MemLp` of a *scalar real-valued Fourier norm*, not of a datum path) |
| `:73,:78` Bochner transports | `Lp`-level convention maps | **absent** |
| `:120` `exists_angular_real_vector_positive_physical_approx` | the `B01` density theorem | **absent** |

So the ratio is worse than 26 : 143 suggests, because the 26 lines and the 143
lines are not doing the same kind of work: `ARVB` builds a *realization* (a map
into `𝓢'` and the pairing identity that identifies it with the manuscript's),
while `HR` only bounds a number.  Counting by what `DATA` needs:

* **Datum witnesses:** inhomogeneous `1` (`ARVB:54`), homogeneous `0`.
* **Users of the `DATA` predicate outside `Data.lean`:** inhomogeneous
  `IsSobolevDatum` — several; homogeneous `IsHomogeneousDatum`,
  `IsHomogeneousSliceDatum`, `IsHomogeneousPath`, `forceHomogeneousENorm`,
  `homogeneousENorm`, `homogeneousFourierENorm`, `CompletedDenseHomogeneous`,
  `IsSliceDistribution` — **`0` each** (checked).
* **`L² → 𝓢'` homogeneous realizations:** exactly one, `FR:44`, for
  `0 < a < 3/2`, cycles convention, landing in `L^{p_a}`.  Nothing at negative
  order, nothing in the angular convention.

Consequently unit 6 below (`lebesgueHomogeneousDatum`) is **not a lift of an
existing lemma**; it is the first inhabitant of `DATA`'s homogeneous half, and
`research/I03/COMPARISON.md:284` reaches the same conclusion from the insertion
side ("Proposition 4.6's `L²(0,∞;Ḣ^{-1})` clause (R46) blocks on U7c
specifically").  `B02` and `I03` therefore share one blocker: `B02` needs the
*spatial* datum witness for `L¹∩L²` fields, `I03` needs the *scaled-family*
witness; unit 6 below is the common core and should be built once.

## 3. Shared-stage interface with B01

`research/B01/COMPARISON.md` §3 fixes this interface; `Spec.lean` follows it
exactly.

* **Shared, unchanged, must be one declaration after promotion.**
  `SeparatedTemporalDense q s` and the field `temporalApprox`; the helper
  definitions `separatedField`, `separatedPath`, `schwartzVector`,
  `scaledCutoff`.  All six are byte-identical between `research/B01/Spec.lean`
  and `research/B02/Spec.lean` (checked, §5 command 3).  They are duplicated
  only because `research/` is not on the Lake module path — `verification` is
  the package root and `import Contracts.V1.Data` is the only import either
  draft can make.  **At promotion time exactly one copy must survive**, next to
  `Data.lean` and in neither lane; this satisfies
  `STATEMENTS.md:903-904` ("formalise it once (B01/B02 share it)").
* **Shared with one substitution.** `separatedAssembly`: `IsHomogeneousPath s`
  replaces `IsSobolevPath s`, and `IsHomogeneousSliceDatum` replaces
  `IsSobolevDatum` in the per-profile hypothesis.  `MemForceCompact` and
  `AEStronglyMeasurable` are word-for-word `B01`'s and are proved once.
* **Not shared, and must not be reused.** `B01`'s `schwartzApprox`,
  `cutoffApprox`, `spatialApprox`.  `B01`'s stage 2 is a Leibniz `H^m` estimate;
  for `s < 0` the comparison `(1+|ξ|²)^s ≤ |ξ|^{2s}` points the wrong way, which
  is exactly why the manuscript writes a different paragraph.
* **Consumed from `B01`, not re-proved.** `compactSubsetForceR`
  (`forceClassCompact ⊆ forceClassR`) and the four `completion*` fields
  identifying the datum-path completion with
  `Lp (RealVectorSobolev s) q forceTimeMeasure`.  All five are
  realization-independent — they mention neither `IsSobolevPath` nor
  `IsHomogeneousPath` — so `B02` states none of them.
* **Conclusion shapes sit side by side.**  `B01` ends at
  `CompletedDense q s forceClassCompact` (`DATA:743`), `B02` at
  `CompletedDenseHomogeneous q s forceClassCompact` (`DATA:752`), and
  `CompletedDenseHomogeneous q s S = CompletedDenseVia q s (IsHomogeneousPath s) S`
  by `rfl` (checked).  `R46` consumes both.

## 4. Bounded implementation split

Nine lemma-sized units.  Units 1-3 and 6 are the new mathematics; 4, 5, 7 are
transports of existing statements; 8-9 are assembly.  No unit re-proves anything
already in the tree, and unit 5 is explicitly `B01`'s unit 7 — `B02` consumes it.

| # | Unit | Size | Statement to prove | Builds on |
|---|---|---|---|---|
| 1 | `annular_truncation` | **M** | `annularRestriction` and `annularSmoothing`: every datum is approximated in `L²` by one supported in a compact annulus away from `0`, then by a smooth such one. | `MSA:97` `Lp.dense_hasCompactSupport_contDiff` / `MSA:82` `MemLp.exist_eLpNorm_sub_le`; `EuclideanSpace.volume_ball` for the origin-removal tail; `RS:24,27` `realSymmetry`/`realSymmetry_ae` plus `RS:123` `mem_realSubspace_iff` for membership in the conjugate-reflection subspace (the annulus is `ξ ↦ −ξ` invariant and its cutoff real, so the truncation commutes with `realSymmetry`). |
| 2 | `annular_schwartz_realization` | **L** | `annularSchwartz`: from `IsAnnularDatum δ R W` with `0 < δ`, produce `ψ : Fin 3 → SchwartzMap Space ℝ` with `IsHomogeneousSliceDatum s (schwartzVector ψ) W`. | `‖ξ‖^{-s}` is `ContDiff` on `{ξ ≠ 0}`, so `|ξ|^{-s}G_n` is smooth with compact support; `CS:37` `CompactSchwartz.ofCompactSupport`; `MSF:51` `fourierTransformCLM` to invert; `AFD:172,176,218` to identify `angularFourierDistribution` of the result with the datum; `RS:60` `fourier_conjugate` + `RS:118` `realSubspace` for real-valuedness (`04:249`).  **`L` because it is the first construction of an `IsHomogeneousDatum` from a concrete field.** |
| 3 | `low_frequency_weight` | **S** | `lowFrequencyIntegrable` and `lowFrequencyIntegral` (`= 4π` at `s = -1`). | `SW:54` at `φ ≡ 1`, `C = 1` (the instantiation pattern is `HT:22`); `MHS:296` `integral_fun_norm_addHaar` with `EuclideanSpace.volume_ball` for the exact value. |
| 4 | `angular_fourier_sup_bound` | **S** | `fourierSupBound`, in the vector form. | `FC:23` `angularFourier` (the `(2π)^{-3/2}` amplitude and the `(2π)⁻¹` dilation); `MSF:279` `norm_fourier_apply_le_toLp_one` for the cycles scalar bound, or directly `norm_integral_le_integral_norm` for the vector one. |
| 5 | `separated_temporal_dense` | **L** | `temporalApprox` / `SeparatedTemporalDense`.  **`B01`'s unit 7; `B02` consumes the result.** | `SBD:30` `dense_span_separatedLp` at `H := RealVectorSobolev s`, `μ := positiveTimeMeasure`; `PTD:73` `dense_positive_temporal_factors`; template `SBD:69` `dense_span_physical_separated_sobolev`. |
| 6 | `homogeneous_datum_of_lebesgue` | **L** | `lebesgueHomogeneousDatum` (existence **and** the norm clause) and `homogeneousDatumSub`, on `-3/2 < s ≤ 0` for `k ∈ L¹ ∩ L²`. | Build `G_i := ‖ξ‖^{s}·angularFourier k_i` as an `L²` element, finiteness from `SW:68` `homogeneous_negative_integrable` (with `CF:17,28` for the Schwartz/compact instances); membership in `RS:118` `realSubspace` from `RS:60` `fourier_conjugate` (the weight is real and even — this *is* `04:249`'s parenthesis); the pairing identity from `AFD:172,218`; the norm clause from `MSF:306` `integral_norm_sq_fourier` (Plancherel) summed over `Fin 3`.  `ASC:22` `angularFourierDistribution_injective` is available but **not required**, because the field pins the norm of *every* datum rather than the datum itself.  **This is unit `U7c`'s spatial core (`research/I03/COMPARISON.md:284`) and the first inhabitant of `DATA`'s homogeneous half.** |
| 7 | `low_high_split` | **M** | `lowHighSplit`, on `SplitRange`, for `k ∈ L¹ ∩ L²`, in `ℝ≥0∞` and in the angular convention. | `HT:14` `homogeneous_energy_le_bound_add_L2` is the scalar core but splits at *cycles* radius `1`; restate it at angular radius `1` by re-running its two-line majorant argument (`SW:54` for the low half, `Real.rpow_le_one_of_one_le_of_nonpos` for the high half) against `FC:23`; then sum over `Fin 3`, feed unit 4 for `C`, and move `Real.sqrt`/`ℝ` to `ℝ≥0∞`.  Widening `HR:17`'s compact-support hypothesis to `L¹ ∩ L²` costs nothing: `HT:14` never uses compactness, only `‖φ‖_∞ ≤ C` and `Integrable ‖φ‖²`. |
| 8 | `cutoff_lebesgue` + `spatial_dense` | **M** | `cutoffLebesgue` and `spatialApproxHomogeneous` (the diagonal). | `SCA:169` `seminorm_truncate_sub_le` + `SchwartzMap.toLpCLM` at `p = 1, 2`; `scaledCutoff baseCutoff R = CC:32 cutoff R` by `rfl`; then units 1, 2, 6, 7: `h_n` from units 1-2, `χ_Rh_n` compact smooth, its datum from unit 6, and `‖H − W‖ₑ = homogeneousFourierENorm s ((1−χ_R)h_n)` from `homogeneousDatumSub` + unit 6's norm clause, bounded by unit 7. |
| 9 | `HomogeneousApproxAPI` term + registration | **M** | `χ := CC:29 baseCutoff` (five fields from `CC:40,46,50,42,44`); `separatedAssembly` by `B01`'s unit 6 with the `IsHomogeneousPath` conjunct from the finite-sum form of `homogeneousDatumSub`; `annularPathApprox` by fibrewise dominated convergence from unit 1's truncation; `approxCompactHomogeneous` from units 5, 8 and `separatedAssembly`; derive `SeparatedCompactHomogeneousDense`; promote to `verification/Contracts/V1/HomogeneousApprox.lean` with a typed `Bindings` entry and the `#print axioms` test. | Packaging pattern of `verification/Contracts/V1/Thresholds.lean` and `verification/contracts.json`. |

Critical path: **6 → 7 → 8 → 9**, with 1 and 2 feeding 8 and 3, 4 feeding 7.
Unit 6 is the single blocker and is shared with `I03`'s `U7c`; it should be
built once, in a new `Paper3` module, and consumed by both lanes.

Optional follow-ups, **not** part of `B02` (recorded so they are not lost):

* **A.** The `0 ≤ s < 3/2` route (`‖z‖_{Ḣ^s} ≤ ‖z‖_{H^s}` plus `B01`'s
  `cutoffApprox`), which would extend `approxCompactHomogeneous` past
  `SplitRange`.  No consumer needs it; `app-B:101` refuses `Ḣ^{3/2}` as a space.
* **B.** Uniqueness of the homogeneous datum (`RECONCILIATION.md` unit L7) from
  `ASC:22`.  Unit 6's norm clause makes it unnecessary here, but `R46` will want
  it as soon as it mixes `forceHomogeneousENorm` with an explicit path.
* **C.** The `L^q_t` lift of unit 6 — the datum path of a compact smooth
  spacetime force and its `forceHomogeneousENorm` — which is what `I03`'s `U7c`
  needs beyond the spatial core, using `HT:82,108`.

## 5. Commands run

All from the worktree, after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`
and no `-j`.

1. `bash scripts/lean-install.sh` — exit 0, `== OK` (last line
   `Contract BlowupDensity.Tests.checkedCorrection: checked; standard logical
   axioms only`).
2. `cd verification && lake build Contracts.V1.Data NSFormalization.Paper3.HomogeneousTime NSFormalization.Paper3.AngularRealVectorBochner`
   — `Build completed successfully (8828 jobs)`.  Pre-existing upstream
   `unusedVariables` warnings in `Paper3/RealPositiveDensity.lean` and
   `Paper3/RealVectorPositiveDensity.lean`; none in the contract.
3. `cd verification && lake env lean ../research/B02/Spec.lean` — exit 0, no
   output, 3.3-3.9 s user time across the successive drafts.
4. Scratch checks (`lake env lean` on temporary files, not committed):
   `#print axioms` on `HomogeneousApproxAPI`, `homogeneousApproxStatement`,
   `manuscriptHomogeneousApproximation`, `SeparatedTemporalDense`,
   `SeparatedCompactHomogeneousDense`, `IsAnnularDatum`, `IsAnnularSupported`,
   `lowHighConstant`, `rnegativeCutoffConstant` → all
   `[propext, Classical.choice, Quot.sound]`;
   `CompletedDenseHomogeneous q s S = CompletedDenseVia q s (IsHomogeneousPath s) S`
   by `rfl`; `bochnerDatumENorm q s G = eLpNorm G q forceTimeMeasure` by `rfl`;
   `forceTimeMeasure = volume.restrict (Ioi 0)` by `rfl`;
   `schwartzVector ψ x i = ψ i x` by `rfl`;
   `(Z i : FourierData)` and `((Z i : FourierData) : Space → ℂ)` elaborate for
   `Z : RealVectorSobolev s`.
5. Source measurements: `grep -rn` for each of the eleven homogeneous `DATA`
   names over `verification/` and `formalization/`, excluding
   `Contracts/V1/Data.lean` — **0 hits each**;
   `wc -l` → `HomogeneousRealization.lean` 26, `AngularRealVectorBochner.lean`
   143, `HomogeneousTime.lean` 116.
6. Shared-definition check: `diff` of the `SeparatedTemporalDense`,
   `separatedPath`, `separatedField`, `schwartzVector` and `scaledCutoff`
   blocks between `research/B01/Spec.lean` and `research/B02/Spec.lean` —
   identical in all five.
7. `make check` — see below.

**Failures and deviations.**

* No Lean failure remains.  Two statements were **corrected during drafting**
  after the source reading, and the corrections are load-bearing:
  1. `fourierSupBound` was first written componentwise
     (`‖ẑ_i(ξ)‖ ≤ (2π)^{-3/2}∫‖z‖`).  Summed over `Fin 3` that loses a factor
     `3` and `lowHighSplit`'s constant would no longer have been the
     manuscript's.  It is now the vector form.
  2. `lowHighSplit` and the realization bridge were first hypothesised on
     `ContDiff ∞` + `HasCompactSupport`, following `HR:17`.  The manuscript
     states eq:Rnegative-cutoff "for every `k ∈ L¹ ∩ L²`" and *needs* the wider
     class, because it applies it to `(1−χ_R)h_n`, which is Schwartz with
     unbounded support.  Both fields now carry `MemLp k 1 volume` and
     `MemLp k 2 volume`, and the bridge was renamed
     `compactHomogeneousDatum → lebesgueHomogeneousDatum`.  A companion field
     `homogeneousDatumSub` was added, without which the estimate on the
     difference does not reach the datum norm.
* `research/B01/COMPARISON.md` §3 asks `B02` to **import** `B01`'s
  `SeparatedTemporalDense` rather than restate it.  That is not possible:
  `research/` is not on the Lake module path, `verification` is the package
  root, and the only import either draft can make is `Contracts.V1.Data`.  The
  definition is therefore restated byte-for-byte and the duplication is flagged
  in both the module docstring and the `def`'s own docstring; one copy must be
  deleted at promotion.
