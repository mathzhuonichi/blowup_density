# B01 — Real positive-time Bochner approximation: source-to-target comparison

Draft specification: [`research/B01/Spec.lean`](Spec.lean), namespace
`BlowupDensity.B01.Draft`, structure `BochnerApproxAPI` (374 lines, typechecks
clean, no `sorry`, no `axiom`, no placeholder `Prop` field), plus the
definitions `scaledCutoff`, `separatedField`, `separatedPath`, `bochnerSpace`
and the derived statements `manuscriptApproximation`, `SeparatedTemporalDense`,
`bochnerApproxStatement`.

Target statement: the **approximation half** of Proposition 4.6
(`prop:Renergy`), `paper/sections/04-whole-space.tex:218-229`, whose proof is at
`:232-260`; the ledger's `B01` export,
`research/section4/STATEMENTS.md:826-830`; the completion object requested as
`⟪D01:BochnerLq q X⟫`, `research/section4/STATEMENTS.md:812-814`.

Out of scope, by the task card: the homogeneous `Ḣ^{-1}` variant
(`04-whole-space.tex:244-252`, node `B02`), the singular-force half
(`04-whole-space.tex:262-264`, node `R41D`/`R45`), and the four simultaneous
convergences (`04-whole-space.tex:221-227`, part (B) of `R46`).

Line numbers were read in this worktree and are current as of commit `4ba9f2b`.
Short names:

* `DATA = verification/Contracts/V1/Data.lean`
* `ARVB = formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean`
* `ARS  = formalization/NSFormalization/Paper3/AngularRealSobolev.lean`
* `RVPD = formalization/NSFormalization/Paper3/RealVectorPositiveDensity.lean`
* `RPD  = formalization/NSFormalization/Paper3/RealPositiveDensity.lean`
* `PPD  = formalization/NSFormalization/Paper3/PositivePhysicalDensity.lean`
* `PBD  = formalization/NSFormalization/Paper3/PhysicalBochnerDensity.lean`
* `SBD  = formalization/NSFormalization/Paper3/SeparatedBochnerDensity.lean`
* `SoBD = formalization/NSFormalization/Paper3/SobolevBochnerDensity.lean`
* `SD   = formalization/NSFormalization/Paper3/SobolevDensity.lean`
* `PTD  = formalization/NSFormalization/Paper3/PositiveTemporalDensity.lean`
* `CST  = formalization/NSFormalization/Paper3/CompactSobolevTime.lean`
* `CSR  = formalization/NSFormalization/Paper3/CompactSobolevRealization.lean`
* `SCT  = formalization/NSFormalization/Paper3/SpatiallyCompactTime.lean`
* `FHB  = formalization/NSFormalization/Source/FiniteHilbertBochner.lean`
* `SCA  = vendor/NavierStokesAndEuler/NavierStokes/R3/SchwartzCompactApproximation.lean`
* `CC   = vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean`

## 0. The headline answer

`EXTERNAL_REUSE.md:38` says the real angular positive-time approximation "is
already present".  That is **correct for the main field and for nothing else**.

`ARVB:120` `exists_angular_real_vector_positive_physical_approx` gives, for
**every real `s`** and **every `q ≠ ⊤` with `Fact (1 ≤ q)`**, and every
`b : Lp (RealVectorSobolev s) q positiveTimeMeasure`, a globally smooth
`F : ℝ × Space → Space` with `HasCompactSupport F` and
`tsupport F ⊆ {z | 0 < z.1}`, plus real scalar components `f i`, such that
`‖b − (memLp_angularRealVectorSlice s f hf hc q).toLp (angularRealVectorSlice s f hf hc)‖ < ε`.

Measured against `DATA`:

* **class**: the three clauses `ContDiff ℝ ∞ F`, `HasCompactSupport F`,
  `tsupport F ⊆ {z | 0 < z.1}` are *exactly* `DATA:559` `MemForceCompact F`, i.e.
  `F_c` — checked in this worktree, see §4 command 4.  The only difference is
  the spelling `{z | 0 < z.1}` versus
  `NavierStokesR3.ProblemStatement.positiveTimeDomain = Ioi 0 ×ˢ univ`, and the
  two sets are equal by `ext; simp` (checked).
* **norm**: the manuscript's `L^q(0,∞;H^s)`, and in the **angular**
  normalization `DATA` fixes: `ARVB:54` `angularRealVectorSlice_pairing` states
  `angularRealization s (angularRealVectorSlice s F hF hc t i) ψ = ∫ x, ψ x * F i (t,x)`,
  which is `DATA:159` `IsSobolevDatum` verbatim.  The cycles-convention
  ancestors (`RVPD:80`, `RPD:107`, `PPD:72`, `PBD:95`) do **not** have this
  property; only the `ARVB` layer does.
* **time domain**: `positiveTimeMeasure = volume.restrict (Ioi 0)`
  (`PTD:11`), which is `DATA:116` `forceTimeMeasure` — the *same* term, so
  `Lp (RealVectorSobolev s) q forceTimeMeasure` and the source's ambient space
  are the same type by `rfl` (checked).
* **vector-ness**: real Euclidean three-vector throughout;
  `RealVectorSobolev s = PiLp 2 (fun _ : Fin 3 => RealSobolevHilbert s)`
  (`RVPD:15`) and `RealSobolevHilbert` is the conjugate-reflection subspace, so
  the manuscript's "take real parts" step (`04-whole-space.tex:250`) is already
  discharged by the carrier.
* **`s` and `q` ranges**: unrestricted real `s`, and `1 ≤ q < ∞`.  Matches the
  manuscript exactly (`04-whole-space.tex:233,243,253`).  **No threshold.**

What is *not* present: the completion identification, the `F_c ⊆ F_R` bridge,
the separated-sum shape the ledger asks `B01` to export, and the manuscript's
three named intermediate stages in `DATA` vocabulary.

## 1. Field-by-field comparison

| Spec field | Paper location | Existing declaration (class / norm / time domain / vector-ness) or gap | Mismatch |
|---|---|---|---|
| `χ`, `chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range` | `04:238` "χ ∈ C_c^∞ equal to one on the unit ball and zero outside the ball of radius two, 0 ≤ χ ≤ 1" | **Present, verbatim.** `CC:29` `baseCutoff` with `CC:40` `baseCutoff_smooth`, `CC:46` `baseCutoff_eq_one (‖x‖ ≤ 1)`, `CC:50` `baseCutoff_eq_zero (2 ≤ ‖x‖)`, `CC:42,44` `baseCutoff_nonneg`/`_le_one`.  Real scalar on `Space`; no time, no vector. | None.  Also `scaledCutoff baseCutoff R = CC:32 cutoff R` by `rfl` (checked), so the paper's `χ_R` is literally the upstream `cutoff R`. |
| `schwartzApprox` | `04:233-237` Fourier truncation/mollification + the `H^s` isometry | **Partial.** `SD:43` `denseRange_weightedFourierLp s` — dense range of `weightedFourierLp s : SchwartzMap Space ℂ → SobolevHilbert s`, every real `s`.  **Scalar complex**, **cycles** convention, no vector, no reality. | Three transports needed: real projection (`RPD:21` `realProjectionTo`), three components (`FHB:35,42` `coord`/`assemble`), angular convention (`ARS:67` `cyclesToAngularReal`, `ARS:89` its realization identity, `ARVB:15` `cyclesToAngularRealVector` — a `≃L[ℝ]`, **not** an isometry, `ARVB:23` bounds it by `frequencyUnit ^ |s|`; density transports, exact norms do not).  Plus: `DATA`'s house form for Schwartz data is one `SchwartzMap Space Space`, while the source has three `SchwartzMap Space ℂ`; Mathlib has no ready finite-product assembly of `SchwartzMap`, so this is the most expensive fidelity-only field. |
| `cutoffApprox` | `04:238-243` `‖(1−χ_R)h_n‖_{H^m} → 0`, then `‖z‖_{H^s} ≤ ‖z‖_{H^m}` | **Partial.** `SCA:177` `approximate ψ n = truncate ψ (n+1)` is `χ_{n+1}ψ`; `SCA:169` `seminorm_truncate_sub_le` is the real-`R` seminorm bound; `SD:51` `weightedFourierLp_physicalCutoff_tendsto` is the `H^s` convergence.  **Scalar complex**, **cycles**, integer sequence. | (a) `ℕ`-sequence versus `Filter.atTop` on `ℝ` (`SCA:169` is already real-`R`, so this is bookkeeping); (b) cycles → angular transport; (c) scalar → real vector; (d) the target is `DATA:186` `sobolevENorm`, a *datum infimum* on the physical field — but only `≤` is needed, so the infimum costs nothing (no datum-uniqueness lemma required). |
| `spatialApprox` | `04:243` + `:250-252` "real vector-valued versions: take real parts" | **Partial.** `SD:59` `dense_compact_weightedFourierLp s` — physical `C_c^∞` functions dense in `SobolevHilbert s`, every real `s`.  **Scalar complex**, **cycles**, no `IsSobolevDatum` statement. | Same three transports as `schwartzApprox`, plus restating the conclusion as `IsSobolevDatum s h H` for the *physical* `h`; the pairing that makes this possible is `CSR:52` `sobolevRealization_compactFourierLp_apply` composed with `ARS`'s `angularRealization_cyclesToAngularReal`.  This is the only spatial field `approxCompact` needs. |
| `temporalApprox` | `04:253-260` restriction to `[1/N,N]`, simple functions, interval approximation, smoothed indicators | **Partial.** `SBD:30` `dense_span_separatedLp` (dense coefficient set × dense scalar time set ⟹ dense separated span, any real normed `H`, any measure) and `PTD:73` `dense_positive_temporal_factors` (`C_c^∞` factors with `tsupport ⊆ Ioi 0` dense in `Lp ℝ q positiveTimeMeasure`).  Carrier-generic, so applies at `H = RealVectorSobolev s` with **no** convention issue. | The source conclusion is `Dense (Submodule.span ℝ {…})` in `Lp H q μ`; the spec wants an explicit finite sum `Σ_{j<J} φ_j(t) • A_j` on **raw paths** with `bochnerDatumENorm`.  Two steps: unwrap `Submodule.span` into a finite ℝ-combination of `separatedLp q h g` (a scalar multiple of a separated product is separated, so the shape survives), and move from the `Lp` quotient to representatives.  No mathematical gap; the largest single unit. |
| `separatedAssembly` | `04:259-260` "the finite sum … is jointly smooth with compact support strictly inside `R³ × (0,∞)`" | **Partial.** `PBD:54` `separated_physical_hasCompactSupport` does the **single** product `a z.1 • ψ z.2`; `PPD:36-53` `separatedLp_mem_positivePhysicalBochner` does the single product's `tsupport ⊆ Ioi 0` pattern. | Needs the finite-sum versions of both (support of a sum ⊆ union of supports), and the additivity of `IsSobolevDatum` over the sum, which needs `integral_finset_sum` with integrability of `ψ · h_j` (Schwartz times compact smooth — immediate). |
| `approxCompact` | `04:219` "dense in each full Bochner space `L^q(0,∞;H^s(R³))`" | **Essentially present.** `ARVB:120` `exists_angular_real_vector_positive_physical_approx`, plus `ARVB:54` `angularRealVectorSlice_pairing` for `IsSobolevPath` and `ARVB:64` `memLp_angularRealVectorSlice` for `AEStronglyMeasurable`.  Correct class, correct angular norm, correct `(0,∞)`, real vector. | Three bookkeeping steps: (i) lift `b` from a raw path to `MemLp.toLp b`; (ii) convert `‖·‖ < ε` in `ℝ` to `bochnerDatumENorm … < η` in `ℝ≥0∞` (handle `η = ⊤`); (iii) note `(F z).ofLp i = f i z` is `rfl` (checked) so the pairing lemma applies to `F` itself. |
| `completionRepresentative`, `completionSurjective`, `completionNorm`, `completionCongr` | `04:219` "full Bochner space"; `01-intro:118-129`; ledger `⟪D01:BochnerLq q X⟫`, `STATEMENTS.md:812-814` | **Gap** (trivial).  `Lp.memLp`, `MemLp.toLp`/`MemLp.coeFn_toLp`, `Lp.norm_def`/`eLpNorm` and `eLpNorm_congr_ae` are all Mathlib. | None mathematically.  Recorded as fields because the ledger asks for a *space object* and `DATA:732` `CompletedDenseVia` quantifies over *paths*; without these four the two readings of `prop:Renergy` are not visibly the same statement. |
| `compactSubsetForceR` | `04:185-193` cor:Rclasses ("`F_R` replaced by `F_c`"), against `02-prelim:17` eq:Rclasses | **Half present.** `L¹_t`/`L²_t` finiteness: `ARVB:64` `memLp_angularRealVectorSlice s F hF hc q` holds for **every** `q`, so `q = 1` and `q = 2` are immediate; the scalar ancestors are `CST:39` `memLp_compactSobolevTimeSlice` and `RPD:86`.  Smoothness-in-time: `CST:18` `contDiff_compactSobolevTimeSlice` gives genuine Banach-valued `ContDiff ℝ ∞` of the **scalar complex cycles** slice path (built on `SCT:16,37,49`); `CST:47` `compact_scalar_force_sobolev_regular` bundles it with the two `MemLp`s at every integer order — i.e. **the manuscript's eq:Rclasses, but only for a scalar complex force**. | **The one real gap.**  No `ContDiff` statement exists for `realCompactSobolevTimeSlice` (`RPD:54`), `realVectorSlice` (`RVPD:46`) or `angularRealVectorSlice` (`ARVB:47`).  Each is a composition with a CLM/CLE (`RPD:21` `realProjectionTo`, `WithLp.toLp 2`, `ARVB:15`), so each transport is a one-liner, but none is written.  Also needed: extracting the components `fun z => (f z).ofLp i` of a given `f` with `MemForceCompact f` (smooth by the coordinate CLM, compactly supported since `tsupport (f · i) ⊆ tsupport f`) — the reverse of `RVPD:18` `physicalVector`. |

### Answers to the three questions the task asks explicitly

1. **Does `exists_angular_real_vector_positive_physical_approx` already give the
   main field, and for which `s` and `q`?**  Yes, up to the three bookkeeping
   steps listed for `approxCompact`.  For **every real `s`** and **every
   `q ∈ [1,∞)`** (`q : ℝ≥0∞`, `q ≠ ⊤`, `Fact (1 ≤ q)`).  It is *not* restricted
   to `s < s_q`, and the manuscript does not restrict it either: `s < s_q`
   enters `prop:Renergy` only at `04-whole-space.tex:262-264`, where
   `cor:Rclasses` supplies a *singular* compact force.  `manuscriptApproximation`
   in `Spec.lean` carries the threshold hypothesis unused, purely to match
   `REnergyAPI.densityInhomogeneous` (`STATEMENTS.md:849-853`).
2. **The `F_c` smoothness-in-time clause.**  `F_c` (`DATA:559`) asks only for
   *joint* smoothness of the physical field, which the source theorem supplies
   directly.  The clause that is missing is the one in **`F_R`**
   (`DATA:544-551`): `ContDiffOn ℝ ∞ G futureTimes` for the order-`m` datum
   path.  It exists upstream for the scalar complex cycles path (`CST:18`) and
   has to be transported through three continuous linear maps; see unit 4.
3. **The `L¹_t`/`L²_t` finiteness of `MemForceR`.**  Already present at the
   angular real-vector level, `ARVB:64`, at every `q` including `1` and `2`, on
   `positiveTimeMeasure`.  Nothing to prove beyond instantiation.

### Two smaller mismatches worth recording

* **`Fact (1 ≤ q)`.**  The source theorem takes it as an instance; `DATA`'s
  `CompletedDense` needs no such instance because `bochnerDatumENorm` is
  `eLpNorm`.  Both `Fact (1 ≤ (1 : ℝ≥0∞))` and `Fact (1 ≤ (2 : ℝ≥0∞))` resolve
  by `inferInstance` (checked), so the implementer supplies them with
  `haveI` from the hypothesis `1 ≤ q`.
* **Angular versus cycles is a bounded equivalence, not an isometry.**
  `ARVB:23` `cyclesToAngularRealVector_norm_le` bounds it by
  `frequencyUnit ^ |s|`.  Density and `Tendsto` transport across it; *exact*
  norm identities do not.  Every field of `BochnerApproxAPI` is stated as a
  density/limit, so this costs nothing — but a future field phrased as a norm
  equality between the two conventions would be false.

## 2. Bounded implementation split

Ten lemma-sized units.  Units 1–3 discharge everything `R46` actually consumes;
4–7 the remaining load-bearing fields; 8–10 the manuscript-fidelity fields and
assembly.  No unit reproves anything already in the tree.

| # | Unit | Size | Statement to prove | Builds on |
|---|---|---|---|---|
| 1 | `sobolevPath_of_compact` | M | For `F : SpaceTimeField` with components `f i` smooth and compactly supported and `∀ z i, (F z).ofLp i = f i z`: `IsSobolevPath s F (angularRealVectorSlice s f hf hc)` and `AEStronglyMeasurable (angularRealVectorSlice s f hf hc) forceTimeMeasure`; and, from `ContDiff ℝ ∞ F`, `HasCompactSupport F`, `tsupport F ⊆ {z \| 0 < z.1}`, `MemForceCompact F`. | `ARVB:54` `angularRealVectorSlice_pairing` (matches `DATA:159` verbatim); `ARVB:64` `.aestronglyMeasurable`; the `MemForceCompact` half is already checked to be `⟨h1, h2, fun z hz => ⟨h3 hz, mem_univ _⟩⟩`. |
| 2 | `approxCompact` | S | `∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s, CompletedDense q s forceClassCompact`. | `ARVB:120` applied to `(hb.toLp b)`; unit 1; `ε := if η = ⊤ then 1 else min 1 η.toReal` with `ENNReal.ofReal_lt_iff`/`Lp.norm_def`; `MemLp.coeFn_toLp` + `eLpNorm_congr_ae` to return to the raw path. |
| 3 | `completion_identification` | S | The four `completion*` fields. | `Lp.memLp`; `⟨hb.toLp b, hb.coeFn_toLp⟩`; `Lp.norm_def` with `Lp.eLpNorm_ne_top`; `eLpNorm_congr_ae`. |
| 4 | `contDiff_angularRealVectorSlice` | M | `ContDiff ℝ ∞ (realCompactSobolevTimeSlice s F hF hc)`, then `… (realVectorSlice s F hF hc)`, then `… (angularRealVectorSlice s F hF hc)`. | `CST:18` `contDiff_compactSobolevTimeSlice`; `(realProjectionTo s).contDiff.comp` (`RPD:21`); `contDiff_piLp`/`Mathlib.Analysis.Calculus.ContDiff.WithLp` (already an import of `RVPD`); `(cyclesToAngularRealVector s).contDiff.comp` (`ARVB:15`). |
| 5 | `compactSubsetForceR` | M | `forceClassCompact ⊆ forceClassR`. | Components `fun z => (f z).ofLp i` of a `MemForceCompact f`: smooth by the coordinate CLM, compact support by `tsupport_comp_subset`; then unit 1 at order `(m : ℝ)`, unit 4 restricted with `.contDiffOn`, and `ARVB:64` at `q = 1, 2`.  Mirrors `CST:47` `compact_scalar_force_sobolev_regular`. |
| 6 | `separatedAssembly` | M | The field, all three conjuncts. | `PBD:54` `separated_physical_hasCompactSupport` summed over `Fin J` (the support of a finite sum lies in the union of the supports); the `tsupport ⊆ Ioi 0 ×ˢ univ` pattern of `PPD:47-53`; `IsSobolevDatum` additivity by `map_sum` of `angularRealization` and `integral_finset_sum`; measurability from continuity. |
| 7 | `temporalApprox` / `SeparatedTemporalDense` | L | The field, and the standalone `def` at every `(q,s)`. | `SBD:30` `dense_span_separatedLp` at `H := RealVectorSobolev s`, `μ := positiveTimeMeasure`, coefficient set `univ`, time set `PTD:73` `dense_positive_temporal_factors`; then `Submodule.mem_span_set`/`Finsupp` unwrapping into `Σ c_k • separatedLp q A_k g_k = Σ (c_k • φ_k) • A_k`; then `SBD:23` `separatedLp_ae` and `Lp.dist_def` to reach `bochnerDatumENorm` on representatives. |
| 8 | `spatialApprox` | M | The field. | `SD:59` `dense_compact_weightedFourierLp`; `RPD:21` `realProjectionTo` + `RPD:34` `realProjectionTo_opNorm_le` for the real part; `FHB:35,42` `coord`/`assemble` and `FHB:64` `approximation_bound` for the three components (the pattern is `RVPD:80` lines 84-103); `ARVB:15` for the convention; `CSR:52` + `ARS:89` `angularRealization_cyclesToAngularReal` for `IsSobolevDatum`. |
| 9 | `schwartzApprox` + `cutoffApprox` | L | The two fidelity-only fields. | `SD:43` `denseRange_weightedFourierLp` and `SD:51`/`SCA:169`/`SCA:188`; a finite-product assembly `(Fin 3 → SchwartzMap Space ℝ) → SchwartzMap Space Space` (no Mathlib API; build with `SchwartzMap.mk` and the componentwise seminorm bounds).  **Fidelity-only:** `R46` consumes neither field, and unit 8 does not depend on them.  If the reviewer prefers a minimal contract, delete both fields and this unit. |
| 10 | `BochnerApproxAPI` term + registration | M | `χ := CC:29 baseCutoff` (five fields discharged by `CC:40,46,50,42,44`, checked); assemble units 2–9; promote to `verification/Contracts/V1/BochnerApprox.lean`, add the typed `Bindings` entry and the `#print axioms` test. | Packaging pattern of `verification/Contracts/V1/Thresholds.lean` and `verification/contracts.json`. |

Optional follow-ups, **not** part of `B01` (recorded so they are not lost):

* **A.** Injectivity of `angularRealization`, i.e. uniqueness of the order-`s`
  datum (`DATA:145-147` calls it unit L1).  Not needed by any `B01` field —
  `cutoffApprox` only uses `sobolevENorm s z ≤ ‖A‖ₑ` for an explicit datum `A` —
  but `R46` will want it as soon as it mixes `forceSobolevENorm` with an
  explicit path.
* **B.** A `ContDiffOn`-hypothesis variant of unit 4, if a consumer ever needs
  the datum path of a force that is smooth only on `[0,∞) × R³`.  `F_c` forces
  are globally smooth, so `B01` does not.
* **C.** `F_c ⊆ F_rd` (`04-whole-space.tex:186-191`).  Belongs to `R45`; unit 5
  produces the datum-path half of what it needs.

## 3. Interface note for B02

`B02` (homogeneous `Ḣ^{-1}`, `04-whole-space.tex:244-252`) shares this lane's
**stage 4 verbatim** and nothing else.  Concretely:

* **Shared, unchanged.**  `SeparatedTemporalDense q s` (`Spec.lean`, and field
  `temporalApprox`).  `04-whole-space.tex:253` writes the Bochner step for
  "any of the preceding separable Hilbert spaces `X`", and in Lean the two
  completions have the *same carrier*: `DATA:200-210` records that
  `bochnerDatumENorm` is literally one expression for both realizations, and
  `DATA:380-390` that `IsHomogeneousPath s` reads a force into the same
  `RealVectorSobolev s` that `IsSobolevPath s` does.  `B02` should therefore
  **import this predicate rather than restate it**; the ledger's instruction
  "formalise it once (B01/B02 share it)" (`STATEMENTS.md:903-904`) is satisfied
  by that single `def`.
* **Shared, unchanged.**  `separatedField`, `separatedPath` and the field
  `separatedAssembly` — with one substitution: `B02`'s assembly clause must
  conclude `IsHomogeneousPath s (separatedField φ h) (separatedPath φ A)` in
  place of `IsSobolevPath`.  Everything else (`MemForceCompact`, measurability)
  is identical and unit 6 proves it once.
* **Not shared.**  The spatial stage.  `B02`'s is the annular construction of
  `04-whole-space.tex:245-249` (`G_n ∈ C_c^∞(R³∖{0})`, `ĥ_n = |ξ|G_n`) followed
  by the low/high split `eq:Rnegative-cutoff`
  (`‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²`, `04-whole-space.tex:246-248`) in place of
  the Leibniz cutoff argument.  `B01`'s `spatialApprox`, `schwartzApprox` and
  `cutoffApprox` have no `Ḣ^{-1}` analogue and must not be reused there.
* **Not shared.**  `compactSubsetForceR` is an inhomogeneous statement about
  `F_R` (`02-preliminaries.tex:17` uses `H^m`, never `Ḣ^s`); `B02` needs it as
  an input, not as an obligation, and should take it from `B01` or from `D01`.
* **Conclusion shape for `B02`.**  `DATA:752` already provides
  `CompletedDenseHomogeneous q s S = CompletedDenseVia q s (IsHomogeneousPath s) S`;
  the `B02` analogue of `approxCompact` should be
  `CompletedDenseHomogeneous 2 (-1) forceClassCompact`, and `R46` then consumes
  the two conclusions side by side.

## 4. Commands run

All from the worktree, after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`
and no `-j`.

1. `bash scripts/lean-install.sh` — exit 0, `== OK`.
2. `cd verification && lake build Contracts.V1.Data NSFormalization.Paper3.AngularRealVectorBochner`
   — `Build completed successfully (8828 jobs)` (pre-existing upstream linter
   warnings in `NSFormalization/Paper3/RealPositiveDensity.lean` and
   `RealVectorPositiveDensity.lean`; none in the contract).
3. `cd verification && lake env lean ../research/B01/Spec.lean` — no output,
   3.7 s.
4. Scratch checks (`lake env lean` on temporary files, not committed):
   `#print axioms BochnerApproxAPI` → `[propext, Classical.choice, Quot.sound]`
   (same for `bochnerApproxStatement`, `manuscriptApproximation`,
   `SeparatedTemporalDense`); `Fact (1 ≤ (1 : ℝ≥0∞))` and `Fact (1 ≤ (2 : ℝ≥0∞))`
   by `inferInstance`; `positiveTimeDomain = {z | 0 < z.1}` by `ext; simp`;
   `Lp (RealVectorSobolev s) q forceTimeMeasure = Lp (RealVectorSobolev s) q positiveTimeMeasure`
   by `rfl`; `(v : Space).ofLp i = v i` by `rfl`; the source's three clauses ⟹
   `MemForceCompact`; `scaledCutoff baseCutoff R = cutoff R` by `rfl` and the
   five `χ` fields from `CC:40,46,50,42,44`.
