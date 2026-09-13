# D01 reconciliation: drafts A and B into `verification/Contracts/V1/Data.lean`

Target: `verification/Contracts/V1/Data.lean`, namespace
`BlowupDensity.Contracts.V1.Data`.  63 declarations (`abbrev`/`def`/`structure`),
no theorem with content, no `sorry`, no `axiom`, no placeholder `Prop` field,
a doc comment on every declaration and on every structure field.
§5 records the revisions made after `REVIEW_RECONCILIATION.md`.

Inputs: `DraftA.lean` + `COMPARISON_A.md` + `REVIEW_A.md` (**REJECT**),
`DraftB.lean` + `COMPARISON_B.md` + `REVIEW_B.md` (**ACCEPT-WITH-NOTES**),
`research/section4/STATEMENTS.md` §8–§9, `research/section4/REVIEW.md` item 1.
Paper line numbers are as in `paper/sections/`.

This file supersedes the implementation splits of `COMPARISON_A.md` §3 and
`COMPARISON_B.md` §2.

---

## 1. Object-by-object record

Ledger tags are the `⟪D01:…⟫` / `⟪G01:…⟫` identifiers of
`research/section4/STATEMENTS.md` §8.  `Data.lean` line numbers are the
declaration lines.

### 1.1 Base setting

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| `R³`, real Euclidean 3-vector fields | `01-intro:91,103` eq:NS | upstream `Space` | upstream `Space` | both faithful | **Both.** `SpatialField`, `SpaceTimeField`, `SpaceTimeScalar` (`:99,104,108`) reuse the pinned `NavierStokes.ProblemStatement` types; time is the first coordinate. | `⟪D01:R3⟫` |
| angular Fourier transform | `01-intro:91` | `Source.angularFourier` + `angularRealization` | same | A: "normalization discharged by `angularFourier_eq_integral` rather than assumed"; B: "never uses Mathlib's cycles `𝓕` as the normalization" | **Both.** Every Sobolev object routes through `angularRealization`. | `⟪D01:R3⟫` |
| reality `F(-ξ) = conj F(ξ)` | `02-prelim:72` | `realSubspace` (+ a named predicate) | `realSubspace` via `RealSobolevHilbert` | both faithful | **B.** Reality is built into the carrier, so no separate field or predicate is needed; A's `IsRealFrequencyDatum` is dropped as redundant. | `⟪D01:R3⟫` |
| vector norm | `01-intro:103` | `RealVectorSobolev` (`PiLp 2`) | same | both reviews: `PiLp 2` is right, the sup-normed `ForceDatum` is not | **Both.** | `⟪D01:R3⟫` |
| `[0,∞)` vs `(0,∞)` | `02-prelim:22`, `01-intro:140` | `forceTimeDomain` (dead), `positiveTimeMeasure` | `Ici 0`, `positiveTimeMeasure` | REVIEW_A minor: A's `forceTimeDomain` is dead code | **Both, deduplicated.** `futureTimes` (`:113`) is now actually used in `MemForceR`; `forceTimeMeasure` (`:118`) is `positiveTimeMeasure`. | `⟪D01:BochnerLq⟫` |
| negative-time freedom | `02-prelim:24` | not addressed | docstring claimed a zero extension, nothing enforced it | REVIEW_B issue 5: "not extensional; blocks a separated metric (U10)" | **New: `AgreesOnFuture` (`:128`).** Imposing `f = 0` for `t < 0` inside `MemForceR` would *weaken* Theorem 4.1(i) (fewer reference forces `g`), so the convention is recorded as the equivalence by which the classes are extensional and by which a separated metric must be quotiented. | — |

### 1.2 Inhomogeneous Sobolev scale and time norms

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| `z` has an order-`s` datum | `01-intro:94` | `IsAngularDatum` (Schwartz pairing) | `RepresentsSlice` (same pairing) | both faithful; modelled on `angularRealVectorSlice_pairing` | **Both** — `IsSobolevDatum` (`:160`), `IsSobolevPath` (`:174`).  The pairing is the only form that makes negative orders meaningful for a classical field. | `⟪D01:Hs s⟫` |
| `‖z‖_{H^s(R³)}` | `01-intro:94` | literal Fourier integral `angularVectorSobolevNorm` | `⨅` over data, on `𝓢'` | REVIEW_A issue 2: A's integral is junk `0` whenever the slice is outside `L¹`, and `H^∞ ⊄ L¹` on `R³` | **B's totalization, on the physical field.** `sobolevENorm` (`:189`) = the norm of the unique datum, `⊤` off `H^s`. A's literal integral is dropped as theorem-facing junk. | `⟪D01:Hs s⟫` |
| Bochner norm of a datum path | `01-intro:118-129` | `forceBochnerNorm = eLpNorm G q` | `∫⁻` of a pointwise `⨅` | REVIEW_B issue 3: B's is a *lower* integral, can under-report | **A.** `bochnerDatumENorm` (`:205`) is `eLpNorm` on `positiveTimeMeasure`; `MemBochnerDatum` (`:212`) is Hunter's strongly-measurable membership. The same expression is also the `L^q(0,∞;Ḣ^s)` norm, since `h ↦ abs(ξ)^{-s}·ĥ` is an isometry onto the same `L²`. | `⟪D01:BochnerLq⟫`, `⟪D01:normLqHs⟫`, `⟪D01:normLqDotHs⟫` |
| `‖f‖_{L^q_tH^s_x}` on a physical field | `01-intro:125` | `forcePhysicalTimeNorm` (junk) **and** an `∃`-path form inside the density predicate | `bochnerSobolevENorm` on distributions (lower integral) | REVIEW_A issue 2 kills A's physical norm; REVIEW_B issue 3 flags B's | **New, combining both:** `forceSobolevENorm` (`:225`) = `⨅` over order-`s` paths that are `AEStronglyMeasurable`, of the Bochner `eLpNorm`.  Measurable-path form, no lower-integral gap; the fail-safe value is `⊤`, never an under-report. `forceSobolevENormL1/L2` (`:231,235`). | `⟪D01:normLqHs⟫` |
| `‖f‖_{L^q_tL^p_x}` | `01-intro:134` | absent | absent | — | **New:** `IsLebesgueSlicePath` (`:242`), `mixedLebesgueENorm` (`:251`), same measurable-path shape. `q=1,p=2` is prop:Renergy's `L¹_tL²_x`; `q=⊤` is `⟪D01:normLinfty⟫`. | `⟪D01:normLqLp⟫`, `⟪D01:normLinfty⟫` |
| `s_q = 2/q − 3/2` | `04:8` | `criticalOrder` | `criticalOrder` | both correct (`1 ↦ 1/2`, `2 ↦ −1/2`) | **Both.** `criticalOrder` (`:259`). | `⟪D01:F_R⟫` consumers, §8.10 |
| `β(q,s)` | `04:57` | absent (only `criticalOrder`) | `scalingExponent` | REVIEW_B: matches `ThresholdAPI.exponent` | **B.** `scalingExponent` (`:265`); a binding should identify it with `ThresholdAPI.exponent` / `Paper3.forceExponent`. | §8.10 |
| exponent typing | — | `q : ℝ` in one norm, `ℝ≥0∞` in another | `q : ℝ` throughout | REVIEW_A minor: A's mismatch forces `ENNReal.ofReal` round-trips | **Fixed:** every *time* exponent is `ℝ≥0∞` (so `q = ⊤` is available), every *Sobolev order* is `ℝ`, and `criticalOrder`/`scalingExponent` stay in `ℝ`. | — |

### 1.3 Homogeneous realizations

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| the space `Ḣ^s` | `02-prelim:58-69`, `app-B:44,56-70` | scalar `Ḣ^{-1}` only | general `s`, no integrability clause | REVIEW_A minor: A's is unusable for prop:Renergy (needs vector, time-integrated); REVIEW_B issue 4: B's non-integrable integrand silently returns `0` | **B's general `s`, plus the paper's own temperedness estimate as an explicit `Integrable` clause.** `IsHomogeneousDatum` (`:321`), `MemHomogeneous` (`:329`), `homogeneousENorm` (`:335`), `MemDotHNegOne` (`:340`), and the vector forms (`:344,349`) over a locally declared `VectorDistribution` (`:284`).  This is exactly `research/section4/REVIEW.md` item 1's recommendation: **one** definition for `−3/2 < s < 3/2`, with the App-B completion identity and the smooth-compact finiteness left as lemmas. Sign convention checked at `s = −1`: `ĥ = abs(ξ)·G`, i.e. `abs(ξ)^{-1}·ĥ = G ∈ L²`, literally eq:homogeneous-realization. | `⟪D01:dotHs a⟫`, `⟪D01:dotHminus1⟫` |
| `L^q(0,∞;Ḣ^s)` on a physical field | `04:212,219,226` prop:Renergy | absent | `bochnerHomogeneousENorm` via a pointwise `∫⁻` (lower integral) | REVIEW_A minor and REVIEW_RECONCILIATION issue 2: prop:Renergy's homogeneous clause must be statable | **New.** `IsSliceDistribution` (`:298`) reads a physical slice as a tempered vector distribution — the same Schwartz pairing `IsSobolevDatum` uses, so no `L² → 𝓢'` homogeneous multiplier and no new Parseval convention.  `IsHomogeneousVectorDatum` (`:355`), `IsHomogeneousSliceDatum` (`:364`), `IsHomogeneousPath` (`:372`), and `forceHomogeneousENorm` (`:387`) in the same measurable-path form as `forceSobolevENorm`. | `⟪D01:normLqDotHs⟫`, `⟪D01:normLqDotHminus1 2⟫` |
| the *quantity* `‖z‖_{Ḣ^s}` on a smooth field | `01-intro:105`, `04:70-72`, `app-B:31,107`, `app-A:24` | `angularVectorHomogeneousNorm` (real-valued) | absent | REVIEW.md item 1: "`‖v‖_{Ḣ^{3/2}}` occurs as notation, so D01 must still define that norm" | **A's literal integral, in `ℝ≥0∞`.** `homogeneousFourierENorm` (`:407`), with `dotHThreeHalvesENorm` (`:415`) and `dotHHalfENorm` (`:420`).  This is the only object usable at `s = 3/2`, where `app-B:101` refuses a space and where the realization above genuinely fails (the temperedness integral diverges at `2s = 3`).  Its docstring records that it must not be used on a general `H^∞` slice. | `⟪D01:dotHsFinite s⟫`, the `Ḣ^{3/2}` quantity |

### 1.4 Energy norm

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| `E_T` | `01-intro:143` eq:Enorm | `ℝ≥0∞`, `essSup` on `Ioo 0 T`, Frobenius gradient in `WithLp 2` | `ℝ` via `.toReal`, reusing `CompactEnergy.l2Sq`/`dissipation` | REVIEW_A: A's is faithful (no endpoint at `T`, Frobenius not operator norm); REVIEW_B issue 2: `.toReal` sends `⊤ ↦ 0`, so eq:REclose is satisfiable by a field of infinite energy | **A.** `energyEssSup` (`:437`), `spatialGradient` (`:446`), `energyGradient` (`:452`), `energyENorm` (`:468`).  `ℝ≥0∞` removes the vacuity; B's reuse of `CompactEnergy` is dropped because it forces the `.toReal`. | `⟪D01:normET T⟫` |

### 1.5 Data and force classes

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| `H^∞` | `02-prelim:12,15` | `ContDiff` + a datum at every integer order | `ContDiff` + `∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume` | both faithful; A: `ContDiff` "usefully pins the representative"; B: field-for-field `SmoothL2Field` | **A's datum form.** `MemHInfty` (`:488`).  Uniformity: "`H^m`" then means one thing across `X_R`, `F_R` and the solution class. B's jet form is the binding to the upstream structure and becomes unit L2. | `⟪D01:X_R⟫` |
| `L²_σ` | `02-prelim:6` | inlined `∑ᵢ (fderiv …) i` | `spatialDivergence` on the time-independent lift | equivalent | **B.** `IsSolenoidal` (`:497`), so one divergence operator serves the datum class and the solution class. | `⟪D01:L2sigma⟫` |
| `X_R` | `02-prelim:12` eq:Rinitial | `datumClassR` | `XR` | both: no Fréchet topology, correct because 4.1 fixes `a` | **Both.** `initialClassR` (`:502`). | `⟪D01:X_R⟫` |
| `S_σ` | `04:192` | absent | `SchwartzSolenoidal` | REVIEW_A: outside A's scope | **B.** `initialClassSchwartz` (`:506`). | `⟪D01:S_sigma⟫` |
| **`F_R`** | `02-prelim:17` eq:Rclasses | `MemForceR` **without** `f ∈ C^∞` | `ForceR` structure **with** `ContDiffOn ℝ ∞ field futureDomain` | **REVIEW_A issue 1 (BLOCKER):** without the `C^∞` clause `MemForceR` is stable under null-set edits of `f`, so `B^R_{ν,a,T}` leaks, 4.1(i) is vacuous and the "only if" of 4.1(ii) is **false** (machine-checked). REVIEW_B explicitly cleared B on this point. | **B's smoothness clause, in A's predicate form.** `MemForceR` (`:537`) = `ContDiffOn ℝ ∞ f futureDomain` ∧ per-order (datum path, `ContDiffOn … (Ici 0)`, `MemLp _ 1`, `MemLp _ 2`).  Predicate on `SpaceTimeField`, **not** B's bundled structure, so that `F_c ⊆ F_rd ⊆ F_R` are set inclusions in one type and `maximalLifespanR ν a ·` is literally the same function on all three — STATEMENTS §9 items 11 and 12. | `⟪D01:F_R⟫` |
| `F_c` | `04:185` | `MemForceCompact` | `MemFc` | identical, both reuse `CompactPositiveTimeSupport` | **Both.** `MemForceCompact` (`:552`), `forceClassCompact` (`:556`). | `⟪D01:F_c⟫` |
| `F_rd` | `04:186-191` | absent | joint `iteratedFDerivWithin` on `futureDomain`, `∀ N k, ∃ C` | REVIEW_B: "matches the paper's `∀ N, α, j` family exactly; no common bound imposed" | **B.** `MemForceRapid` (`:565`), `forceClassRapid` (`:571`). | `⟪D01:F_rd⟫` |

### 1.6 Pressure, solutions, lifespan, breakdown

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| pressure gauge | `02-prelim:31` | `PressureGaugeEquiv T` (on `Ico 0 T`) | global | both faithful | **Set-parametric, subsuming both:** `PressureGaugeEquivOn` (`:582`).  The *spatially constant* gauge of `04:320` is the case of a constant `c`. | `⟪D01:pressureGaugeFreedom⟫` |
| radial potential | `02-prelim:97` | `radialPressurePotential` | `pressurePotential` | identical transcription | **Both.** `pressurePotential` (`:589`). | `⟪D01:gradPressure⟫` (potential clause) |
| `∇p = (I−P)(f − ∇·(u⊗u))` | `02-prelim:90` eq:Rpressure | not encoded | not encoded | both reviews: correct to omit — for a smooth solenoidal solution it follows from the momentum equation plus `∇p ∈ L²` | **Omitted deliberately**; becomes unit L9. | `⟪D01:gradPressure⟫` (partial) |
| classical solution | `02-prelim` §2.1/§2.3, prop:local | `ClassicalSolutionR ν T a f`, all-order continuous **datum** path | `ClassicalSolutionR ν a f T`, `MemHInfty` slices + `L²` **jet** paths + a.e. identification + continuity | both faithful; both impose the equation on `Ioo 0 T` (two-sided `∂_t` at `0` is undetermined) | **A's datum form, B's argument order.** `ClassicalSolutionR` (`:617`).  Fewer fields, and `C([0,S];H^m)` is `ContinuousOn G (Ico 0 T)` in the same `H^m` sense as `F_R`.  `pressure_gradient : MemLp (pressureGradient …) 2 volume` and **no** scalar `p ∈ L²`, per `02-prelim:101`. | `⟪D01:IsClassicalSolution⟫` |
| `T^ν_{max,R}(a,f)` | `02-prelim:32` | `⨆ T, ⨆ _ : Nonempty …, ofReal T` | identical | both: same shape as `SmoothLifespan.lifespan`; empty sup `= 0`, so downstream statements must carry the class hypotheses | **Both.** `maximalLifespanR` (`:650`). | `⟪D01:Tmax⟫` |
| "regular through `T`" | `02-prelim:34` | `RegularThrough` | identical | both faithful | **Both.** `RegularThrough` (`:657`). | `⟪D01:RegularThrough⟫` |
| `B^R_{ν,a,T}` | `02-prelim:42` | `Set SpaceTimeField` with a `MemForceR` conjunct | `Set ForceR` | REVIEW_A/B both accept theirs | **A's carrier, generalized:** `breakdownSetIn` (`:665`) is parametric in the ambient class, `breakdownSetR` (`:671`) and `breakdownSetRZero` (`:679`) are the `F_R` instances.  STATEMENTS §9 item 12 requires one lifespan function across `F_R`, `F_c`, `F_rd`. | `⟪D01:B_R⟫` |

### 1.7 Density and grids

| Object | Paper | A | B | Reviews | Final choice and reason | Ledger |
|---|---|---|---|---|---|---|
| relative density | `01-intro:137`, `04:8` | `RelativelyDenseInForceR` (`Y = F_R` fixed) | `RelativelyDense` (`Y` = the whole bundled type) | both: the `ε` form is right for a pseudometric topology (periodic analogue `denseAt_iff_approximation` proved) | **Parametric in the ambient class:** `RelativelyDense q s Y S` (`:695`), `BreakdownDenseR` (`:700`).  `research/section4/REVIEW.md` item 17 asks exactly for this so that R45 and R46 share one instance. | `⟪D01:DenseRel⟫` |
| density in the completion | `04:219` prop:Renergy | absent (declared out of scope) | `CompletedDense` quantified over **all** `ℝ → ForceDistribution` | **REVIEW_B issue 1 (major):** a target off `H^s` sits at distance `⊤` from everything, so B's predicate is false for every `S` and prop:Renergy stated with it is unprovable. **REVIEW_RECONCILIATION issue 1:** the *approximating* path also needs measurability | **Fixed twice.** `CompletedDenseVia` (`:725`) quantifies the target over the completion itself — a datum path with `MemBochnerDatum q s b` — and requires `AEStronglyMeasurable D forceTimeMeasure` of the approximant, closing the lower-integral gap on both sides of the quantifier.  It is parametric in the realization, so prop:Renergy's two clauses are `CompletedDense` (`:736`, inhomogeneous) and `CompletedDenseHomogeneous` (`:745`, `q = 2`, `s = -1`).  Kept distinct from `RelativelyDense` (STATEMENTS §9 item 11, C4). | `⟪D01:DenseRel⟫` (second half) |
| grid | `04:288` | absent | reuses `CartesianGrid` | REVIEW_B: per-axis widths, half-open `cell`, positive finite volume | **B.** `Grid` (`:759`), with the docstring stating the ledger's recommended shape explicitly: **per-axis mesh widths, arbitrary offset, half-open cells**, infinitely many cells indexed by `Fin 3 → ℤ`. | `⟪G01:UniformCartesianGrid⟫`, `⟪G01:cells⟫` |
| `A_h` | `04:290-291` | absent | `cellAverage` + `gridObservation` | REVIEW_B: matches §4.8 with coordinatewise equality | **B.** `cellAverage` (`:767`), `gridObservation` (`:776`).  The componentwise spelling `Paper3.componentCellAverage` (`CompactObservations.lean:62`) already exists and carries the grid theorems; agreement is unit L11. | `⟪G01:cellAverage⟫` |

---

## 2. Canonical local dependencies

The contract layer is implementation-independent by default.  `Data.lean`
imports Mathlib, the pinned upstream `NavierStokes.*` package, and exactly six
local modules, each of which fixes a *definition-level convention* the whole
project treats as canonical.  Every one is unavoidable in the sense that
re-declaring it locally would create a second, competing spelling of a
convention that other lanes already build on.

| module | declarations used | why not re-declared locally |
|---|---|---|
| `NSFormalization.Source.FourierConvention` | `angularFourier` | It *is* the manuscript's `(2π)^{-3/2}∫e^{-ix·ξ}` transform, and `angularFourier_eq_integral` is the in-tree proof of that identification.  A local copy would have to be re-proved equal to it, or silently diverge on the `2π` convention — the single largest fidelity hazard in this project. |
| `NSFormalization.Paper3.AngularFourierDilation` | `angularRealization`, `angularFourierDistribution` | The only in-tree `L² → 𝓢'` map carrying the manuscript weights, built from `angularDistributionDilation ∘ 𝓕` in ~200 lines of definitions; its injectivity (`:203`) is what makes every datum in this contract unique. |
| `NSFormalization.Source.RealSobolev` | `FourierData` in code; `realSubspace` / `RealSobolevHilbert` reach the contract only through `RealVectorSobolev` | The reality constraint `F(-ξ) = conj (F ξ)` as a *closed real subspace*, so reality is carried by the type rather than by a side condition. Already in the closure of the previous module. |
| `NSFormalization.Paper3.RealVectorPositiveDensity` | `RealVectorSobolev` | The Euclidean (`PiLp 2`) three-vector carrier of `01-intro:103`, and the normed instances the Bochner norms need.  One module beyond the closure already forced by `AngularFourierDilation`.  The alternative sup-normed `ForceDatum` is *not* the manuscript's vector norm. |
| `NSFormalization.Paper3.PositiveTemporalDensity` | `positiveTimeMeasure` | The `(0,∞)` force-time measure of `01-intro:140`.  Already in the closure above; re-declaring `volume.restrict (Ioi 0)` would fork the name that `RealAdmissibleForce` and the existing density work already use. |
| `NSFormalization.Paper3.GridGeometry` | `CartesianGrid`, `CartesianGrid.cell` | Grid geometry in exactly the shape STATEMENTS §8.9 recommends; two modules, 279 lines, no proof content beyond the geometry lemmas.  The existing grid-observation theorems are stated against this structure. |

Total added closure over Mathlib: 51 modules / 7161 LOC, of which 35 local
(3795 LOC) and 16 pinned upstream, built in ~2 min from a cold local cache.  Explicitly **not** imported:
`RealAdmissibleForce`, `AngularForceNorms`, `HomogeneousRealization`,
`InsertionEnergy`, `CompactEnergy`, `CompactObservations`, `SmoothLifespan`,
`ManuscriptTopology`, `Euler.LpSmoothField` — every one of these is a *proof*
module; each is named below as a binding target instead.

**Policy change required.**  `experiments/check_contracts.py` previously
allowed a `Contracts.*` module to import only `Mathlib`, `Lean`, `Init` and
`Contracts.*`, which rejects the import policy this task mandates.  The gate is
now an explicit, auditable list matched by **exact module name on both halves**:
a seven-element `CONTRACT_CANONICAL_MODULES` frozenset holding the six local
modules above plus the single pinned upstream module
`NavierStokes.R3.ProblemStatement`, together with a prefix rule for
`Mathlib.` / `Lean.` / `Init.` / `Contracts.` and exact matches for the bare
roots `Mathlib`, `Lean`, `Init`.  There is no package prefix on the vendor side
any more, so the 643 other `NavierStokes.*` modules — the comparator machinery
included — are rejected, and `MathlibExtras.X` or `Initialize.X` no longer slip
past the root rule.  The list governs **direct** imports, not the transitive
closure.  `experiments/test_contract_policy.py` pins this in both directions:
four unit tests on `contract_import_allowed`, and two **end-to-end** tests that
drive `check()` over a throwaway tree containing one probe contract — the
negative case asserts the `AssertionError` names the offending module.  This is
a reviewed policy change, not a routine edit; see the open questions in §4.

---

## 3. Remaining implementation split

Twelve lemma-sized units.  This list supersedes `COMPARISON_A.md` §3 (L1–L10)
and `COMPARISON_B.md` §2 (U1–U10); the correspondence is given in the last
column.  "Binds to" names an existing declaration; "**gap**" means nothing
suitable exists in tree.

| # | Obligation | Binds to / gap | supersedes |
|---|---|---|---|
| **L1** | Datum uniqueness: `IsSobolevDatum s z A → IsSobolevDatum s z B → A = B`, and `sobolevENorm s z = ‖A‖ₑ` for that `A`; `sobolevENorm s z = ⊤` iff no datum exists. Makes the `⨅` an honest norm. | Binds: `Paper3.angularRealization_injective` (`AngularFourierDilation.lean:203`), `Paper3.MemAngularSobolev.exists_unique_datum` (`AngularSobolevClass.lean:68`), `mem_range_angularRealization_iff` (`AngularSobolevClass.lean:54`), plus `PiLp` coordinate injectivity. Order-theoretic. | A-L1, B-U1 |
| **L2** | `MemHInfty a ↔ ContDiff ℝ ∞ a ∧ ∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`, i.e. the datum form equals draft B's jet form; and either implies `∃ A : SmoothL2Field Space, A.field = a`. | Binds: `EulerLpTranslation.SmoothL2Field` (`vendor/…/Euler/LpSmoothField.lean:31`), `Source.FourierPhysicalJets.smoothL2FieldOfFourier` (`:169`), `physicalJetLp_ae` (`:159`). **Gap** in the `⟸` direction at non-compact data: only `Paper3.realCompactSobolevTimeSlice` (`RealPositiveDensity.lean:54`) currently produces data, and only for compact smooth input. | A-`X_R` row, B-U2 |
| **L3** | `IsSolenoidal a` agrees with the other in-tree divergences and implies membership in the closed `L²` divergence-free subspace. | Binds: `EulerSmoothLimit.divergence` (`Euler/EulerProof.lean:5216`), `divergenceFreeSpace` (`Euler/EulerProof.lean:1340`), `Source.OrdinaryForcedLocal.initial_divergenceFree` (`OrdinaryForcedLocal.lean:18`), `Comparator.divergence` (used by `Paper3.GridObservations`). Definitional bookkeeping (trace of `fderiv` vs coordinate sum). | B-U3 |
| **L4** | `F_R` algebra: `0 ∈ F_R`; closure under `+`, `−`; and `MemForceR g → MemForceCompact F → MemForceR (g + F)`. This is what thm:Rinsert needs for `g_ε = g + H_ε + F_ε ∈ F_R`. Also `MemForceCompact f → MemForceR f` and `F_c ⊆ F_rd ⊆ F_R`. | Binds: `Paper3.realAdmissibleForce_add/neg/sub` (`RealAdmissibleForce.lean:30,41,49`), `realAdmissibleForce_add_compact` (`:99`), `realAdmissibleForce_compactForceDistribution` (`:86`), `angularRealVectorSlice` (`AngularRealVectorBochner.lean:47`) with `memLp_angularRealVectorSlice` (`:64`). Adaptation: transport from the sup-normed `ForceDatum` to `RealVectorSobolev` via `cyclesToAngularRealVector` (`AngularRealVectorBochner.lean:15`). | A-L2/L3, B-U4 |
| **L5** | Order monotonicity with constant one: `s ≤ r → sobolevENorm s z ≤ sobolevENorm r z`, hence `forceSobolevENorm q s ≤ forceSobolevENorm q r`. Needed by thm:Rmain's converse (`H^s ↪ H^{1/2}`, `H^s ↪ H^{-1/2}`) and by the last step of thm:Rinsert (`04:78`). | Binds: `Paper3.sobolevOrderLowering` (`SobolevOrderLowering.lean:26`) with `sobolevOrderLowering_norm_le` (`:39`) and `sobolevRealization_orderLowering` (`:78`). **Neither comparison found this module**; A-L5 called it a gap. Remaining work is transporting it across the dilation, for which `angularDistributionDilation_weight_cancel` (`AngularFourierDilation.lean:142`) is available. | A-L5 (was "gap") |
| **L6** | `forceSobolevENorm q s (f − g) = physical slicewise norm` for a `C_c^∞` difference; in particular `t ↦ ‖(f−g)(t)‖_{H^s}` is measurable. This is the bridge that lets the *already proved* scaling estimates discharge thm:Rmain's convergence. | Binds: `angularRealVectorSlice_pairing` (`AngularRealVectorBochner.lean:54`), `norm_angularDatum` (`AngularFourierDilation.lean:228`), `Source.vectorAngularSobolevNorm_equivalence` (`AngularForceNorms.lean:19`), then `compact_angular_force_L1_tendsto` (`:88`) and `compact_angular_force_L2_tendsto` (`:98`). | A-L4 (whose unrestricted form REVIEW_A showed **false**; the `L¹`-slice hypothesis is now part of the statement), B-U5 |
| **L7** | `Ḣ^s` is well posed on `−3/2 < s < 3/2`: the `Integrable` clause of `IsHomogeneousDatum` holds for every `G ∈ L²` and every Schwartz `φ`; the datum is unique; `homogeneousENorm` is attained; `G ↦ u` is injective (no polynomial ambiguity). | Partially binds: `Source.FractionalRealization.realization_toDistribution` (`:78`), `realization_norm_le_datum` (`:96`) for `0 < a < 3/2`; `Paper3.angularFourierDistribution_injective` (`AngularSobolevClass.lean:22`) for uniqueness; `Paper3.compact_homogeneous_norm_bound` (`HomogeneousRealization.lean:17`) for finiteness on compact inputs. **Gap** for the negative range and for the `L² → 𝓢'` direction: `HomogeneousRealization.lean` states outright that a full homogeneous multiplier is intentionally absent (`‖ξ‖` is not `HasTemperateGrowth`). | A-L6/L7, B-U6 |
| **L8** | `homogeneousFourierENorm` is finite on smooth compactly supported profiles for `−3/2 < s < 0`, uniformly over a family with common compact support and uniform derivatives (`04:70`); and `sobolevENorm s z ≤ homogeneousFourierENorm s z` for `s < 0` (from `(1+abs(ξ)²)^s ≤ abs(ξ)^{2s}`, `04:71`). Also the exact `(2π)^s` factor to `Source.homogeneousFourierNorm`. | Binds: `Paper3.compact_homogeneous_norm_bound` (`HomogeneousRealization.lean:17`), `Source.homogeneousFourierNorm` (`TimeNormScaling.lean:68`), `Source.frequencyUnit` (`FourierConvention.lean:15`), `angularSobolevSq_eq_frequency_weight` (`FourierConvention.lean:50`). Change of variables, no analysis. | A (implicit), B-U7 |
| **L9** | Pressure package: (a) `PressureGaugeEquivOn (Ico 0 T)` preserves `ClassicalSolutionR` (needs `c` differentiable, or insensitivity of `pressureGradient`); (b) `pressurePotential G` has gradient `G` when `∂_jG_k = ∂_kG_j`; (c) eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` ⟺ `momentum` given `divergence` and `∇p ∈ L²`. | (a),(b) self-contained calculus, the manuscript's own two-line argument (`02-prelim:99`). (c) **gap**: needs the Leray complement on physical fields. Reusable at the distributional level as HeliCorgi `MNS2.r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259`) and `r3LerayComplementL2` (`:228`), blocked on toolchain task U05 (HeliCorgi is Lean 4.32.1, this project 4.34.0-rc2). | A-L8/L9, B-U8 |
| **L10** | Lifespan interface for `ClassicalSolutionR`: restriction to shorter horizons; `maximalLifespanR ν a f ≤ ofReal T ↔ ∀ S > T, IsEmpty (ClassicalSolutionR ν a f S)`; and the two-case alternative "breaks down by `T`, or is regular through `T`". | Binds by direct transcription: `Source.SmoothLifespan.lifespan` (`SmoothLifespan.lean:41`), `lifespan_le_iff` (`:48`), `lifespan_le_iff_no_extension` (`:58`), `bad_or_regular_reference` (`:70`), `Flow.restrict` (`:83`), `lifespan_eq_of_forall_shorter_of_upper_bound` (`:124`). Only the structure changes; all proofs are order-theoretic. | A-L10, B-U9 |
| **L11** | `forceSobolevENorm q s (· − ·)` is a pseudometric on `forceClassR`, separating modulo `AgreesOnFuture`, and `RelativelyDense q s Y S ↔ Dense S` in the induced relative topology. Also `cellAverage C z j = componentCellAverage C z j` under integrability. | Binds by analogy: `Paper1.ManuscriptTopology.forceEMetric` (`:139`), `forceMetric` (`:150`), `relativeTopology` (`:156`), `DenseAt` (`:161`), `denseAt_iff_approximation` (`:176`). **Gap** for separation on `R³`: the periodic proof `eq_of_forceDistance_eq_zero` (`:44`) uses periodic Fourier uniqueness and must be redone with `angularRealization_injective`; the quotient must be by `AgreesOnFuture`. Cell averages bind to `Paper3.componentCellAverage` (`CompactObservations.lean:62`) and `Paper3.actual_force_cell_averages_eq` / `actual_velocity_cell_averages_eq` (`ActualGridObservations.lean:22,73`). | B-U10, plus the new grid clause |
| **L12** | `MemForceR f → forceSobolevENorm q s f < ⊤` for **every real** `s` and `q ∈ {1,2}` (`STATEMENTS.md` §8.6 derived fact); and `MemBochnerDatum` of the resulting path. Required before `RelativelyDense` can be read as an approximation statement rather than a `⊤ < ⊤` triviality. | Follows from L5 (lower `s` from the integer clause) plus L1. No existing declaration states it. | new (neither comparison listed it) |

Out of D01's scope by construction, and unchanged from both comparisons: local
existence / uniqueness / continuation for `ClassicalSolutionR` (A01, A02, A04 —
this contract never asserts the class is inhabited); the critical embeddings and
the `L¹`/`L²` regularity balls (A03, A05, R43, R44); the insertion family
itself (I01, I02, I03, R42).

---

## 4. Ledger D01 requirements **not** covered

Every item below is a `⟪D01:…⟫` or `⟪G01:…⟫` entry of `STATEMENTS.md` §8 that
`Data.lean` does not define, with the reason.

**Definitions that are lemmas, not definitions** (§8.2, §8.4) — these are
*properties* of objects already fixed here, so they belong to the split above
or to A03/A05, not to a data contract:
`‖z‖_{H^s} ≤ ‖z‖_{H^r}` for `s ≤ r` (L5); `‖z‖²_{H^{3/2}} = ‖z‖²_{H^{1/2}} +
‖∇z‖²_{H^{1/2}}`; `‖z‖²_{H²} ≤ C(‖z‖²₂ + ‖Δz‖²₂)` and `‖D²z‖₂ = ‖Δz‖₂`;
separability of `H^s` and the isometry `h ↦ ⟨ξ⟩^sĥ` onto `L²` (L1);
the App-B completion identity, the unique `L^{p_a}` representative and
`p_a = 6/(3−2a)`; the pairing `|⟨h,z⟩| ≤ ‖h‖_{Ḣ^{-1}}‖∇z‖₂`; the cutoff bound
`‖k‖²_{Ḣ^{-1}} ≤ C‖k‖₁² + ‖k‖₂²` (eq:Rnegative-cutoff); simple-function density
in the Bochner space; the recorded grid inequality
`Σ_C |C||(A_hz)_C|² ≤ ‖z‖₂²`.

**Genuinely absent objects:**

1. `⟪D01:Lambda⟫ = (−Δ)^{1/2}` and `⟪D01:J⟫ = (I−Δ)^{1/2}` as *operators*.
   Section 4 uses them only inside quantities — `‖Λ^{1/2}u‖₂ = ‖u‖_{Ḣ^{1/2}}`,
   `‖Λ^{3/2}u‖₂ = ‖u‖_{Ḣ^{3/2}}`, `‖Ju‖_{H^s} = ‖u‖_{H^{s+1}}` — all of which
   `homogeneousFourierENorm` and `sobolevENorm` already express.  The operators
   themselves are needed by the *testing* arguments of prop:Rcritical1/2 and by
   Lemma A.1, i.e. by A03/A05/R43/R44, which should own them.
2. `⟪D01:Leray⟫`, the projection with symbol `I − ξ⊗ξ/|ξ|²`, and the projected
   equation eq:projected.  Deliberately omitted: no Section 4 *statement* uses
   it (eq:Rpressure is derivable from `momentum` + `divergence` + `∇p ∈ L²`,
   unit L9), and the only in-tree construction is HeliCorgi's, blocked on U05.
   It is a prerequisite of R43/R44's energy arguments, not of the data layer.
3. `⟪D01:IsMaximalSolution⟫` and the *mild* formulation eq:mild and the
   continuation criterion eq:criterion.  `maximalLifespanR` is a supremum of
   horizons, not a chosen maximal solution; identifying the two needs local
   uniqueness (A02) and the heat semigroup (A01/A04).  Putting a "maximal
   solution" structure here would either be vacuous or would smuggle in
   prop:local.
4. `⟪D01:V⟫ = H¹(R³;R³) ∩ L²_σ` and `V'`.  `04:202-206` calls these
   "documentation of the intended pairing only"; no Section 4 statement
   quantifies over them.
5. *(Closed after review — was listed here as not covered.)* Physical-field
   `L^q_t Ḣ^s_x` and prop:Renergy's `L²(0,∞;Ḣ^{-1})` clause are now defined:
   `IsSliceDistribution` reads a physical slice as a tempered vector
   distribution, `IsHomogeneousVectorDatum` / `IsHomogeneousSliceDatum` /
   `IsHomogeneousPath` carry the homogeneous datum along a trajectory, and
   `forceHomogeneousENorm` is the measurable-path Bochner norm.  No `L² → 𝓢'`
   homogeneous multiplier is needed — the bridge goes through the Schwartz
   pairing that `IsSobolevDatum` already uses, so no new Parseval convention is
   introduced.  What remains genuinely absent is the *scalar* physical
   `Ḣ^s`-norm identity relating `forceHomogeneousENorm` to
   `homogeneousFourierENorm` on smooth compact profiles, which is unit L8.
6. The Fréchet topology on `H^∞` (§8.2, `02-prelim:15`).  eq:Rinitial fixes
   only the set, thm:Rmain fixes `a` and never topologizes `X_R`.  Both drafts
   omitted it and both reviews ratified the omission.
7. `⟪G01:faceSet⟫` (closed, locally finite union of planes, measure zero).
   This is G01's, and `Paper3.GridGeometry.finite_grids_common_interior`
   (`:40`) / `finite_grids_common_ball` (`:69`) already supply what thm:Rgrid's
   proof needs from it.
8. `⟪D01:normLp p⟫` for `p ∈ {1,2,3,6}` as new declarations.  These are
   Mathlib's `eLpNorm _ p volume` with no manuscript-specific convention;
   `mixedLebesgueENorm ⊤ p` and `mixedLebesgueENorm q p` cover the mixed forms,
   and the purely spatial ones need no definition.
9. §8.8 packet data (`⟪I01:…⟫`) and §8.10 exponent arithmetic.  The former is
   I01's; the latter is frozen in `Contracts/V1/Thresholds.lean`, and
   `scalingExponent` here is stated so a binding can identify the two.

**Known residual risks carried forward, not defects of this contract:**
`maximalLifespanR` is `0` for data with no solution at all, so 4.1(i) stays
provable-but-vacuous until prop:local lands (A01/A04); `IsSobolevDatum`'s
right-hand integral is Lean-totalized for a slice that is not locally
integrable, which the `m = 0` clause of `MemForceR`/`MemHInfty` excludes but
which a bare use of `IsSobolevDatum` does not; and `homogeneousFourierENorm`
is faithful only on `L¹ ∩ L²` slices, as its docstring says.

---

## 5. Revisions after `REVIEW_RECONCILIATION.md`

The reviewer accepted `Data.lean` with notes and accepted the six-module local
allowlist while asking for the vendor half to be narrowed.  Every ranked issue
is addressed below; line numbers throughout this file are the revised ones.

| # | Sev | Reviewer's point | What changed |
|---|---|---|---|
| 1 | moderate | `CompletedDense`'s approximating path `D` carried no measurability, re-introducing the lower-integral gap on the other side of the quantifier | `CompletedDenseVia` (`:725`) now requires `AEStronglyMeasurable D forceTimeMeasure`, matching `forceSobolevENorm` |
| 2 | moderate | prop:Renergy's `L²(0,∞;Ḣ^{-1})` clause was not statable | added `IsSliceDistribution` (`:298`), `IsHomogeneousVectorDatum` (`:355`), `IsHomogeneousSliceDatum` (`:364`), `IsHomogeneousPath` (`:372`), `forceHomogeneousENorm` (`:387`); `CompletedDenseVia` is parametric in the realization, with `CompletedDense` (`:736`) and `CompletedDenseHomogeneous` (`:745`) as its two instances. §4 item 5 is closed |
| 3 | minor | `E_T` applies `eLpNorm`/`∫⁻` with no measurability, contradicting the blanket "no lower Lebesgue integral" claim in the module docstring | the module docstring's Totalization bullet now names the two remaining totalized places and why they cannot bite (every field Section 4 applies them to is smooth); `energyEssSup`, `energyGradient` and `energyENorm` carry the caveat, and `energyENorm` records that `T ≤ 0` gives `0` |
| 4 | minor | `IsSobolevDatum`'s totalized right-hand side admits a junk `0` for a slice that pairs integrably with no Schwartz test | recorded in both the `IsSobolevDatum` and the `sobolevENorm` docstrings, with the reason it is unreachable from `MemHInfty` / `MemForceR`; no side condition added, to keep the shape of `angularRealVectorSlice_pairing` |
| 5 | minor | a datum is demanded at every `t ≥ 0`, while the paper identifies slices a.e. | recorded in the `IsSobolevPath` docstring, covering `IsLebesgueSlicePath` and `IsHomogeneousPath` too |
| 6 | minor | the `Integrable` clause note claimed the range `-3/2 < s < 3/2` | reworded: the clause constrains only `2s < 3`; for `s ≤ 0` the integrand is integrable at every `s`, and the lower bound belongs to injectivity / no-polynomial-ambiguity, i.e. to unit L7 |
| 7 | cosmetic | `breakdownSetRZero` cited the torus line `02-prelim:41` | now cites `04:11` thm:Rmain (ii) and `02-prelim:42`, noting the torus symbol is a different set |
| 8 | cosmetic | the dependency table listed `RealSobolevHilbert` as used in code and claimed `NavierStokesR3.*` is an allowed package | both rows corrected, in `Data.lean` and in §2 here; the vendor half is now one exact module |
| 9 | cosmetic | closure counts | §2 now says 51 modules / 7161 LOC, of which 35 local (3795 LOC) and 16 vendor |

Reviewer recommendations on the policy gate, all applied: the `NavierStokes.`
prefix is replaced by the exact entry `NavierStokes.R3.ProblemStatement` inside
`CONTRACT_CANONICAL_MODULES`; `Mathlib` / `Lean` / `Init` are matched exactly or
with a dot, so `MathlibExtras.X` and `Initialize.X` no longer pass; the comment
states that the list governs direct imports, not the closure; and
`test_contract_policy.py` gained two end-to-end cases that drive `check()` over
a throwaway tree (one rejected non-allowlisted local import whose message must
name the module, one accepted canonical import).

Infrastructure, per the reviewer's bookkeeping note: `verification/lakefile.toml`
now has `defaultTargets = ["Tests", "Contracts"]`, so a bare `lake build`
elaborates `Contracts.V1.Data` even when the file is unchanged; `testDriver`
is untouched.  The Paper-to-Lean table and the attempts log moved out of the
generated task card into `research/D01/PAPER_TO_LEAN.md` and
`research/D01/ATTEMPTS.md`, and `python3 experiments/tasks.py render` restored
`collaboration/tasks/D01.md` to its generated form.
