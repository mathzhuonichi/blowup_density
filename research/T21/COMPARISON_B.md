# T21 draft B — clause table, choices, ambiguities, lemma list, implementation candidates

Lane `411-SPEC-t21-draft-b`.  Statement-only draft of `cor:nondensity` and
`thm:main` (i)+(ii) for `paper/sections/03-torus.tex`.
File: `research/T21/DraftB.lean` (1406 lines; elaborates with 0 errors).

Vocabulary policy: registered contracts imported and used by name; the T19
density package, the T12 membership/derivative vocabulary and the T20
`CriticalRegularityTAPI` copied verbatim in delimited blocks (sources and the
one deliberate re-basing are in the module docstring of `DraftB.lean`).

---

## 1. `cor:nondensity` (`03-torus.tex:506-509`, proof `:510-520`)

| paper clause | line | Lean field / object in `DraftB.lean` | Section 4 counterpart |
|---|---|---|---|
| there is `c>0` (the `prop:critical` constant) | `:384` | `NonDensityAPI.hc` (index `c` + this field) | torus-only as a *field*; on `R³` the constant is hidden inside `R43.criticalConst` and never appears in `MainThresholdsAPI` |
| `g∈𝓕`, `ρ=‖g‖_{L¹(0,∞;H^{1/2})}<cν ⟹ T_max^ν(0,g)=∞` | `:385-389` | `NonDensityAPI.criticalGlobalRegularity` (verbatim `CriticalRegularityTAPI.globalRegularity`) | torus-only in the registry; the `R³` analogue is the implementation lemma `R43.inhomogeneousAtZero_of_memForceR` |
| the set `{g∈𝓕 : ‖g‖_{L¹_tH^{1/2}_x}<cν}` | `:511-514` | `def criticalBallT c ν (1/2)` | no registered counterpart — `R41` never names the ball, it uses the radius form `criticalRadius_le_forceSobolevENorm` |
| "is a nonempty … ball, containing zero" | `:515` | `NonDensityAPI.zeroMemBall` | implementation `R41.zero_mem_forceClassR` (`A04.memForceR_zero`) |
| "relative **open** ball" | `:515` | `NonDensityAPI.ballRelativelyOpen` | torus-only; `R41` never states openness (it contraposes density at the single centre `0`) |
| "disjoint from `𝓑⁰_{ν,T}` by `prop:critical`" (at `s=1/2`) | `:515-516` | `NonDensityAPI.criticalBallDisjoint` | `R41.criticalRadius_le_forceSobolevENorm` at `s=1/2` (radius spelling of the same fact) |
| "the Fourier weights imply …" — coefficient mechanism | `:517` | `NonDensityAPI.reweightContraction` (uses the registered `IsPeriodicReweight`) | `R41.angularOrderLowering_norm_le` + `R41.lowerVectorL_norm_le` (continuous-frequency analogue) |
| `‖g(t)‖_{H^{1/2}} ≤ ‖g(t)‖_{H^s}` for `s≥1/2` | `:517-518` | `NonDensityAPI.sliceSobolevMonotone` | torus implementation already exists: `Paper1.PeriodicCriticalRegularity.periodicVectorSobolevNorm_mono` |
| the same for the time-integrated norm | `:519` | `NonDensityAPI.forceSobolevMonotone` | `R41.forceSobolevENorm_mono_order`; torus implementation `Paper1.PeriodicCriticalRegularity.forceDistance_order_mono` |
| "the ball `‖g‖_{L¹_tH^s_x}<cν` is therefore also disjoint" | `:519` | `NonDensityAPI.ballDisjoint` | same `R41` theorem instantiated with `1/2 ≤ s` |
| "a dense subset cannot miss a nonempty open set" | `:519` | **not a field** — it is `RelativelyDenseT` unfolded at `g=0`, `r=ofReal (cν)`, so a field would be a tautology.  It is the proof of `NonDensityAPI.nonDensity` | last three lines of `R41.not_breakdownDenseR_zero_L1` |
| the corollary itself | `:507-508` | `NonDensityAPI.nonDensity`, and `def nonDensityStatement` in the paper's order | `R41.not_breakdownDenseR_zero_L1` / `not_breakdownDenseR_zero_of_q` |

`Disjoint (criticalBallT c ν s) (breakdownSetTZero ν T)` is pointwise
equivalent to `R41`'s radius spelling `∀ f ∈ 𝓑⁰, ENNReal.ofReal (c*ν) ≤
‖f‖_{L¹_tH^s}`, because both sets are relative to `𝓕`.  The paper writes
"disjoint", so `Disjoint` is the rendering chosen here.

## 2. `thm:main` (`03-torus.tex:6-16`, proof `:522-524`)

| paper clause | line | Lean field / object | Section 4 counterpart (`04-whole-space.tex`, `Contracts/V1/MainThresholds.lean`) |
|---|---|---|---|
| "Equip `𝓕` with its relative `L¹(0,∞;H^s(𝕋))` norm topology" | `:7` | encoded in every density field as `RelativelyDenseT 1 s forceClassT …`; the `example` after `criticalBallT` unfolds it to the `ε` form | `MainThresholdsAPI` carries `∀ q : ℝ≥0∞, (q = 1 ∨ q = 2)`; **the torus fixes `q = 1`** |
| threshold `1/2` | `:9,13` | `MainTheoremAPI.thresholdValue : criticalOrder 1 = 1/2` | `MainThresholdsAPI.thresholdValues` — a *conjunction* of two values (`criticalOrder 1 = 1/2`, `criticalOrder 2 = -1/2`); the torus has no second conjunct |
| "for zero initial velocity" (the datum `0` is admissible) | `:10` | `MainTheoremAPI.zeroInitialClass` | torus-only as a field; `Data.breakdownSetRZero`'s own docstring records that `𝓑⁰_{ν,T}` is the *torus* symbol |
| **(i)** `∀ a∈𝓧`, `𝓑_{ν,a,T}` dense if `s<1/2` | `:9` | `MainTheoremAPI.fixedInitialDensity` | `MainThresholdsAPI.fixedInitialDensity` (same shape, with `q` and `criticalOrder q.toReal`) |
| **(ii)** `𝓑⁰_{ν,T}` dense `⟺ s<1/2` | `:10-14` | `MainTheoremAPI.zeroInitialDensityIff` | `MainThresholdsAPI.zeroInitialDensityIff` (identical shape) |
| "Corollary `cor:nondensity` gives non-density … These are the two assertions of the theorem" | `:523` | `MainTheoremAPI.zeroInitialNonDensity` | torus-only as a field; `R41` keeps only the biconditional |
| "Around every reference regular through `T` … singularity exactly at `T` … `E_T`" | `04-whole-space.tex:13` only | **absent from `thm:main`** — on the torus this content is `cor:closure` (`:540-561`), i.e. `BlowupDensity.T19.StrongClosureAPI` in the copied block | `MainThresholdsAPI.regularReferenceApproximation` |
| "The converse has been proved for zero initial velocity. The behavior for general nonzero initial velocities … remains outside this classification" | `:525` | not formalized: it states what is *not* proved | `04-whole-space.tex:17` has the analogous remark about `q=2` |

### Where the torus differs from Section 4, exactly

1. **One critical exponent, `q = 1` only.**  `s_q = 2/q-3/2` collapses to
   `criticalOrder 1 = 1/2`; `SECTION3_PLAN.md` §4.  Every density field here
   writes the literal `1/2` (as `03-torus.tex:9,13` does) and
   `MainTheoremAPI.thresholdValue` ties it to the registered `criticalOrder`.
2. **No regular-reference rider in `thm:main`.**  See the table row.
3. **Non-density goes through an explicit ball of radius `cν`.**  The torus
   proof `:511-519` is entirely `prop:critical` + Fourier-weight monotonicity;
   `R41`'s `q = 2` converse additionally needs a radius depending on `T`
   (`04-whole-space.tex:17`), which has no torus counterpart.
4. **The smallness constant is absolute.**  `:384` "depending only on the unit
   torus and the stated norm conventions"; Prop. 4.4's `r_{ν,S}` depends on
   `S`.  This is why `c` can be a single structure index here.

## 3. Choices

* **`NonDensityAPI` is `Prop`-valued and indexed by `c : ℝ`.**
  `cor:nondensity` (`:506-508`) introduces no constant; the only constant in
  its proof is `prop:critical`'s.  Making `c` an index (rather than a `Type`
  field) keeps the structure a `Prop` and lets `nonDensityOfCritical : ∀ K :
  CriticalRegularityTAPI, NonDensityAPI K.c` be the literal statement "the
  corollary follows from the proposition".  The index is prevented from being
  an arbitrary real by the two fields `hc` and `criticalGlobalRegularity`,
  which are verbatim `CriticalRegularityTAPI.hc` / `.globalRegularity`.
* **`MainTheoremAPI` is `Prop`-valued**, following `research/T19/Spec.lean`
  and T24 (data-free results), diverging from the `Type`-valued registry
  convention of `MainThresholdsAPI` / `CompletedDensityAPI`.  **Owner
  question** — the same one T19's reconciliation raised.
* **(ii) is a single biconditional**, the `R41` convention, so both directions
  sit under identical hypotheses and `s = 1/2` is covered.  The non-density
  half is *also* kept as its own field, because `:523` names it as one of "the
  two assertions of the theorem" and because that is the field a consumer
  inherits from `NonDensityAPI.nonDensity`.
* **Openness is the `ε`-form, not a `TopologicalSpace` instance.**  There is no
  topology on `forceClassT` in the contract layer; `RelativelyDenseT` is
  already the `ε` form.  `ballRelativelyOpen` is stated in the same idiom.
  This is not a weakening: `Paper1/ManuscriptTopology.lean` builds the actual
  `MetricSpace`/`relativeTopology` on the smooth periodic force class and
  proves `denseAt_iff_approximation`, i.e. that topological density *is* the
  `ε` form.
* **`breakdownSetTZero` is defined locally.**  `Contracts/V1/Data.lean`
  registers `breakdownSetRZero` for `R³` and its docstring says explicitly
  that `𝓑⁰_{ν,T}` is the torus symbol; no torus zero-datum set is registered
  yet, so the draft adds `breakdownSetTZero ν T := breakdownSetT ν (fun _ ↦ 0)
  T` with an `example` checking the registered `R³` def has the same shape.
* **`criticalBallT` is parameterized by the order `s`**, so the `s = 1/2` ball
  of `:513` and the `s ≥ 1/2` ball of `:519` are one object.
* **The monotonicity clause is split into three fields** (coefficient
  contraction `:517`, physical slice `:517-518`, `L¹_t` norm `:519`).  The
  paper writes one sentence but the three are genuinely different statements —
  the last is an inequality between infima over *strongly measurable paths*.
* **The four T19 structures are copied whole**, though only
  `PeriodicDensityAPI` is consumed; copying rather than excerpting keeps the
  T13 copy policy literal and makes it impossible for a field here to
  re-invent one of them.

## 4. Ambiguities (for the reconciliation)

1. **`Prop` vs `Type` for `MainTheoremAPI`** — see Choices.  A `Type`-valued
   version would match the registry but would carry no data field.
2. **Quantifier position of `ν`, `T`.**  `thm:main` fixes `ν,T>0` in
   `02-preliminaries.tex:38` and never re-binds them; T19's
   `PeriodicDensityAPI.fixedInitialDensity` binds `a` first, then `ν,T`.  This
   draft binds `ν,T` first everywhere (the paper's reading), so the two differ
   by binder position only.  Draft A may have chosen T19's order.
3. **Keeping `zeroInitialNonDensity` alongside the biconditional.**  It is
   logically redundant (contrapositive of one direction).  Defensible both
   ways; `:523` is the argument for keeping it.
4. **`Disjoint` vs the radius spelling** of the ball/breakdown separation.
   Equivalent; the paper says "disjoint".
5. **Unconditional monotonicity fields.**  `sliceSobolevMonotone` /
   `forceSobolevMonotone` are stated for *every* field, with no smoothness or
   integrability hypothesis, because both sides are `⨅`-with-`⊤` extended
   norms, so the inequality is true and strictly stronger.  The paper states
   it only for `g(t)`, `g∈𝓕`.  An alternative draft may have added
   `g ∈ forceClassT`.
6. **`s` unrestricted below `1/2` in clause (ii)'s biconditional.**  The paper
   does not restrict `s` in (ii); negative orders are included and are
   harmless on the torus (`SECTION3_PLAN.md` §4: "negative orders trivial").
7. **The `:525` scope remark** is deliberately not a field.  If the owner
   wants it recorded, the natural shape is a comment, not a `Prop`.

## 5. Needs a lemma (what the T21 *proof* lane will consume)

From the copied/registered inputs:

* `BlowupDensity.T19.PeriodicDensityAPI.fixedInitialDensity` — clause (i) and
  the `⟸` half of (ii) (at `a = 0`, via `MainTheoremAPI.zeroInitialClass`).
* `BlowupDensity.T20.Spec.CriticalRegularityTAPI.{c, hc, globalRegularity}` —
  and **nothing else** from T20.  The other 17 fields are the internal
  estimates of `prop:critical`.
* T11 is **not** consumed directly: `maximalLifespanT` is used only through
  `globalRegularity`'s conclusion `= ⊤` and through `breakdownSetT`'s `≤
  ofReal T`.  The contradiction is `ENNReal.ofReal T ≠ ⊤`.

New lemmas the proof lane must supply (none of these exist on the torus side
of the registry today):

1. **`0 ∈ forceClassT`** — `MemForceT 0`: `ContDiff`, `IsPeriodicOn univ`, and
   a compact `K ⊆ Ioi 0` with `tsupport 0 = ∅ ⊆ K ×ˢ univ`.  Mirror of
   `A04.memForceR_zero`.
2. **`forceSobolevENormT q s 0 = 0`** — already proved:
   `NSFormalization.Section3.T19.torusForceSobolevENorm_zero`
   (`formalization/NSFormalization/Section3/T19/Bookkeeping.lean`).  Together
   with (1) this is `zeroMemBall`.
3. **`0 ∈ initialClassT`** — smooth, periodic, `IsSolenoidal` (which is
   `∀ x, spatialDivergence (lift 0) 0 x = 0`).
4. **Weight contraction on data** (`reweightContraction`): for `s ≤ t`,
   `periodicFrequencyWeight k ^ ((s-t)/2) ≤ 1` because
   `periodicFrequencyWeight k = 1 + 4π²|k|² ≥ 1`; then componentwise `ℓ²`
   domination in `PeriodicVectorData = WithLp 2 (Fin 3 → lp 2)`.
5. **Slice monotonicity** (`sliceSobolevMonotone`): from (4), by mapping a
   representing datum at order `t` to one at order `s` and taking `⨅`.  Needs
   the reweighted datum to stay in `realPeriodicSubmodule` (the weights are
   real and even, so conjugate reflection survives).
6. **Path monotonicity** (`forceSobolevMonotone`): the reweighting map is a
   *bounded linear* map `PeriodicSobolev t → PeriodicSobolev s` of operator
   norm `≤ 1`, hence continuous, hence preserves
   `AEStronglyMeasurable`; then `eLpNorm_mono`.  This is exactly the shape of
   `R41.forceSobolevENorm_mono_order` (whose proof is 12 lines given
   `lowerVectorL` as a `ContinuousLinearMap`), so the torus lane needs a
   coefficient-side `lowerVectorLT : PeriodicSobolev t →L[ℝ] PeriodicSobolev s`.
7. **Triangle inequality for `forceSobolevENormT 1 s`** (`ballRelativelyOpen`):
   `IsPeriodicDatum` is additive in `(z, A)` jointly, so the sum of two
   representing paths represents the sum; then `eLpNorm_add_le`.  Torus
   analogue of `Paper1.PeriodicForceTopology.forceDistance_triangle`.
8. **`ENNReal` bookkeeping** for `ballRelativelyOpen`: the radius is
   `ENNReal.ofReal (c*ν) - forceSobolevENormT 1 s g`, positive because the
   subtrahend is `< ofReal (c*ν) < ⊤`.

### How `L¹_t H^s` is spelled in `TorusLocalTheory`

`Contracts/V1/TorusLocalTheory.lean:89`

```
forceSobolevENormT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → PeriodicSobolev s //
      IsPeriodicSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure
```

with `IsPeriodicSobolevPath s f G := ∀ t, 0 ≤ t → IsPeriodicDatum s (f(t,·)) (G t)`
and `forceTimeMeasure = volume.restrict (Ioi 0)` (`Contracts/V1/Data.lean:118`,
`01-introduction.tex:140`).  So `‖g‖_{L¹_tH^{1/2}_x}` is
`forceSobolevENormT 1 (1/2) g`, which is definitionally
`BlowupDensity.T20.Spec.criticalRho g` — checked by an `example … := rfl` in
`DraftB.lean`.  Consequences: the norm is `⊤` when no strongly measurable
representing path exists (fail-safe, no junk zero), and monotonicity in `s`
must move a whole path, not one datum.

## 6. Implementation candidates

**Section 4 template (`R41` non-density), `formalization/NSFormalization/Section4/R41/`:**

| declaration | file:line | what it gives T21 |
|---|---|---|
| `angularOrderLowering_norm_le` | `NonDensityL1.lean:16` | the order-lowering contraction (continuous-frequency model of `reweightContraction`) |
| `lowerVectorL_norm_le` | `NonDensityL1.lean:30` | componentwise version |
| `forceSobolevENorm_mono_order` | `NonDensityL1.lean:42` | **the exact proof skeleton** for `forceSobolevMonotone` (`le_iInf`, transport the path by a `ContinuousLinearMap`, `eLpNorm_mono`) |
| `criticalRadius_le_forceSobolevENorm` | `NonDensityL1.lean:82` | the ball/breakdown separation, radius spelling |
| `zero_mem_forceClassR` | `NonDensityL1.lean:101` | `0` is in the ambient class |
| `not_breakdownDenseR_zero_L1` | `NonDensityL1.lean:105` | the whole `nonDensity` argument, 6 lines |
| `RMainThresholds`, `nonDensityZero_of_q`, `not_breakdownDenseR_zero_of_q`, `RMainNonDensity` | `NonDensity.lean:25,49,73,93` | the `q`-indexed assembly; on the torus only the `q=1` branch survives |

**Torus assets already in `formalization/NSFormalization/Paper1/` (the modules
named in the T21 row of `SECTION3_PLAN.md`):**

| declaration | file:line | what it gives T21 |
|---|---|---|
| `periodicVectorSobolevNorm_mono` | `PeriodicCriticalRegularity.lean:33` | slice monotonicity, already proved on the torus (weaker `TestForce` vocabulary) |
| `forceDistance_order_mono` | `PeriodicCriticalRegularity.lean:47` | `L¹_t` monotonicity, already proved on the torus |
| `CriticalRegularityCertificate` / `exists_critical_regularity_constant` | `PeriodicCriticalRegularity.lean:63,72` | the `c`/`hc`/`globalRegularity` triple in Paper1 spelling — the exact index of `NonDensityAPI` |
| `critical_regular_ball` | `PeriodicCriticalRegularity.lean:81` | `cor:nondensity` as `GaugeSeparated`, already proved from the certificate |
| `paper1_main_with_critical_interfaces` | `PeriodicCriticalRegularity.lean:99` | `thm:main` (i)+(ii) already assembled, conditional on the certificate and `UnforcedLocalExistence` |
| `GaugeSeparated`, `not_GaugeDense_of_GaugeSeparated`, `zero_slice_GaugeDense_iff_subcritical`, `paper1_main` | `PeriodicMain.lean:26,32,44,59` | the ball ⇒ non-density ⇒ biconditional chain, purely order-theoretic |
| `forceDistance_triangle`, `forceDistance_mono` | `PeriodicForceTopology.lean:123,112` | triangle inequality for `ballRelativelyOpen` |
| `forceMetric`, `relativeTopology`, `DenseAt`, `denseAt_iff_approximation`, `not_denseAt_of_regular_ball`, `zero_slice_nondense_of_regular_ball` | `ManuscriptTopology.lean:150,156,161,176,201,217` | the genuine relative-topology object and the proof that topological density = the `ε` form used by `RelativelyDenseT` |
| `singularSlice`, `GaugeDense` | `PeriodicDense.lean:29,41` | the `𝓑_{ν,a,T}` / density pair in Paper1 spelling |

The gap between these assets and the draft is **vocabulary, not mathematics**:
Paper1 works with `TestForce` + `forceDistance` + `lifespan`, the contracts
with `forceClassT` + `forceSobolevENormT` + `maximalLifespanT`.  Bridging is
the same job `Bindings.TorusLocalTheory` already does for T10/T11.

**Canonical vs registered spellings (measured, not assumed).**  Probe file
`/tmp/t21drift.lean` (`lake env lean`, imports `Contracts.V1.TorusLocalTheory`
and `NSFormalization.Section3.T20.CriticalRegularity`):

* `Contracts.V1.TorusLocalTheory.forceSobolevENormT = NSFormalization.Section3.T10.forceSobolevENormT` — `rfl` **accepted**;
* `… .forceClassT = NSFormalization.Section3.T10.forceClassT` — `rfl` **accepted**;
* `… .maximalLifespanT = NSFormalization.Section3.T10.maximalLifespanT` — `rfl` **rejected** (type mismatch), because `ClassicalSolutionT` is a distinct inductive on the two sides (`CLAUDE.md` structure exception).

Consequence for the proof lane: `criticalRho` and the whole ball vocabulary
transfer definitionally between the canonical and registered sides; the single
field that does not is `globalRegularity`'s conclusion, which must go through
the fieldwise `ClassicalSolutionT` conversion in `Bindings.TorusLocalTheory`.
