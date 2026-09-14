# C1b-m-D — the finite-order datum constructor, sub-lemma split (lane 125)

Row **C1b-m-D** of `research/A01/C1B_SPLIT.md` and the real blocker of A01's carrier bridge:
D01 has an order-`0` datum constructor from a bare `MemLp` field
(`Section4/D01/OrderZeroDatum.lean:96` `orderZeroDatum`, realized by `:103`
`isSobolevDatum_orderZeroDatum`) and an **all-orders** constructor from a `SmoothL2Field`
(`Section4/D01/SmoothDatum.lean:260` `smoothAngularDatum`, realized by `:278`
`smoothAngularDatum_isSobolevDatum`).  There is **nothing in between**: no constructor taking a
field of finite regularity (`MemLp 2` plus `L²` derivatives up to order `m`) to an order-`m` datum.
This table splits that missing constructor and records what lane 125 proved.

## 0. The mathematical shape (what has to happen)

`IsSobolevDatum s z A` (`Contracts/V1/Data.lean:160`, restated `Section4/D01/SmoothDatum.lean:237`)
says `angularRealization s (A i : FourierData) ψ = ∫ ψ · z_i`.  The order-`s` weight
`(1+‖ξ‖²)^{s/2}` lives **inside** `angularRealization s`
(`Paper3/SobolevHilbertModel.lean:24` `sobolevBesselWeight`); the same physical field at order `s`
and at order `s+1` corresponds to two *different* raw-frequency `L²` functions
`A_s(ξ), A_{s+1}(ξ)`, related by

  `angularOrderLowering (s+1) s : A_{s+1} ↦ (1+‖ξ‖²)^{-1/2}·A_{s+1}(ξ) = A_s`

a.e. in the raw frequency variable (`Section4/D01/LerayLowering.lean:126`
`Leray.angularOrderLowering_coeFn'`, the angular convention having absorbed the dilation, so the
multiplier is exactly the ordinary Bessel weight and no `2π` survives).  **Lowering is bounded;
raising is not** — the raised datum `A_{s+1} = (1+‖ξ‖²)^{1/2}·A_s` is in `L²` iff the field has one
more order of regularity.  That single fact is why C1b-m-D is a *real-analysis* gap, not a
normalization question (`C1B_SPLIT.md` §0).

The vector order-`m` Plancherel isometry that `OrderZeroDatum.lean:40-53` records as absent (the
norm identity `‖smoothAngularDatum …‖ = ‖·‖_{H^m}`) is **NOT** needed by the constructor: existence
of the datum `A` at order `s+1` needs only that the raised function lands in `L²`, not a norm
equality.  This is confirmed by the proof of `isSobolevDatum_raise` (row D-d1), which never mentions
a norm.

## 1. Sub-lemma table

Size key: **S** ≤ ~100 lines, no new machinery; **M** self-contained lemma, known proof;
**L** multi-file campaign.  Status: **DONE** = proved and building this lane
(`Section4/D01/FiniteOrderDatum.lean`); **ready** = inputs present, no blocker; **gap** = named
blocker.  Every `file:line` was opened and `#check`ed this lane (probes
`research/D01/probes/finite_order_probe.lean`, `raise_probe{,2,3}.lean`, `bound_probe2.lean`,
`witness_probe.lean`; and the preserved reviewer probes `rev125_*.lean`).

| # | sub-lemma (Lean-ready statement) | size | inputs (file:line, #checked) | status / blocker |
|---|---|---|---|---|
| **D-c** | `Real.sqrt (1+‖ξ‖²) ≤ 1 + ∑ⱼ |ξ j|` (the induction-friendly symbol bound) | S | Mathlib `sqrt_one_add_norm_sq_le` (`√(1+‖x‖²) ≤ 1+‖x‖`); tree `EulerMeanCutoffCurl.norm_le_sum_coordinates` (`‖ξ‖ ≤ ∑ⱼ|ξ j|`) | **DONE** — `FiniteOrderDatum.lean:96` `sqrt_one_add_normSq_le` (3-line `.trans` + `gcongr`, lane-125 review finding 4; the original `nlinarith` on `∑(ξj)² ≤ (∑|ξj|)²` is recorded in `ATTEMPTS_FINITE_ORDER.md`) |
| **D-c′** | `‖sobolevBesselWeight 1 ξ‖ = √(1+‖ξ‖²)`; `‖(1+‖ξ‖²)^{1/2}·w‖ ≤ ‖w‖ + ∑ⱼ|ξ j|·‖w‖` | S | `sobolevBesselWeight` (`SobolevHilbertModel.lean:24`); `Complex.norm_real`; `Real.sqrt_eq_rpow` | **DONE** — `FiniteOrderDatum.lean:81,115` `norm_sobolevBesselWeight_one`, `norm_raiseIntegrand_le` |
| **D-d1-mem** | raised element is in the reality subspace: `RaisableWitness (a:FourierData) → hg.toLp _ ∈ realSubspace (s+1)` | S | `realSymmetry_ae`, `mem_realSubspace_iff` (`Source/RealSobolev.lean`); `MemLp.coeFn_toLp`; `Measure.measurePreserving_neg` | **DONE** — `FiniteOrderDatum.lean:167` `raise_mem` (weight real & even) |
| **D-d1-real** | raised datum realizes the same distribution: `angularRealization (s+1) (raiseHilbert a hg) = angularRealization s a` | S | `Leray.angularOrderLowering_coeFn'` (`LerayLowering.lean:126`); `angularRealization_orderLowering` (`Paper3/AngularTameProduct.lean:51`); `sobolevBesselWeight_mul` (`SobolevHilbertModel.lean:32`) | **DONE** — `FiniteOrderDatum.lean:199` `angularRealization_raiseHilbert` |
| **D-d1** | **the induction step** — `IsSobolevDatum s z A → (∀ i, RaisableWitness (A i)) → IsSobolevDatum (s+1) z (raised A)` | M (S given D-d1-mem/real) | `IsSobolevDatum` (`SmoothDatum.lean:237`); `WithLp.toLp` projection; D-d1-mem, D-d1-real | **DONE** — `FiniteOrderDatum.lean:223` `isSobolevDatum_raise`; the reverse of `isSobolevDatum_partialDeriv` |
| **D-d2** | reduce the witness to coordinate `L²`: `(∀ j, MemLp (ξ ↦ (ξ j)·(A i)(ξ)) 2) → RaisableWitness (A i)` | S | D-c′; `MemLp.mono'`, `MemLp.add`, `MemLp.norm`; `Lp.memLp`; `continuous_sobolevBesselWeight_one` (`:88`) | **DONE** — `FiniteOrderDatum.lean:136` `raisableWitness_of_memLp_smul` |
| **D-schwartz** | **smoothness-free derivative datum** (Schwartz-duality route): `IsSobolevDatum s z A → (weak-deriv pairing of w) → IsSobolevDatum (s-1) w (angularDirectionalDerivativeReal s eⱼ ∘ A)` | S (~10 lines) | `angularRealization_directionalDerivative` (`DerivativeDatum.lean:69`); `angularDirectionalDerivativeReal_coe`; `TemperedDistribution.lineDerivOp_apply_apply` (Mathlib) | **proved (reviewer)** — `research/D01/probes/rev125_partialderiv_weak.lean` `isSobolevDatum_partialDeriv_weak`; removes the `SmoothL2Field` hypothesis of `isSobolevDatum_partialDeriv` (`DerivativeDatum.lean:245`) — the `⟪…⟫` integration by parts is the hypothesis `hw`, not a fact to prove about `z`, so no compact cutoff |
| **D-b** | row D-b **in the cycles (pre-dilation) variable**, no smoothness: `2πi·ξⱼ·((cyclesToAngular s).symm (A i)) =ᵐ (cyclesToAngular s).symm (C i)` (`C` = order-`s` datum of the weak `∂ⱼz`) | **M** (~70 lines) | D-schwartz; `Leray.isSobolevDatum_lower` (`LerayLowering.lean:202`); `isSobolevDatum_unique` (`ForceClass.lean:286`); `cyclesToAngular_symm_orderLowering` (`AngularTameProduct.lean:44`); `sobolevDirectionalDerivative_coeFn` (`SobolevDirectionalDerivative.lean:59`, the smoothness-free raw multiplier — **in tree**); `sobolevOrderLowering_coeFn` (`SobolevOrderLowering.lean:31`) | **proved (reviewer)** — `research/D01/probes/rev125_db_cycles.lean` `db_cycles_full`.  The raw-multiplier a.e. identity **is** in tree (`sobolevDirectionalDerivative_coeFn`, arbitrary `L²`, no smoothness); D01 already uses it at coeFn level (`Transverse.lean:128-147`, `Longitudinal.lean:128-145`) |
| **D-b-transport** | **the only genuinely new work:** transport `db_cycles_full` from the cycles variable to the raw *angular* variable — conclude `∀ i j, MemLp (ξ ↦ (ξ j)·(A i)(ξ)) 2 volume` | **M** (~50 lines) | template `transverse_of_divergence_free`/`transverse_symm_of_divergence_free` (`Transverse.lean:68-205`, same expression `ξⱼ·(A i)(ξ)` in the angular variable); `angularFrequencyDilation_coeFn` (`AngularFourierDilation.lean:248`); `angularWeightEquiv_coeFn` (`AngularSobolevCoordinates.lean:284`); `Measure.map_addHaar_smul` | **DONE (lane 132)** — `FiniteOrderConstructor.lean:memLp_coord_smul_datum`.  The transport collapses to the clean angular a.e. identity `(ξⱼ)·(A i) =ᵐ (frequencyUnit/2πi)·(C j i)`: since `A i = angularFrequencyDilation∘angularWeightEquiv s` of its cycles form and `A i`, `C j i` carry the *same* dilation and Bessel-weight factors, both cancel after substituting `db_cycles_full`; only the dilation Jacobian `frequencyUnit` and `2πi` survive.  No `Transverse`-style symbol juggling was needed.  Feeds `raisableWitness_of_memLp_smul` (D-d2) |
| **D-euler-pairing** | Euler side owes the **Schwartz-pairing form** of its weak derivatives: `∫ψ·(∂ⱼz)_i = ∫(-∂ⱼψ)·z_i` for each descended `L²` word | S–M | C1b-m-E of `C1B_SPLIT.md` (`word_hasDerivAt` gives *strong `L²` translation derivatives*, not the Schwartz pairing directly) | **DONE (lane 140)** — `Section4/A01/EulerPairing.lean:weakDeriv_pairing_of_translation_hasDerivAt`.  Proof: pair both sides against the `L²` inner product through `innerSL`+`compLpL`; move the translation onto `ψ` (`integral_add_right_eq_self`) and differentiate `ψ`'s smooth `L²` orbit (`EulerLpTranslation.smooth_hasFDerivAt`), then `HasDerivAt.unique`.  No smoothness of `z`, no DCT, no cutoff.  Single `maxHeartbeats 400000` (statement size only) |
| **D-euler-coord** | Euler side supplies each `(ξ j)·(A i) ∈ L²` from the descended `L²` derivative words | M | D-euler-pairing + D-b-transport (feed `C j` = datum of the word into `db_cycles_full`, transport, get coordinate `L²`) | **DONE (lanes 132+140)** — `memLp_coord_smul_datum` (lane 132) does the transport; lane 140's `HasWeakDerivsL2`-based route (`weakDeriv_pairing_of_translation_hasDerivAt` → `exists_isSobolevDatum_of_memLp_derivs`) delivers the packaged coordinate-`L²`/datum end-to-end from the cylinder solution (`exists_isSobolevDatum_m_of_cylinder`). |
| **D-e** | finite-order `DatumToJets`: `IsSobolevDatum m z A ∧ ContDiff → MemLp (iteratedFDeriv m z) 2` **without `∀ n`** | M | `memLp_of_isSobolevDatum` (`DatumToJets.lean:267`) is `j=0`; `memLp_iteratedFDeriv_of_isSobolevDatum` (`DatumToJets.lean:241`) already does finite order but **needs `ContDiff ℝ ∞`** | **ready→M** (converse direction; not what C1b-m-D needs, listed for completeness — it is the `⟹`, the constructor is the `⟸`) |
| **D-book** | bookkeeping: `raiseHilbert` coe (`coe_raiseHilbert`), `WithLp.toLp` projection defeq | — | — | **DONE** — `FiniteOrderDatum.lean:191` `coe_raiseHilbert` |
| **D-close** | **C1b-m-D itself**, `exists_isSobolevDatum_of_memLp_derivs`: by induction on `m` — order-`0` seed `orderZeroDatum` (`OrderZeroDatum.lean:96`), step `raisableWitness_of_memLp_smul` (lane 125) → `isSobolevDatum_raise` (lane 125).  Hypothesis to expose to the Euler side: `MemLp z 2` plus, for each word up to order `m`, an `L²` field `w` **with** its Schwartz pairing (row D-euler-pairing) | S (given D-b-transport + D-euler-pairing) | D-euler-coord; `raisableWitness_of_memLp_smul`; `isSobolevDatum_raise` | **DONE (lane 132)** — `FiniteOrderConstructor.lean:exists_isSobolevDatum_of_memLp_derivs`, hypothesis packaged as the predicate `HasWeakDerivsL2 z m` (recursive: `MemLp z 2` + per-`j` `L²` weak derivative with Schwartz pairing, up to order `m`).  Induction on `m` (base `orderZeroDatum`; step applies IH to `z` and each `∂ⱼz`, then `memLp_coord_smul_datum`→`raisableWitness_of_memLp_smul`→`isSobolevDatum_raise`).  `weakDerivs_mono` (order monotonicity), `weakDerivs_smooth` (non-vacuity: every `SmoothL2Field` satisfies it), and the uniqueness-consistency `example` are proved too. |

## 2. Reading of the table

* **The order-raising *machinery* is in Lean** (rows D-c, D-c′, D-d1-mem, D-d1-real, D-d1, D-d2,
  D-book — all DONE this lane).  Given an order-`s` datum of `z` and the `L²` witness that each
  component carries one more order, `isSobolevDatum_raise` produces the order-`(s+1)` datum, needing
  **no** smoothness, **no** compact support, **no** `L¹`, and — the point `OrderZeroDatum.lean:40-53`
  flags — **no vector Plancherel isometry** (no norm appears in the proofs).  *Qualification*
  (lane-125 review finding 3): the *content* of `isSobolevDatum_raise` is the order-lowering
  realization identity; the implication itself is an **equivalence** — by datum uniqueness the
  witness `RaisableWitness (A i)` is equivalent to "`z` has an order-`(s+1)` datum" (reviewer probe
  `research/D01/probes/rev125_converse.lean` `raisableWitness_of_higher`).  So the step is a faithful
  *translation* lemma, not an analytic theorem: **nothing is gained until D-b-transport discharges
  the witness**.  The genuine analysis is the (small) symbol bound (D-c) and row D-b-transport.
* **The remaining work is one M row, not a blocker.**  Row D-b — the raw-frequency Fourier identity
  — is **already in tree** at the coeFn level (`sobolevDirectionalDerivative_coeFn`,
  `SobolevDirectionalDerivative.lean:59`, arbitrary `L²`, smoothness-free) and the reviewer proved
  its full cycles-variable form (`db_cycles_full`) and the smoothness-free datum lemma
  (`isSobolevDatum_partialDeriv_weak`, D-schwartz) from in-tree lemmas; both are preserved as probes
  under `research/D01/probes/`.  The **only genuinely new work** is **D-b-transport** (M, ~50 lines):
  carry `db_cycles_full` from the cycles to the raw *angular* variable, exactly the transport
  `Transverse.lean:177-205` already performs for the same expression `ξⱼ·(A i)(ξ)`.  Then
  `raisableWitness_of_memLp_smul` (D-d2) + `isSobolevDatum_raise` (D-d1) close C1b-m-D by induction
  from `orderZeroDatum` (row D-close), once the Euler side also supplies the weak-derivative Schwartz
  pairing (D-euler-pairing).
* **Lane 132 update: the D01 side is fully closed.**  `Section4/D01/FiniteOrderConstructor.lean`
  promotes `isSobolevDatum_partialDeriv_weak` and `db_cycles_full` into a registered module, proves
  the transport `memLp_coord_smul_datum` (row D-b-transport), and assembles the constructor
  `exists_isSobolevDatum_of_memLp_derivs` (row D-close) by induction on the order, with the
  Euler-facing hypothesis packaged as the predicate `HasWeakDerivsL2`.  Non-vacuity (`weakDerivs_smooth`:
  every `SmoothL2Field` satisfies it to all orders) and the uniqueness-consistency check are proved.
  The transport turned out **simpler than the `Transverse.lean` template**: because `A i` and the
  derivative datum `C j i` share the same dilation and Bessel-weight factors, both cancel after
  substituting `db_cycles_full`, leaving the clean identity `(ξⱼ)·(A i) =ᵐ (frequencyUnit/2πi)·(C j i)`.
  The **only remaining obligation** for C1b-m-D is row D-euler-pairing (the Euler side's Schwartz
  pairing), external to D01.  `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all eight
  new declarations (`research/D01/axioms_finite_order_close.lean`).  Like `FiniteOrderDatum.lean`, the
  module is outside the registered test closure (lane-125 CI note applies: re-run
  `axioms_finite_order_close.lean` when `LerayLowering`/`SmoothDatum`/`AngularTameProduct`/`DerivativeDatum`
  change).
* **Where the vector order-`m` Plancherel isometry would be needed, and why the constructor avoids
  it:** the isometry is needed to *bound the norm* of the constructed datum (row C1b-c8-m of
  `C1B_SPLIT.md`, datum-path continuity/finiteness).  The **constructor** (C1b-m-D, existence of
  `A`) does not touch a norm — `isSobolevDatum_raise` produces `A` and proves it realizes the field
  purely through the order-lowering realization identity.  Confirmed: the proof has no norm term.
* **CI note** (lane-125 review finding 2): `FiniteOrderDatum.lean` is **outside the registered test
  closure** — no `Contracts`/`Bindings` module imports it, only `research/D01/axioms_finite_order.lean`
  does.  CI builds it on *this* PR via `experiments/build_changed_lean.py` (the "compile changed
  modules outside the registered test closure" step), but after merge nothing re-checks it when its
  dependencies (`LerayLowering`/`SmoothDatum`/`AngularTameProduct`) change.  Every later D01 lane that
  touches those should re-run `research/D01/axioms_finite_order.lean` (the drift mode of
  `logs/LESSONS.md`'s 068 entry).

## 3. Proved in Lean this lane

Module `formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean`
(`#print axioms` = `[propext, Classical.choice, Quot.sound]` for all,
`research/D01/axioms_finite_order.lean`):

* `sqrt_one_add_normSq_le`, `norm_sobolevBesselWeight_one`, `norm_raiseIntegrand_le`,
  `continuous_sobolevBesselWeight_one` — row D-c / D-c′.
* `RaisableWitness`, `raisableWitness_of_memLp_smul` — the raising witness and its `L²` assembly
  (row D-d2 reduction).
* `raise_mem`, `raiseHilbert`, `coe_raiseHilbert`, `angularRealization_raiseHilbert`,
  `isSobolevDatum_raise` — the order-raising step (row D-d1, the induction step).

**Also preserved (reviewer probes, `research/D01/probes/rev125_*.lean`, each compiles under
`lake env lean`; not registered modules):** `rev125_partialderiv_weak.lean`
(`isSobolevDatum_partialDeriv_weak`, D-schwartz), `rev125_db_cycles.lean` (`db_cycles_full`, D-b in
the cycles variable), `rev125_nonvac.lean` (non-vacuity: every smooth `L²` field satisfies the
witness, and the raised datum equals `smoothAngularDatum m (s+1)` by uniqueness),
`rev125_collapse.lean` (`free_raise_collapse`: witness-free raising would prove `C^∞∩L² ⊆ H¹`, false;
plus the symbol evaluated at `ξ=(1,1,1)`, `2 ≤ 4`), `rev125_converse.lean` (`raisableWitness_of_higher`,
the equivalence).

## 4. To close C1b-m-D (next lane — reviewer §5 sequence)

Items 1–2 are already proved in the preserved reviewer probes and can be lifted verbatim into a
registered module; item 3 is the only genuinely new work.

1. **`isSobolevDatum_partialDeriv_weak`** (S, ~10 lines, proved — `rev125_partialderiv_weak.lean`):
   the smoothness-free derivative datum.  Inputs `angularRealization_directionalDerivative`
   (`DerivativeDatum.lean:69`), `angularDirectionalDerivativeReal_coe`,
   `TemperedDistribution.lineDerivOp_apply_apply`.
2. **`db_cycles_full`** (S–M, ~70 lines, proved — `rev125_db_cycles.lean`): D-b in the cycles
   variable.  Inputs: item 1, `Leray.isSobolevDatum_lower` (`LerayLowering.lean:202`),
   `isSobolevDatum_unique` (`ForceClass.lean:286`), `cyclesToAngular_symm_orderLowering`
   (`AngularTameProduct.lean:44`), `sobolevDirectionalDerivative_coeFn`
   (`SobolevDirectionalDerivative.lean:59`), `sobolevOrderLowering_coeFn`
   (`SobolevOrderLowering.lean:31`).
3. **`memLp_coord_smul_datum`** (M, ~50 lines, *the only genuinely new work* — row D-b-transport):
   transport item 2 to the raw angular variable, concluding
   `∀ i j, MemLp (fun ξ => (ξ j : ℂ) • ((A i : FourierData) : Space → ℂ) ξ) 2 volume`.  Recipe
   in tree: `transverse_symm_of_divergence_free`/`transverse_of_divergence_free`
   (`Transverse.lean:68-205`, same expression) via `angularFrequencyDilation_coeFn`
   (`AngularFourierDilation.lean:248`), `angularWeightEquiv_coeFn`
   (`AngularSobolevCoordinates.lean:284`), `Measure.map_addHaar_smul`.
4. **`exists_isSobolevDatum_of_memLp_derivs`** (S given 1–3 — row D-close): C1b-m-D itself, by
   induction on `m` — order-`0` seed `orderZeroDatum` (`OrderZeroDatum.lean:96`), step
   `raisableWitness_of_memLp_smul` → `isSobolevDatum_raise` (both this lane).  The hypothesis to
   expose to the Euler side is `MemLp z 2` plus, for each word up to order `m`, an `L²` field `w`
   **together with** its Schwartz pairing (row D-euler-pairing, finding 7).
