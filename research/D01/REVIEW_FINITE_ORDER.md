# REVIEW — lane 125 (D01 · C1b-m-D, finite-order datum constructor, split-and-start)

Reviewer run 2026-09-13 on branch `erenup/125-D01-finite-order-datum`, one commit `d2d838b` on top of
merge-base `82bcfde` with `origin/erenup/integration`.  Probes in `/tmp/rev125/` (contents quoted
below, per `logs/LESSONS.md` on volatile probe paths).

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct, compiles, is axiom-clean and hygienic; every exported statement says what the
lane claims it says, and the order-raising step is non-vacuous (the reviewer ran it on a concrete
field and pinned the result with `isSobolevDatum_unique`).  The notes are about the **split table**,
not the code: row **D-b**'s "not in tree / M–L" classification is too pessimistic — the reviewer
proved the whole of D-b **in the cycles variable, with no smoothness**, in one 70-line probe from
in-tree lemmas, and proved the smoothness-free derivative-datum lemma (the Schwartz-duality route)
in 10 lines.  D-b is an **M**, and the table is missing one row (the weak-derivative pairing the
Euler side must deliver).  None of this blocks the merge.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.FiniteOrderDatum
Build completed successfully (9928 jobs).
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean
(silent, exit 0, 0 bytes of output)
$ LEAN_NUM_THREADS=6 lake env lean ../research/D01/axioms_finite_order.lean
'…sqrt_one_add_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'…norm_sobolevBesselWeight_one'      … [propext, Classical.choice, Quot.sound]
'…norm_raiseIntegrand_le'            … [propext, Classical.choice, Quot.sound]
'…continuous_sobolevBesselWeight_one'… [propext, Classical.choice, Quot.sound]
'…raisableWitness_of_memLp_smul'     … [propext, Classical.choice, Quot.sound]
'…raise_mem'                         … [propext, Classical.choice, Quot.sound]
'…angularRealization_raiseHilbert'   … [propext, Classical.choice, Quot.sound]
'…isSobolevDatum_raise'              … [propext, Classical.choice, Quot.sound]
$ cd ..; make check         → 13 tests OK; 30 work items consistent
$ LEAN_NUM_THREADS=6 make test
info: Tests/DatumLemmasV3.lean:31:0: Contract …checkedDatumLemmasV3: checked; standard logical axioms only
(all Tests replayed, no failure)
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean
(none)
```

**Finding 1 [note].**  `research/D01/axioms_finite_order.lean` covers 8 of the 11 exports; the three
`def`/`rfl` items `RaisableWitness`, `raiseHilbert`, `coe_raiseHilbert` are not listed.  Harmless
(they are in the closure of the listed theorems) but cheap to add.

**Finding 2 [note].**  The module is **outside the registered test closure** (no `Contracts`/
`Bindings` entry imports it; only `research/D01/axioms_finite_order.lean` does).  CI does build it on
*this* PR, via the `Compile changed modules outside the registered test closure` step
(`experiments/build_changed_lean.py`, `.github/workflows/contracts.yml:77`).  After merge nothing
re-checks it when its dependencies change — the drift mode of `logs/LESSONS.md`'s 068 entry.  The
`axioms_finite_order.lean` sweep should be run by every later D01 lane that touches
`LerayLowering`/`SmoothDatum`/`AngularTameProduct`.

## 2. Statement fidelity and non-vacuity — **PASS** (with one qualification)

### 2a.  Every export, `pp.fullNames` (`/tmp/rev125/p1_check.lean`, exit 0)

```
…D01.sqrt_one_add_normSq_le : ∀ (ξ : Space), √(1 + ‖ξ‖ ^ 2) ≤ 1 + ∑ j, |ξ.ofLp j|
…D01.norm_sobolevBesselWeight_one : ∀ (ξ : Space), ‖Paper3.sobolevBesselWeight 1 ξ‖ = √(1 + ‖ξ‖ ^ 2)
…D01.continuous_sobolevBesselWeight_one : Continuous (Paper3.sobolevBesselWeight 1)
…D01.norm_raiseIntegrand_le : ∀ (h : ↥FourierData) (ξ : Space),
  ‖Paper3.sobolevBesselWeight 1 ξ • ↑↑h ξ‖ ≤ ‖↑↑h ξ‖ + ∑ j, |ξ.ofLp j| * ‖↑↑h ξ‖
…D01.RaisableWitness : ↥FourierData → Prop
…D01.raisableWitness_of_memLp_smul : ∀ (h : ↥FourierData),
  (∀ (j : Fin 3), MemLp (fun ξ => ↑(ξ.ofLp j) • ↑↑h ξ) 2 volume) → RaisableWitness h
@…D01.raise_mem : ∀ {s : ℝ} (a : ↥(RealSobolevHilbert s)) (hg : RaisableWitness ↑a),
  MemLp.toLp (fun ξ => sobolevBesselWeight 1 ξ • ↑↑↑a ξ) hg ∈ realSubspace (s + 1)
@…D01.angularRealization_raiseHilbert : ∀ {s} (a) (hg),
  (angularRealization (s + 1)) ↑(raiseHilbert a hg) = (angularRealization s) ↑a
@…D01.isSobolevDatum_raise : ∀ {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s},
  IsSobolevDatum s z A → ∀ (hg : ∀ i, RaisableWitness ↑(A.ofLp i)),
    IsSobolevDatum (s + 1) z (WithLp.toLp 2 fun i => raiseHilbert (A.ofLp i) ⋯)
```

`RaisableWitness h` unfolds (checked by `Iff.rfl` in the probe) to exactly
`MemLp (fun ξ => sobolevBesselWeight 1 ξ • ⇑h ξ) 2 volume`.  It is an **`L²`-membership hypothesis on
a raw Fourier function**, not a disguised copy of the conclusion: it never mentions `z`,
`IsSobolevDatum`, or `angularRealization`.  `IsSobolevDatum` itself is the frozen contract predicate
verbatim (`Contracts/V1/Data.lean:160` ≡ `SmoothDatum.lean:237`), pairing against Schwartz tests.

**Finding 3 [minor — claim, not code].**  By datum uniqueness the witness is nevertheless
*equivalent* to the conclusion.  Reviewer probe `/tmp/rev125/p10_conv.lean` (compiles, silent) proves
the converse:

```lean
theorem raisableWitness_of_higher {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) {B : RealVectorSobolev (s + 1)}
    (hB : IsSobolevDatum (s + 1) z B) (i : Fin 3) :
    RaisableWitness ((A i : RealSobolevHilbert s) : FourierData)
```

(19 lines: `isSobolevDatum_unique` + `angularOrderLowering_coeFn'` + `sobolevBesselWeight_mul`.)
So `isSobolevDatum_raise` is a faithful **translation** lemma — "the raised raw datum is in `L²`"
⟺ "there is a datum at order `s+1`" — and carries no analysis of its own; all the analysis sits in
`raisableWitness_of_memLp_smul` (the symbol bound, real but small) and in row D-b.  This is what the
module docstring says ("the analytic content is packaged as an explicit witness"), but
`FINITE_ORDER_SPLIT.md` §2 bullet 1 ("The order-raising **mechanism** is now fully in Lean") reads
stronger than it is.  Suggest adding half a sentence: *the mechanism is the realization identity;
the implication itself is an equivalence, so nothing is gained until D-b discharges the witness.*
The companion claim — that **no vector Plancherel isometry is needed** — is verified: no norm
appears anywhere in the proofs, and the reviewer's own runs never needed one.

### 2b.  Non-vacuity — the raise actually fires, and lands on the right datum

`/tmp/rev125/p3_nonvac.lean` (compiles; one deprecation warning on `iteratedFDeriv_zero_fun`):

* `zeroField : SmoothL2Field Space` — a concrete inhabitant of the hypothesis class.
* `witness_smooth (m s) (hs1 : s + 1 ≤ m) (Z : SmoothL2Field Space) (i)` —
  **every** smooth `L²` field satisfies `RaisableWitness` for its order-`s` datum
  `smoothAngularDatum m s _ Z i` (19 lines; not the degenerate zero case).
* `raise_fires` — `IsSobolevDatum (s+1) Z.field (WithLp.toLp 2 fun i => raiseHilbert …)`,
  i.e. `isSobolevDatum_raise` applied to real data.
* `raise_pins` — **the uniqueness pin the brief asks for**:
  `(WithLp.toLp 2 fun i => raiseHilbert (smoothAngularDatum m s _ Z i) …) = smoothAngularDatum m (s+1) hs1 Z`
  by `isSobolevDatum_unique`.  So the raised datum is *the* order-`(s+1)` smooth datum, hence
  consistent with `smoothAngularDatum_isSobolevDatum` and with everything downstream of it
  (`isSobolevDatum_partialDeriv`, whose hypothesis is exactly an order-`(m+1)` datum of `Z.field`).
* the final `example` instantiates all of this at `zeroField` with concrete orders `1 → 2`.

### 2c.  The symbol bound is the right one, in the right direction

`/tmp/rev125/p4_neg.lean` (compiles, exit 0) evaluates it at `ξ = (1,1,1)`:
`‖ξ‖² = 3`, so the left side is `√(1+3) = 2` and the right side is `1 + 3 = 4`; the general lemma
instantiated there is literally `(2 : ℝ) ≤ 4`.  The direction is the one domination needs: the
weight is bounded **above** by `1 + ∑|ξ j|`, and `norm_raiseIntegrand_le` multiplies through by
`‖h ξ‖ ≥ 0`, which is what `MemLp.mono'` consumes in `raisableWitness_of_memLp_smul`.

**Finding 4 [minor — simplification, for the SIMP/tester pass].**  Mathlib already has the `‖ξ‖`
form: `sqrt_one_add_norm_sq_le (x : E) : √(1 + ‖x‖ ^ 2) ≤ 1 + ‖x‖`
(`Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:41`), and the tree already has
`EulerMeanCutoffCurl.norm_le_sum_coordinates (ξ) : ‖ξ‖ ≤ ∑ j, |ξ j|` (found by `exact?`).  The
16-line `nlinarith` proof collapses to three lines (`/tmp/rev125/p6_simp.lean`, compiles, standard
axioms):

```lean
theorem sqrt_one_add_normSq_le' (ξ : Space) : Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 1 + ∑ j : Fin 3, |ξ j| :=
  (sqrt_one_add_norm_sq_le ξ).trans (by gcongr; exact EulerMeanCutoffCurl.norm_le_sum_coordinates ξ)
```

### 2d.  Negative check — the witness is not removable

The witness appears in the conclusion as *data*, so the honest restatement without it is the
existential one.  Two checks:

* natural attempt (`/tmp/rev125/p5_attempts.lean`):
  `⟨_, isSobolevDatum_raise hA (fun i => Lp.memLp _)⟩` →
  ```
  error: Type mismatch
    Lp.memLp ?m.27
  has type   MemLp ↑↑?m.27 ?m.24 ?m.25
  but is expected to have type   RaisableWitness ↑(A.ofLp i)
  ```
  i.e. membership of the datum itself never gives membership of the **weighted** datum.
* **the collapse argument, formalised** (`/tmp/rev125/p4_neg.lean`, compiles):

  ```lean
  theorem free_raise_collapse
      (freeRaise : ∀ {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s},
        IsSobolevDatum s z A → ∃ B : RealVectorSobolev (s + 1), IsSobolevDatum (s + 1) z B)
      {z : Space → Space} (hz : ContDiff ℝ ∞ z) (hL2 : MemLp z 2 volume) :
      MemLp (iteratedFDeriv ℝ 1 z) 2 volume
  ```
  (`orderZeroDatum` seed + `memLp_iteratedFDeriv_of_isSobolevDatum`).  Witness-free raising would
  therefore prove `C^∞ ∩ L² ⊆ H¹`, which is false.  The brief's indicator-of-a-ball counterexample
  is **not** available in tree: `memLp_of_isSobolevDatum` / `memLp_iteratedFDeriv_of_isSobolevDatum`
  (`DatumToJets.lean:267,241`) both assume `ContDiff ℝ ∞ z`, so an indicator cannot be fed to them;
  the collapse above is the valid substitute (it needs only a smooth `L²` field with non-`L²`
  gradient, which is standard and the repo nowhere claims otherwise).

## 3. The table `research/D01/FINITE_ORDER_SPLIT.md` — **two substantive corrections**

All 15 cited `file:line` references were re-opened with `sed -n`: every one is exact
(`OrderZeroDatum.lean:96,103,40`; `SmoothDatum.lean:237,260,278`; `LerayLowering.lean:126`;
`SobolevHilbertModel.lean:24,32`; `DerivativeDatum.lean:69,245`; `DatumToJets.lean:241,267`;
`AngularTameProduct.lean:51`; `RealSobolev.lean:118`).  The DONE rows D-c, D-c′, D-d1-mem,
D-d1-real, D-d1, D-d2, D-book are all really proved at the stated line numbers, sizes plausible.
The lane's own saved probes still compile (`bound_probe2`, `witness_probe`, `raise_probe3`,
`finite_order_probe` — all silent).

**Finding 5 [major — row D-b is misclassified].**  The table says the raw-multiplier a.e. form
"is not in tree" and sizes D-b **M–L**.  Three counter-facts:

1. `Paper3/SobolevDirectionalDerivative.lean:59`
   `sobolevDirectionalDerivative_coeFn (s) (a) (h : SobolevHilbert s) :`
   `⇑(sobolevDirectionalDerivative s a h) =ᵐ[volume] fun ξ => sobolevDirectionalSymbol a ξ * ⇑h ξ`
   **is** the a.e. raw-frequency Fourier identity of the (weak, distributional) derivative — for
   *arbitrary* `L²` data, no smoothness, no integrability — with
   `sobolevDirectionalSymbol (e_j) ξ = 2πi · ξ_j · (1+‖ξ‖²)^{-1/2}` (reviewer `db_symbol`, proved).
2. D01 **already uses it at the coeFn level on data** twice: `Transverse.lean:128-147` and
   `Longitudinal.lean:128-145`; and `Transverse.lean:177 transverse_of_divergence_free` states a
   conclusion with the literal raw `ξ j` in the *angular* variable
   (`∀ᵐ ξ, ∑ j, ↑(ξ j) * ⇑↑(A j) ξ = 0`), i.e. the angular transport the table calls missing is
   worked out in tree at `Transverse.lean:177-205` (dilation + `Measure.map_addHaar_smul`).
3. Reviewer probe `/tmp/rev125/p9_db.lean` (compiles, exit 0) proves **the whole of D-b in the
   cycles (pre-dilation) variable, with no smoothness anywhere**, in ~70 lines:

   ```lean
   theorem db_cycles_full {s : ℝ} (j : Fin 3) {z w : Space → Space}
       {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
       {C : RealVectorSobolev s} (hC : IsSobolevDatum s w C)
       (hw : ∀ (i : Fin 3) (ψ : 𝓢(Space, ℂ)),
         ∫ x, ψ x * ((w x i : ℝ) : ℂ) = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))
       (i : Fin 3) :
       ∀ᵐ ξ ∂volume,
         (2 * (Real.pi : ℂ) * Complex.I) * ((ξ j : ℝ) : ℂ) * ⇑((cyclesToAngular s).symm ↑(A i)) ξ
           = ⇑((cyclesToAngular s).symm ↑(C i)) ξ
   ```
   Route, all in-tree: `isSobolevDatum_partialDeriv_weak` (finding 6) + `Leray.isSobolevDatum_lower`
   + `isSobolevDatum_unique` + `cyclesToAngular_symm_orderLowering` (`AngularTameProduct.lean:44`)
   + `sobolevDirectionalDerivative_coeFn` + `sobolevOrderLowering_coeFn`
   (`Paper3/SobolevOrderLowering.lean:31`), then cancel the nowhere-zero `(1+‖ξ‖²)^{-1/2}`.

   So the accurate wording is: *the **angular-convention transport** of the raw multiplier is not in
   tree; the identity itself is.*  Size **M** (~150 lines total with the transport), not M–L.  For
   the closest Mathlib relatives the table does not mention: `Real.fourierIntegral_deriv` /
   `VectorFourier.fourierIntegral_fderiv` need `Integrable f` **and** `Integrable (fderiv f)` and
   give the identity for the *Bochner* Fourier integral — useless for `L²` weak derivatives; the
   tree's `sobolevDirectionalDerivative` route (multiplier defined by Hölder multiplication, realized
   distributionally) is strictly better and is the one to use.

**Finding 6 [major — a missing row: the Schwartz-duality route].**  The table says
`isSobolevDatum_partialDeriv` is "`SmoothL2Field`-only", and `C1B_SPLIT.md` row C1b-m-D repeats
"so does not apply".  The smoothness is **removable in 10 lines**, because `IsSobolevDatum` is
defined by Schwartz pairing and `∂_a` on tempered distributions is characterised by
`TemperedDistribution.lineDerivOp_apply_apply : (∂_{m} f) g = f (-∂_{m} g)`.  Reviewer probe
(`/tmp/rev125/p8_weakdatum.lean` and `p9_db.lean`, both compile):

```lean
theorem isSobolevDatum_partialDeriv_weak {s : ℝ} {z w : Space → Space} (j : Fin 3)
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A)
    (hw : ∀ (i : Fin 3) (ψ : 𝓢(Space, ℂ)),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ) = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    IsSobolevDatum (s - 1) w
      (WithLp.toLp 2 fun i => angularDirectionalDerivativeReal s (coordinateVector j) (A i)) := by
  intro i ψ
  have hcoe := angularDirectionalDerivativeReal_coe s (coordinateVector j) (A i)
  rw [hcoe, angularRealization_directionalDerivative s (coordinateVector j) ((A i : FourierData)),
    TemperedDistribution.lineDerivOp_apply_apply, hA i (-∂_{coordinateVector j} ψ), hw i ψ]
```

Note for the record: lane 094's `Cut.physical_pairing_zero` (`OrderZeroSymbol.lean:198`) is **not**
this machinery — it is the compact-cutoff integration-by-parts for a *smooth* `L²` field whose
derivative need not be integrable, used to kill a divergence pairing.  The duality route above needs
no cutoff at all, because the integration by parts is the **hypothesis** `hw` (the definition of the
weak derivative), not something to be proved about `z`.

**Finding 7 [minor — the consumer obligation is D-b *plus* one thing].**  Unfolding
`RaisableWitness (A i)` and pushing it through `raisableWitness_of_memLp_smul`, a consumer must
produce, for each `i, j`, `MemLp (fun ξ => (ξ j : ℂ) • (A i : FourierData) ξ) 2 volume` **in the raw
angular variable**.  From "the Euler side descends each derivative word to an ordinary `L²` field"
(row C1b-m-E) that needs three things, not one:

  (i) an order-`s` datum `C j` of the weak derivative `∂ⱼz` (induction hypothesis / `orderZeroDatum`
      seed at `s = 0`) — bookkeeping;
  (ii) **the weak-derivative pairing itself**, `∫ψ·(∂ⱼz)_i = ∫(-∂ⱼψ)·z_i`, for the descended field.
      `word_hasDerivAt` gives *strong `L²` translation derivatives*; converting that to the Schwartz
      pairing is a real (small) obligation currently recorded nowhere.  **Add this as a row
      (`D-euler-pairing`, S–M) to both `FINITE_ORDER_SPLIT.md` and `C1B_SPLIT.md` row C1b-m-E.**
  (iii) D-b in the angular variable.

## 4. Honesty of `ATTEMPTS_FINITE_ORDER.md` — **PASS**

Three of the four recorded failures reproduce verbatim (`/tmp/rev125/p5_attempts.lean`):

```
error: `fun_prop` was unable to prove `Continuous fun ξ => ↑((1 + ‖ξ‖ ^ 2) ^ (1 / 2))`
Issues:  Failed to prove necessary assumption `0 ≤ 1 / 2` when applying theorem `Real.continuous_rpow_const`.

error: Tactic `rewrite` failed: Did not find an occurrence of the pattern  ?x ^ ↑?n
in the target expression  (1 + ‖ξ‖ ^ 2) ^ (1 / 2) = √(1 + ‖ξ‖ ^ 2)        [ATTEMPTS #2, Real.rpow_natCast]

error: Tactic `rewrite` failed: Did not find an occurrence of the pattern  ?a * ?c + ?b * ?c
in the target expression  √(1 + ‖ξ‖ ^ 2) * ‖↑↑h ξ‖ ≤ ‖↑↑h ξ‖ + (∑ i, |ξ.ofLp i|) * ‖↑↑h ξ‖   [ATTEMPTS #4, ← add_mul]
```

matching the recorded text word for word.  The structural claims in ATTEMPTS (`realSubspace` ignores
its order argument; raising is an exact right inverse of lowering; the realization identity does not
need reality) are all consistent with what the reviewer re-derived independently.

## 5. The next D01 lane (answer for the lead)

Close C1b-m-D in one lane, in this order; items 1–2 are already proved in reviewer probes
`/tmp/rev125/p8_weakdatum.lean`, `/tmp/rev125/p9_db.lean` and can be lifted verbatim.

1. **`isSobolevDatum_partialDeriv_weak`** (S, 10 lines, proved) — the smoothness-free derivative
   datum, statement as in finding 6.  Inputs: `angularRealization_directionalDerivative`
   (`DerivativeDatum.lean:69`), `angularDirectionalDerivativeReal_coe`,
   `TemperedDistribution.lineDerivOp_apply_apply` (Mathlib).
2. **`db_cycles_full`** (S–M, 70 lines, proved) — D-b in the cycles variable, statement as in
   finding 5.3.  Inputs: item 1, `Leray.isSobolevDatum_lower` (`LerayLowering.lean:202`),
   `isSobolevDatum_unique` (`ForceClass.lean:286`), `cyclesToAngular_symm_orderLowering`
   (`AngularTameProduct.lean:44`), `sobolevDirectionalDerivative_coeFn`
   (`SobolevDirectionalDerivative.lean:59`), `sobolevOrderLowering_coeFn`
   (`SobolevOrderLowering.lean:31`).
3. **`memLp_coord_smul_datum`** (M, ~50 lines, *the only genuinely new work*) — transport item 2 to
   the raw angular variable and conclude
   `∀ i j, MemLp (fun ξ => (ξ j : ℂ) • ((A i : FourierData) : Space → ℂ) ξ) 2 volume`.
   Recipe, in tree: `transverse_symm_of_divergence_free` → `transverse_of_divergence_free`
   (`Transverse.lean:68-205`) is the same transport for the same expression `ξ_j · (A i)(ξ)`;
   ingredients `angularFrequencyDilation_coeFn` (`AngularFourierDilation.lean:248`),
   `angularWeightEquiv_coeFn` (`AngularSobolevCoordinates.lean:284`),
   `Measure.map_addHaar_smul` + `MeasurePreserving.quasiMeasurePreserving`.
4. **`exists_isSobolevDatum_of_memLp_derivs`** (S given 1–3) — C1b-m-D itself, by induction on `m`:
   order-`0` seed `orderZeroDatum` (`OrderZeroDatum.lean:96`), step
   `raisableWitness_of_memLp_smul` (this lane) → `isSobolevDatum_raise` (this lane).
   Hypothesis shape to expose to the Euler side: `MemLp z 2` plus, for each word up to order `m`,
   an `L²` field `w` **together with** its Schwartz pairing (row `D-euler-pairing`, finding 7).

## 6. Recommended (non-blocking) edits before merge

* `FINITE_ORDER_SPLIT.md` row D-b: replace "the a.e. coeFn form … is not in tree" with "the
  **angular-convention transport** of the in-tree raw multiplier `sobolevDirectionalDerivative_coeFn`
  (`SobolevDirectionalDerivative.lean:59`, smoothness-free) is not in tree"; size **M–L → M**; cite
  `Transverse.lean:177-205` as the worked transport.
* `FINITE_ORDER_SPLIT.md`: add rows **D-b0** (the Schwartz-duality removal of `SmoothL2Field`,
  finding 6) and **D-euler-pairing** (finding 7).
* `FINITE_ORDER_SPLIT.md` §2 bullet 1: qualify "the mechanism is fully in Lean" per finding 3.
* `axioms_finite_order.lean`: add the three missing `#print axioms` (finding 1).
* SIMP pass: three-line `sqrt_one_add_normSq_le` (finding 4).

## 7. Commands run

```
. scripts/lean-env.sh
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.FiniteOrderDatum
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/D01/axioms_finite_order.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/D01/probes/{bound_probe2,witness_probe,raise_probe3,finite_order_probe}.lean
make check ; LEAN_NUM_THREADS=6 make test
cd verification && LEAN_NUM_THREADS=6 lake env lean /tmp/rev125/{p1_check,p3_nonvac,p4_neg,p5_attempts,p6_simp,p8_weakdatum,p9_db,p10_conv}.lean
```

Results: all builds/probes exit 0 except `p5_attempts.lean` (the four deliberate failures above) —
`p1`, `p3`, `p4`, `p6`, `p8`, `p9`, `p10` compile clean; `make check` and `make test` pass.
