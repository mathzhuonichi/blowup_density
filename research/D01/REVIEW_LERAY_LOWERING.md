# REVIEW — lane 085 (D01 · P2 · SL7c): the Leray complement commutes with order lowering

Reviewer run 2026-09-13, worktree `.claude/worktrees/085-D01-p2-sl7c-commute` @ `3553cf6`
(base `120a5bc` = `erenup/integration`).  Diff vs base is exactly three files, 281 added lines,
no deletions, no registry / contract / `paper/` touch.

## Verdict — **ACCEPT-WITH-NOTES**

The Lean is clean, the axioms are the standard three, the commutation is the right *kind* of
statement for SL7c and its proof is non-degenerate.  Two real notes: the ATTEMPTS file asserts
that lane 082's closed form `lowering_mid_symbol_eq` is **not in tree** — it is, at the lane's own
base commit — and as a result `loweringMult` is shipped in a three-factor form that collapses to a
single standard Bessel weight in one rewrite; and the datum-transport corollary the bootstrap
actually needs is the **iff**, which no lemma in tree states (the downward half cited by the worker
is only half of it).  Neither is a mathematical error; both are follow-on work, not a re-do.

---

## 1. Compiles — clean

All five gate commands green; see §5 for verbatim results.  No `sorry` / `admit` / `axiom` /
`native_decide` / `maxHeartbeats` anywhere in the module (the only `grep` hits are the words
`sorry` and `axiom` inside the module docstring at `:41`).  All four declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`.  `lake env lean` on the module prints nothing (0 bytes).
`make check` exit 0; `make test` additionally run and green (the module is not in any contract
closure, so this is a no-op check, recorded for completeness).

## 2. Statement fidelity

### (a) `angularOrderLowering_coeFn` and `loweringMult` — correct, and it agrees with 082

**The worker's claim that 082's `lowering_mid_symbol_eq` "does not exist" is false.**  It is at
`formalization/NSFormalization/Section4/A04/RealPairing.lean:114` (namespace
`NSFormalization.Paper3`), and `git cat-file -e 120a5bc:…/A04/RealPairing.lean` confirms the file
was present in the lane's base tree.  It says

```lean
angularWeightSymbol r ξ * sobolevBesselWeight (r - s) ξ * angularWeightSymbol (-s) ξ
  = sobolevBesselWeight (r - s) (frequencyUnit • ξ)
```

**Independent derivation of the expected multiplier** (from the definitions, not from the lane's
proof).  Write `c = frequencyUnit`, `B_a = sobolevBesselWeight a`, `W_a = angularWeightSymbol a`.
`AngularSobolevCoordinates.lean:13` gives `W_a ξ = B_a (c•ξ) · B_{-a} ξ`; `angularOrderLoweringMid`
(`LaplacianPairing.lean:131`) is `angularWeightEquiv r ∘ sobolevOrderLowering s r ∘ (angularWeightEquiv s)⁻¹`,
so its symbol is
`σ(ξ) = W_r ξ · B_{r-s} ξ · W_{-s} ξ = B_r(cξ)B_{-s}(cξ) · B_{-r}ξ B_{r-s}ξ B_s ξ = B_{r-s}(cξ)`
— exactly `lowering_mid_symbol_eq`.  With `angularOrderLowering = U ∘ Mid ∘ U⁻¹` and
`(U h)(ξ) = c^{-3/2} h(c⁻¹ξ)` (`Transverse.lean:66`),

```
(U Mid U⁻¹ h)(ξ) = c^{-3/2} σ(c⁻¹ξ) (U⁻¹h)(c⁻¹ξ)   and   h(ξ) = c^{-3/2}(U⁻¹h)(c⁻¹ξ),
```

so the Jacobians cancel and `(angularOrderLowering h)(ξ) = σ(c⁻¹ξ)·h(ξ)`.  That is **precisely**
the lane's `loweringMult s r ξ = W_r(c⁻¹ξ)·B_{r-s}(c⁻¹ξ)·W_{-s}(c⁻¹ξ)`.  The lemma is right.

And `σ(c⁻¹ξ) = B_{r-s}(c·c⁻¹ξ) = B_{r-s}(ξ)`, i.e. the two closed forms agree exactly, up to the
dilation argument, as anticipated.  Verified in Lean (probe, compiles):

```lean
theorem loweringMult_eq (s r : ℝ) (ξ : Space) :
    loweringMult s r ξ = sobolevBesselWeight (r - s) ξ := by
  rw [loweringMult, lowering_mid_symbol_eq, smul_inv_smul₀ frequencyUnit_pos.ne']
```

So on the raw `L²` carrier the angular order lowering is multiplication by the **ordinary**
`(1+|ξ|²)^{(r-s)/2}` — the angular convention conjugates away entirely.  Sanity: at `r = s` this is
`1`, and deriving `angularOrderLowering s s = id` from the lane's coeFn reproduces A04's
independently proved `angularOrderLowering_self` (`RealPairing.lean:157`).  Verified in the probe
(`self_crosscheck`).  This is a genuine second-source cross-check of the delivered lemma.

### (b) Is the commutation the right SL7c statement?

Instantiation works as intended (probe, compiles):

```lean
example (m : ℝ) (A : RealVectorSobolev (m + 2)) :
    lerayComplement m (lowerVectorL (m+2) m (by linarith) A)
      = lowerVectorL (m+2) m (by linarith) (lerayComplement (m+2) A) :=
  lerayComplement_lowerVectorL (m + 2) m (by linarith) A
```

**The datum-transport corollary is extractable in four lines**, confirming the worker's claim that
it sits inside `isSobolevPath_lower` (`HalfOrder.lean:120`) — verified:

```lean
theorem isSobolevDatum_lower {s r : ℝ} (hrs : r ≤ s) {z : Space → Space}
    {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    IsSobolevDatum r z (lowerVectorL s r hrs A) := by
  rw [isSobolevDatum_iff]; intro i; rw [lowerVectorL_apply]
  exact ((isSobolevDatum_iff s _ A).mp hA i).lower hrs
```

Chaining it with the commutation does give "the order-`r` Leray datum is the lowering of the
order-`s` Leray datum" **without** any uniqueness hypothesis (probe `leray_datum_lower`):
if `A` is an order-`s` datum of `z` and `lerayComplement s A` is an order-`s` datum of `w`, then
`lerayComplement r (lowerVectorL … A) = lowerVectorL … (lerayComplement s A)` is an order-`r`
datum of `w`.

**But that is the wrong direction for the SL7 bootstrap**, which runs order-0 seed ⟹ order-`m`
conclusion.  The needed converse is free, because `angularRealization_orderLowering`
(`Paper3/AngularTameProduct.lean:51`) is an *equation*, not an implication — so the transport is an
**iff** (probe `isSobolevDatum_lower_iff`, compiles, 6 lines):

```lean
IsSobolevDatum r z (lowerVectorL s r hrs A) ↔ IsSobolevDatum s z A
```

With that iff plus the lane's commutation, the order-`m` transport lemma
`IsSobolevDatum m z A → IsSobolevDatum m ((I−ℙ)z) (lerayComplement m A)` reduces to the **order-0**
one.  That is the real payoff of this lane and it is not written down anywhere in the deliverable.

### (c) Degeneracy

The commutation alone pins nothing — it holds trivially if `lerayComplement` were `0` or `id`, and
equally if `lowerVectorL` were `0`.  As the brief anticipated, this is fine: 081 pins the complement
(`lerayComplement_ae` :295, `_idempotent` :281, `_opNorm_le_one` :277, `_eq_zero_of_transverse` :316)
and this lane's own `angularOrderLowering_coeFn` now pins the lowering to the nowhere-vanishing
multiplier `(1+|ξ|²)^{(r-s)/2}`.  The proof is **not** degenerate: it consumes `lerayComplement_ae`
on both sides (`s` and `r`), `assemble_vec_ae` twice, `angularOrderLowering_coeFn` on every
component, and `map_smul` through the private `complementSymbolComplex_smul_apply`.  No `simp`-only
collapse, no route that would survive a zero symbol.

## 3. Consistency

* **Imports**: `D01.LerayDatum`, `D01.HalfOrder`, `D01.Transverse`, `A04.LaplacianPairing` — all
  canonical, all actually used (`lerayComplement`, `lowerVectorL`, `angularFrequencyDilation_coeFn`,
  `angularOrderLoweringMid*` respectively).  The one that *should* have been added is
  `A04.RealPairing` (finding 1).
* **No restated definitions.**  `loweringMult` is a new definition, not a copy;
  `complementSymbolComplex_smul_apply` is `private`.  No name in the module duplicates anything in
  tree (`grep` for `loweringMult` / `assemble_vec_ae` outside the module: only the axiom scratch).
* **`assemble_vec_ae` matches 081-reviewer finding 1's requested shape** and is in fact *more*
  general: stated for an arbitrary `h : Fin 3 → Lp ℂ 2 volume` rather than only for datum
  coercions, with value `WithLp.toLp 2 (fun j => h j ξ) : MNS2.R3C`, and
  `MNS2.R3C = EuclideanSpace ℂ (Fin 3)` (`vendor/HeliCorgi/Formal/R3StokesL2Operator.lean:13`).
  Proved the way the finding predicted (`ae_all_iff` + `coordinates_ae` + `coordinates_assemble` +
  `PiLp.ext`).  Good.
* **No leftover copy of `angularFrequencyDilation_coeFn`** — commit `3553cf6` removed it; the only
  occurrences in tree are `Transverse.lean:66` and the `Paper3` definition it is about.

## 4. Honesty of ATTEMPTS

Route (b) is described accurately and matches the delivered proof line for line: the `h = U(U⁻¹h)`
substitution, the forward-only use of `angularFrequencyDilation_coeFn`, the `c^{±3/2}` cancellation,
and the quasi-measure-preserving transport of the middle symbol to `c⁻¹ξ`.

"**No complex 0-homogeneity lemma needed**" is **true of the delivered proof**: `grep -nE 'smul|homog'`
on the module shows every `smul` use is either linearity (`map_smul`, `PiLp.smul_apply`,
`WithLp.toLp_smul`, `Complex.real_smul`, `smul_eq_mul`) or the dilation's measure bookkeeping
(`Measure.map_addHaar_smul`, `Measure.smul_absolutelyContinuous`, `continuous_const_smul`).  Nothing
asserts homogeneity of `complementSymbolComplex`.  081's finding 4 is *avoided here*, not discharged.

The one dishonest-by-omission item is discarded-approach #2 (see finding 1).

---

## Findings

1. **(medium — reuse + accuracy; `ATTEMPTS_LERAY_LOWERING.md` "Failed / discarded" item 2;
   `LerayLowering.lean:76-82`)**  "`RealPairing.lean` (082) `lowering_mid_symbol_eq` — no such
   file/lemma exists in tree (`find`/`grep` empty)" is **false**:
   `Section4/A04/RealPairing.lean:114`, present at base commit `120a5bc`.  Consequence:
   `loweringMult` ships as an unsimplified three-factor product that collapses in one rewrite to
   `sobolevBesselWeight (r - s) ξ` (verified above).  The delivered symbol is mathematically
   correct and agrees with 082's, so nothing is wrong — but every downstream consumer will now
   carry the long form.  **Fix (follow-on / SIMP lane, ~4 lines):** `import
   NSFormalization.Section4.A04.RealPairing`, add `loweringMult_eq` and a simplified
   `angularOrderLowering_coeFn'`; optionally redefine `loweringMult := sobolevBesselWeight (r-s)`.
   Also correct the ATTEMPTS entry so the false "not in tree" claim does not propagate.

2. **(low — under-delivery; ATTEMPTS "Corollary (datum bookkeeping) — already exists")**  The
   downward transport really is inside `isSobolevPath_lower` and extracts in 4 lines, as claimed.
   But (i) `isSobolevPath_lower` is a statement about a datum *path* over `t`, while SL7/SL8 consume
   a single datum at a single time, and (ii) the direction SL7's bootstrap needs is the **converse**,
   which nothing in tree states.  Both are free from `angularRealization_orderLowering`
   (`AngularTameProduct.lean:51`, an equation) as a 6-line **iff**.  Calling the standalone lemma
   "over-engineering" is the wrong call here — it is the interface SL7b/SL8 will call.
   **Fix:** add `isSobolevDatum_lower` and `isSobolevDatum_lower_iff` in the SL7 lane (probe text
   above is ready to paste).

3. **(low — stale doc; `ATTEMPTS_LERAY_LOWERING.md` §"What was proved", third bullet)**  Still lists
   `angularFrequencyDilation_coeFn — copied from lane 079` among the module's public lemmas; commit
   `3553cf6` removed it and §"Duplication — discharged" says so.  Contradictory.  **Fix:** delete the
   bullet.

4. **(informational — not this lane's file)** `Section4/D01/Transverse.lean:60-64` still says
   "lane 085 is copying it meanwhile".  Now false.  For whichever SIMP lane promotes
   `angularFrequencyDilation_coeFn` to `Paper3/AngularFourierDilation.lean`.

5. **(informational — scope of SL7c)**  The delivered lemma is not P2_SPLIT 7c's headline
   `angularRealization m ∘ Q = Q_dist ∘ angularRealization m`; it is the "commutes with the scalar
   order weight" half.  081's finding 4 (0-homogeneity of `complementSymbolComplex`, i.e. the
   normalized-angular-ξ ↔ raw-ξ convention bridge) is untouched and still owed.  The lane does
   narrow it usefully: combined with finding 2's iff, the order-`m` transport reduces to the
   **order-0** transport, so the convention bridge is paid **once**, not per order.  Worth stating
   explicitly in `P2_SPLIT.md` when SL7 is scheduled.

6. **(very low — process)**  The lane carries no claim commit and no registry touch (diff = the 3
   reviewed files).  `check_work_queue.py` is green because D01 is already owned by `erenup` from
   the earlier lanes, so nothing is inconsistent; noted only against CLAUDE.md's lane recipe.

---

## 5. Commands and results

All from `.claude/worktrees/085-D01-p2-sl7c-commute`, after `bash scripts/lean-install.sh`
(idempotent, ended `== OK`), `. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`; lake run only
from `verification/`, one process at a time.

| # | Command | Result |
|---|---|---|
| 1 | `lake build NSFormalization.Section4.D01.LerayLowering` | `Build completed successfully (9926 jobs).` (only pre-existing vendor/Paper3 deprecation warnings) |
| 2 | `lake env lean ../formalization/NSFormalization/Section4/D01/LerayLowering.lean` | **no output** (0 bytes), exit 0 |
| 3 | `lake env lean ../research/D01/axioms_leray_lowering.lean` | 4 declarations, each `[propext, Classical.choice, Quot.sound]`: `assemble_vec_ae`, `loweringMult`, `angularOrderLowering_coeFn`, `lerayComplement_lowerVectorL` |
| 4 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/LerayLowering.lean` | one hit, `:41`, inside the docstring ("No `sorry`, no `axiom`"). Scratch file: no hits |
| 5 | `make check` | exit 0 (`test_contract_policy` 13 tests OK; `check_work_queue` "30 work items … consistent") |
| 6 | `make test` (extra) | all contract Tests replayed, "standard logical axioms only" |
| 7 | `lake build NSFormalization.Section4.{A04.RealPairing,A03.VectorTameProduct,D01.HalfOrder}` | success (probe deps) |
| 8 | reviewer probe `/tmp/rev085_probe.lean` (7 declarations: `loweringMult_eq`, `angularOrderLowering_coeFn'`, `self_crosscheck`, `isSobolevDatum_lower`, the `m+2 → m` instantiation, `leray_datum_lower`, `isSobolevDatum_lower_iff`) | **compiles**, only one `unusedVariables` linter warning (an intentionally unused hypothesis in one probe) |
| 9 | `git diff --stat 120a5bc HEAD` | 3 files, +281, −0 |

## 6. What SL7b (order-0 seed → every order) and SL8 now have, and still need

**Have.**  The order-lowering operator is now a first-class **scalar a.e. Fourier multiplier on the
raw carrier** (`angularOrderLowering_coeFn`) — before this lane it was only available as the
conjugated composite `U ∘ Mid ∘ U⁻¹`, and only its *middle* symbol had a coeFn.  That immediately
gives the SL7c commutation `lerayComplement r ∘ lowerVectorL = lowerVectorL ∘ lerayComplement s`
for all real `r ≤ s`, and the exported `assemble_vec_ae` closes 081-review finding 1 (the
`assemble`-to-tuple repackaging SL5/SL7/SL8 all need), in a more general form than requested.
Together with the four-line `isSobolevDatum_lower` and the six-line `isSobolevDatum_lower_iff`
(both verified in the probe, neither yet committed), the structural consequence is:

> the **order-`m`** Leray transport lemma `IsSobolevDatum m z A ⟹ IsSobolevDatum m ((I−ℙ)z)
> (lerayComplement m A)` follows from the **order-0** one, for every `m ≥ 0`.

So SL7b's bootstrap is, modulo the two small lemmas above, structurally done: once the order-0 case
exists, every order follows by lowering to 0, applying the seed, and lifting back through the iff.

**Still need.**
1. **SL7a — the order-0 datum constructor** (`MemLp ⟹ ∃ A, IsSobolevDatum 0 z A`, via
   `MeasureTheory.Lp.fourierTransformₗᵢ`).  Unchanged; still the only thing that *manufactures* a
   datum rather than transforming one.  Not touched by this lane.
2. **The order-0 transport lemma** `IsSobolevDatum 0 z A ⟹ IsSobolevDatum 0 ((I−ℙ)z)
   (lerayComplement 0 A)`.  This is where 081's finding 4 gets paid: `angularRealization 0` is
   `angularCoordinateRealization 0 ∘ angularFrequencyDilation.symm`, so relating
   `complementSymbolComplex ξ` (raw `ξ`) to the distributional `(I−ℙ)` still needs
   `complementSymbolComplex (c • ξ) = complementSymbolComplex ξ` for `c > 0` — absent from tree
   (`LeraySymbol.lean:144` has it for the *real* symbol; `LerayMultiplier.lean:309` has only
   `complementSymbolComplex_neg`).  **Budget it once, at order 0.**  Mirroring the real proof via
   `Submodule.span_singleton_smul_eq` is the indicated route.
3. **The two small bookkeeping lemmas of finding 2** (`isSobolevDatum_lower`,
   `isSobolevDatum_lower_iff`) — trivial, but nothing in tree states them.
4. **SL5 / SL6** (longitudinality of `∇p`; the `iξⱼ` datum) — unchanged, supply the hypotheses of
   `lerayComplement_eq_self_of_longitudinal` / `_eq_zero_of_transverse`.
5. **SL8's final pin** — `representative_ae` + `angularRealization_boundedRepresentative` +
   `DatumToJets` ⇒ `SmoothSquareIntegrableJets (∇p)`.  Unchanged.

SL8's blocker list can now be written **SL7a, the order-0 transport (0-homogeneity), SL5, SL6** —
the "at every order" part of eq:Rpressure is no longer a blocker.
