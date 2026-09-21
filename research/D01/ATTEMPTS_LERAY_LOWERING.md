# ATTEMPTS — D01 · P2 · SL7c: Leray complement commutes with order lowering

Lane 085. Module: `formalization/NSFormalization/Section4/D01/LerayLowering.lean`.
Unit delivered: `lerayComplement_lowerVectorL` (+ exported helper `assemble_vec_ae`).
No `sorry`, no `axiom`, no `maxHeartbeats`. Axioms: standard three (see
`research/D01/axioms_leray_lowering.lean`).

## What was proved

`lerayComplement_lowerVectorL (s r : ℝ) (hrs : r ≤ s) (A : RealVectorSobolev s) :`
`  lerayComplement r (lowerVectorL s r hrs A) = lowerVectorL s r hrs (lerayComplement s A)`.

`lowerVectorL` is the **already existing** vector-level lowering (`HalfOrder.lean:99`,
`lowerVectorL_apply` :113, `= lowerDatum s r hrs (A i)` componentwise). The brief's placeholder
name `lowerVec` was not introduced — `lowerVectorL` is exactly it, so it is reused verbatim.

Supporting public lemmas in the module:
* `assemble_vec_ae` — the exported helper the brief requested (coeFn of `assemble` a.e. equals the
  pointwise `PiLp`/`EuclideanSpace ℂ (Fin 3)` tuple `fun j => h j ξ`). Three downstream lanes
  (SL5/SL7/SL8) repackage `lerayComplement_ae`'s `assemble` argument this way.
* `loweringMult` / `angularOrderLowering_coeFn` — the order-lowering operator as a plain a.e.
  Fourier multiplier `angularOrderLowering s r hrs h =ᵐ loweringMult s r · • h`.
* `loweringMult_eq` / `angularOrderLowering_coeFn'` — the multiplier collapses to the **standard
  Bessel weight** `sobolevBesselWeight (r−s) ξ = (1+‖ξ‖²)^{(r−s)/2}` in the raw variable (lane 082's
  `RealPairing.lowering_mid_symbol_eq`; the angular convention conjugates away). Added on review.
* `angularOrderLowering_self_of_coeFn` — cross-check: at `r = s` the multiplier is `1`, re-deriving
  A04's `RealPairing.angularOrderLowering_self` from this lane's coeFn (review probe B).
* `isSobolevDatum_lower`, `isSobolevDatum_lower_iff`, `leray_datum_lower` — the datum-transport
  interface (see the dedicated section below). Added on review.

(`angularFrequencyDilation_coeFn` is **not** a lemma of this module; it is imported from lane 079's
merged `Section4/D01/Transverse.lean` — see "Duplication — discharged" below.)

## Route chosen — (b), the raw a.e. multiplier

The brief offered two routes.

* **Route (a)** [rejected]: use `0`-homogeneity `complementSymbolComplex (c • ξ) = complementSymbolComplex ξ`
  (which does **not** yet exist — `LerayMultiplier.lean:309` only has `complementSymbolComplex_neg`,
  the `c = -1` case; `REVIEW_LERAY_DATUM.md` finding 4 flagged this gap). Cost of route (a): first
  prove the complex `0`-homogeneity (mirror `LeraySymbol.lean:144`'s real `complementSymbol_smul`
  via `Submodule.span_singleton_smul_eq`), THEN still push the dilation `ξ ↦ frequencyUnit⁻¹ • ξ`
  through the fibre reindexing inside the commutation proof. Two pieces of new machinery.

* **Route (b)** [executed]: show the lowering is a.e. a **scalar** multiplier in the *raw* frequency
  variable, `angularOrderLowering s r hrs h =ᵐ fun ξ => loweringMult s r ξ • h ξ`. Then a scalar
  multiplier commutes with the `ℂ`-linear fibre map `complementSymbolComplex ξ` by `map_smul`
  — no `0`-homogeneity of the complex symbol is needed at all. One new lemma
  (`angularOrderLowering_coeFn`), plus the dilation coefficient.

Route (b) needs strictly less: it avoids the complex `0`-homogeneity lemma entirely (the very lemma
route (a) would first have to build). Decision recorded per brief.

### The dilation-cancellation trick (why `angularOrderLowering_coeFn` needs no `U⁻¹` coefficient)

`angularOrderLowering s r hrs = U ∘ M ∘ U⁻¹` with `U = angularFrequencyDilation` and
`M = angularOrderLoweringMid` (`A04.angularOrderLowering_eq_dilation_mid`, a `rfl`).
`M` acts a.e. as multiplication by the symbol `σ(η) = angularWeightSymbol r η · sobolevBesselWeight
(r-s) η · angularWeightSymbol (-s) η` (`A04.angularOrderLoweringMid_coeFn`).

Instead of computing `U⁻¹`'s coefficient, substitute `h = U (U⁻¹ h)` and apply the **forward**
dilation coefficient `angularFrequencyDilation_coeFn` twice:
`(U (M (U⁻¹ h)))(ξ) = c^{-3/2} · (M (U⁻¹ h))(c⁻¹ξ) = c^{-3/2} · σ(c⁻¹ξ) · (U⁻¹ h)(c⁻¹ξ)`
and `h(ξ) = (U (U⁻¹ h))(ξ) = c^{-3/2} · (U⁻¹ h)(c⁻¹ξ)`. The `c^{±3/2}` cancel, so
`(angularOrderLowering h)(ξ) = σ(c⁻¹ξ) · h(ξ)`, i.e. `loweringMult s r ξ := σ(frequencyUnit⁻¹ • ξ)`.
The middle-symbol a.e. identity is transported from `η` to `c⁻¹ξ` by the quasi-measure-preserving
dilation (`hqmp := ⟨measurable, map_addHaar_smul ▸ smul_absolutelyContinuous⟩`, then `.ae`).

## The `assemble`/`WithLp.toLp` bridge in the commutation proof

After `PiLp.ext; Subtype.ext; Lp.ext`, work at the coeFn level per component `i`. Both sides reduce
a.e. to `loweringMult s r ξ • (complementSymbolComplex ξ (WithLp.toLp 2 (fun j => (A j) ξ))) i`:
* LHS (`lerayComplement r (lowerVectorL A)`): `lerayComplement_ae` gives `(complementSymbolComplex ξ
  (assemble(lowered) ξ)) i`; `assemble_vec_ae` turns `assemble(lowered) ξ` into the tuple; each
  entry `(angularOrderLowering (A j)) ξ = loweringMult · • (A j ξ)` by `angularOrderLowering_coeFn`;
  `WithLp.toLp_smul` pulls the scalar out of the tuple; `map_smul` + `PiLp.smul_apply` pull it
  through `complementSymbolComplex ξ` and past the `i`-projection.
* RHS (`lowerVectorL (lerayComplement s A)`): componentwise `= angularOrderLowering s r hrs
  ((lerayComplement s A) i)` (`rfl` via `lowerVectorL_apply` + `coe_lowerDatum`);
  `angularOrderLowering_coeFn` then `lerayComplement_ae` then `assemble_vec_ae`.

## Corollary (datum bookkeeping) — now delivered as the SL7b/SL8 interface

Initially I judged the standalone corollary redundant with `HalfOrder.isSobolevPath_lower`
(`HalfOrder.lean:120`), whose body is the vector-level lowering verbatim (`rw [isSobolevDatum_iff];
intro i; rw [lowerVectorL_apply]; exact ((isSobolevDatum_iff s _ A).mp hA i).lower hrs`). The
lane-085 review (finding 2) corrected this: `isSobolevPath_lower` is about a datum *path* over `t`,
while SL7/SL8 consume a single datum at a single time, and — more importantly — the direction the
SL7 bootstrap needs is the **converse** (order-0 seed ⟹ order-`m`), which nothing in tree stated.
So the module now exports three standalone lemmas (reviewer probes C/E/F):
* `isSobolevDatum_lower` — the downward transport, single-time standalone form.
* `isSobolevDatum_lower_iff` — the **iff**, free because `Paper3.angularRealization_orderLowering`
  (`AngularTameProduct.lean:51`) is an *equation*: the lowered datum realizes the same tempered
  distribution, so being an order-`r` datum of the lowering ⟺ being an order-`s` datum. This is the
  lemma that turns SL7c into a bootstrap.
* `leray_datum_lower` — commutation + `isSobolevDatum_lower`: the order-`r` Leray datum is the
  lowering of the order-`s` one, no uniqueness hypothesis. (Its `_hA` argument records that `A` is a
  datum of `z` for the narrative; the proof needs only the transport hypothesis, hence the
  underscore to keep the module warning-free.)
The scalar per-component `IsScalarSobolevDatum.lower` (`A03/ScalarTameProduct.lean:114`) and
`isSobolevDatum_iff` (`A03/VectorTameProduct.lean:54`) are the pairing partners.

## Failed / discarded approaches

1. **Route (a) (complex `0`-homogeneity first).** Rejected before writing: it requires proving
   `complementSymbolComplex (c • ξ) = complementSymbolComplex ξ` (absent from tree) AND then still
   the dilation reindexing. Strictly more machinery than route (b). Not attempted in Lean.
2. ~~**`RealPairing.lean` (082) `lowering_mid_symbol_eq`** — the brief cited it, but no such
   file/lemma exists in tree (`find`/`grep` empty).~~ **CORRECTION (lane-085 review, finding 1):
   this claim was wrong.** `lowering_mid_symbol_eq` DOES exist at
   `Section4/A04/RealPairing.lean:114` (namespace `NSFormalization.Paper3`), present at the base
   commit. My grep missed it: I searched only for a file literally named `RealPairing.lean` under
   the path the brief spelled and for `lowering_mid_symbol_eq` in `A04/RealPairing.lean` while my
   shell's cwd was the `085-` worktree (the earlier `find`/`grep` had run against a relative path
   that resolved wrong), so both came back empty and I concluded it was absent — it was not. The
   proof still went through via `A04.angularOrderLoweringMid_coeFn` (`LaplacianPairing.lean:146`),
   which gives the same three-factor symbol; but `lowering_mid_symbol_eq` collapses it to the single
   Bessel weight. The review added `import NSFormalization.Section4.A04.RealPairing` and the
   one-line `loweringMult_eq` (+ `angularOrderLowering_coeFn'`), so downstream consumers get the
   short form `sobolevBesselWeight (r−s) ξ` instead of the long product.
3. **Deriving `angularFrequencyDilation.symm`'s coeFn** — avoided by the `h = U (U⁻¹ h)` substitution
   trick above; only the forward `angularFrequencyDilation_coeFn` is needed.

## Duplication — discharged (lane 079 merged)

`angularFrequencyDilation_coeFn` was initially copied verbatim from lane 079. After 079 merged onto
`erenup/integration` (its `Section4/D01/Transverse.lean` with `angularFrequencyDilation_coeFn` :66),
the copy was **removed** and the module now `import`s `NSFormalization.Section4.D01.Transverse` and
uses that lemma directly. It lives in the parent namespace `NSFormalization.Section4.D01`, so from
this module's `NSFormalization.Section4.D01.Leray` the bare name resolves with no extra `open` or
qualification (no clash with the opened `NSFormalization.Paper3`). No duplicate remains.

## Scope of SL7c and what remains (review finding 5)

This lane delivers the **"commutes with the scalar order weight"** half of P2_SPLIT step 7c. It is
NOT the headline `angularRealization m ∘ Q = Q_dist ∘ angularRealization m`: the remaining half is
the **convention bridge** between the normalized-angular frequency variable (in which
`angularRealization s` lives) and the raw `ξ` (in which `complementSymbolComplex ξ` is HeliCorgi's
symbol) — i.e. `0`-homogeneity of the complex symbol `complementSymbolComplex (c • ξ) =
complementSymbolComplex ξ` (081's finding 4, still owed). This lane does **narrow** that obligation:
with `isSobolevDatum_lower_iff` + `lerayComplement_lowerVectorL`, the order-`m` transport
`IsSobolevDatum m z A → IsSobolevDatum m ((I−ℙ)z) (lerayComplement m A)` reduces to the **order-0**
one, so the convention bridge is paid **once at order 0**, not per order. (Recommend recording this
in `P2_SPLIT.md` when SL7 is scheduled.)

SL7a's order-0 datum constructor already exists on integration and should not be re-derived:
`D01/OrderZeroDatum.lean` `exists_isSobolevDatum_zero_of_memLp` (:119),
`IsSobolevDatum 0` from `MemLp z 2 volume`.

## Commands run

* `lake build NSFormalization.Section4.D01.LerayLowering` → `Build completed successfully
  (9927 jobs).` (only vendor HeliCorgi warnings). [after review edits: +`RealPairing` import and
  the five added lemmas]
* `lake env lean ../formalization/NSFormalization/Section4/D01/LerayLowering.lean` → silent
  (0 bytes; no unused-variable warnings — the unused `_hA` in `leray_datum_lower` is underscored).
* `lake env lean ../research/D01/axioms_leray_lowering.lean` → all ten public decls `[propext,
  Classical.choice, Quot.sound]`.
* `make check` → exit 0.
