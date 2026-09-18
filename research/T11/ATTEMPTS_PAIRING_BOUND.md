# ATTEMPTS — lane 336, T11 unit U12b (the tame pairing bound)

Non-generated file. Route, reuse audit, every path that failed with its exact
error text, and the exact residual.

## 0. Target and route

Fact (b) of `ATTEMPTS_HIGH_ORDER.md` §3 (lane 322's residual):
`|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m}`, i.e. the nonlinear
term of `appendix-a-local-theory.tex:131-138` `eq:Rhigh`.

Realized on the coefficient carrier, at a single top-order datum, because
`PeriodicSobolev` is **phantom-indexed**: one `A : PeriodicSobolev r` carries
every order of the same field, and `torusOrderDown r s A` is its `H^s`
realization (`HighOrder.lean:158`). With `s := r - 1` (`= m`, so `r = m+1`), the
three factors of the estimate are

```
‖torusOrderDown r 2 A‖      -- ‖u‖_{H²}
‖torusOrderDown r (r-1) A‖  -- ‖u‖_{H^m}
‖A‖                         -- ‖u‖_{H^{m+1}}, the "gradient" factor g of hRhigh
```

and the convection is lane 328's `torusConvectionDatumReal hr A A`, which lands
at exactly the phantom order `r - 1`, so the pairing typechecks with no
reindexing at all.

Fourier-side chain (all four steps are in `Section3/T11/PairingBound.lean`):

1. `|2πkⱼ| ≤ W(k)^{1/2}` (`torusDerivativeSymbol_le`), so the output weight
   `W(k)^{(r-1)/2}` of the symbol plus the derivative gives `W(k)^{r/2}`, and the
   partner `H^{r-1}` coefficient contributes `W(k)^{-1/2}`; net `W(k)^{(r-1)/2}`
   against the **raw** convolution `∑ₗ |ĉ(l)||ĉ(k-l)|`.
2. Peetre at the real exponent `(r-1)/2`, `torusWeightPeetre`:
   `W(k)^a ≤ 4^a (W(l)^a + W(k-l)^a)`, so in each half exactly one factor picks up
   the full `H^{r-1}` weight and the other stays unweighted.
3. The unweighted factor is summed in `ℓ¹` against the `H²` datum:
   `∑ₙ |ĉ(n)| ≤ (∑ₙ W(n)^{-2})^{1/2} ‖u‖_{H²}` — this is the step that makes the
   estimate *tame*, and it needs `∑ₖ W(k)^{-2} < ∞`, which was **not** in the tree
   (see §2.1).
4. One Cauchy–Schwarz on the lattice square `Z³ × Z³` against the convolution
   measure: `torusTrilinearConvolution`,
   `∑_{k,l} X(k)Y(l)β(k-l) ≤ ‖X‖_{ℓ²}‖Y‖_{ℓ²}‖β‖_{ℓ¹}`, proved by writing the
   summand as `(X(k)√β)·(Y(l)√β)` and computing the two marginals
   `(∑X²)(∑β)`, `(∑Y²)(∑β)` by the two reindexings `(k,l)↦(k,k-l)` and
   `(k,l)↦(l,k-l)`.

The divergence-free cancellation `⟪(u·∇)v,v⟫_{L²} = 0` is **not** used anywhere:
the bound holds for every real datum. That matches the manuscript, which only
uses solenoidality for the pressure term (discharged by lane 322).

## 1. Reuse audit (what did NOT have to be redone)

* `Section3/T11/ConvolutionBoundReal.lean` (lane 328) — `torusConvectionSymbolReal`,
  `torusConvectionDatumReal`, `torusConvectionDatumReal_coeff`,
  `torusProjectedConvectionDatumReal(_coeff)`. The symbol and the datum are taken
  verbatim; only their **norms** are re-estimated (328 proves the non-tame
  `H^r × H^r → H^{r-1}` bound, which cannot give the `H²` factor).
* `Section3/T11/HighOrder.lean` (lane 322) — `torusRealPairing`, `torusOrderDown`,
  `torusOrderDown_reweight`, `torusSobolevNormAt(_eq, _nonneg)`.
  The proof of `projection_drop` is lane 322's `torusPressureDrop` computation
  with the `2πi` normalization stripped.
* `Section3/T11/CriterionBridge.periodicSobolevENorm_eq_datum` and
  `Section3/T11/Persistence.persistence_datum_of_reweight` — the two physical
  bridges (`torusPairingBound_enorm`, `torusPairingBound_profile`).
* `Paper1.PeriodicWeightShift.weight_add_le` — the lattice triangle inequality
  behind Peetre.
* Mathlib: `lp.tsum_mul_le_mul_norm` (Hölder, used three times: the pairing,
  the `ℓ¹` bound, the lattice-square Cauchy–Schwarz), `lp.norm_rpow_eq_tsum`,
  `Summable.prod` / `Summable.prod_factor` / `Summable.tsum_prod`,
  `Real.summable_abs_int_rpow`.

**Deliberately reproved, not imported:** `ConvolutionBoundReal.lean`'s weight
arithmetic (`weightR_pos`, `one_le_weightR`, `weightR_peetre`,
`derivativeR_sq_le`) is `private`, so `wpos`, `one_le_w`, `torusWeightPeetre`,
`torusDerivativeSymbol_le` are proved again here (about 40 lines). The Peetre
and derivative lemmas are exported this time.

## 2. Paths tried, and what failed

### 2.1 `∑ₖ W(k)^{-2} < ∞` is not in the tree — new proof

`Paper1.PeriodicInverseWeightSummable` only has `summable_weight_rpow_neg_three`
(`∑ W^{-3}`), and lane 328's `inverse_weightR_summable` requires `3 ≤ r` for
exactly that reason. Using it would force the low factor into `H³`, i.e. the
bound `C‖u‖_{H³}‖u‖_{H^m}‖u‖_{H^{m+1}}`, which is **useless** for `eq:Rhigh`:
the continuation criterion controls `∫‖u‖²_{H²}`, not `H³`.

`torusInverseWeight_summable` therefore proves `Summable (W^(-r))` for every
real `r > 3/2`, by splitting the weight across the three coordinates,
`W(k)^r ≥ ∏ᵢ (1+kᵢ²)^{r/3}` (each factor by `1 + kᵢ² ≤ W k` and monotonicity of
`rpow`), and `∑_{n∈Z} (1+n²)^{-r/3} < ∞` because `2r/3 > 1`
(`Real.summable_abs_int_rpow`). Specialized at `r = 2`. Failures on the way:

* `simp only [this, if_pos rfl]` in the `n = 0` base case →
  ``warning: `if_pos` has been deprecated: Use `ite_eq_left` instead`` and then
  ```
  error: linarith failed to find a contradiction
  a✝ : (if True then 1 else 0) + |↑0| ^ (-(2 * a)) < (1 + ↑0 ^ 2) ^ (-a)
  ```
  `simp` had rewritten the goal into a shape `linarith` could not use. Fix: prove
  the three values (`(1+0²)^{-a} = 1`, `0 ≤ |0|^{-2a}`, `(if 0 = 0 then 1 else 0) = 1`)
  as separate `have`s, `rw` them, then `linarith`.
* `congr 1` on `(|n|^{(2:ℝ)})^a = ((n)^2)^a` produced the **wrong** goal, so the
  following rewrite failed:
  ```
  error: Tactic `rewrite` failed: Did not find an occurrence of the pattern 2
    in the target expression |↑n| ^ a = ↑n ^ 2
  ```
  Fix: no `congr`; prove `|n|^{(2:ℝ)} = n^2` as a standalone `have` and rewrite
  inside `Real.rpow_mul`.
* `inv_le_inv_of_le` → ``error: Unknown identifier `inv_le_inv_of_le` ``. At this
  pin the usable form is `one_div_le_one_div_of_le` (after `inv_eq_one_div`).
* `mul_le_mul (mul_le_mul _ _ p1 q0) (hstep 2) p0 _` →
  ```
  error: Application type mismatch: the argument p0 has type
    0 ≤ (1 + ↑(k 0) ^ 2) ^ (r / 3)
  but is expected to have type 0 ≤ (1 + ↑(k 2) ^ 2) ^ (r / 3)
  ```
  `mul_le_mul`'s third argument is the nonnegativity of the *right* factor of the
  left-hand product, not of the first factor.

### 2.2 `Summable.comp_injective` loops at `whnf` unless `i` is given explicitly

This cost the most time. With the reindexing `(k,l) ↦ (l, k-l)` packaged as a
named injectivity lemma,

```lean
have hb := hY.mul_of_nonneg hβ (fun k ↦ sq_nonneg (Y k)) hβ0
exact hb.comp_injective shiftSnd_inj
```
```
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
has been reached
```
(reported at the *declaration header*, not at the tactic; raising the budget to
`1000000` did not help, so it is a genuine loop, not slowness). The elaborator
has to solve `(fun x ↦ Y x.1^2 * β x.2) ∘ ?i =?= fun p ↦ Y p.2^2 * β (p.1 - p.2)`
with `?i` still a metavariable when the expected type arrives. Fix: name the
index map in the application,

```lean
exact hb.comp_injective (i := fun p : PeriodicFrequency × PeriodicFrequency ↦
  (p.2, p.1 - p.2)) shiftSnd_inj
```

which elaborates in milliseconds. The **asymmetry is a trap**: the companion
reindexing `(k,l) ↦ (k, k-l)` (first component unchanged) elaborated fine without
the hint, so the pattern only shows up on one of the two marginals. Every
`comp_injective` in this module now passes `i` explicitly.

### 2.3 `Equiv.tsum_eq` cannot be used through `rw`

```lean
change (∑' p, (fun q ↦ X q.1 ^ 2 * β q.2) (shiftEquivFst p)) = _
rw [shiftEquivFst.tsum_eq]
```
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑' (c : PeriodicFrequency × PeriodicFrequency), ?f (shiftEquivFst c)
```
(the `change` itself succeeded — the goal displayed is literally the pattern).
`rw` will not solve the higher-order pattern `?f (e c)`. Fix: use it as a term
with a fully stated intermediate `have`,
```lean
have he1 : (∑' p, X p.1 ^ 2 * β (p.1 - p.2)) = ∑' q, X q.1 ^ 2 * β q.2 :=
  shiftEquivFst.tsum_eq (fun q ↦ X q.1 ^ 2 * β q.2)
```
Writing it inline inside `Eq.trans` *also* timed out at `whnf` in the
`(l, k-l)` case; the explicitly typed `have` is what makes it robust.

### 2.4 Small ones, with their error text

* `rw [h.1, h.2]` where `h.1 : a.1 = b.1`, `h.2 : a.1 - a.2 = b.1 - b.2`:
  ```
  error: Did not find an occurrence of the pattern a.1 - a.2
    in the target expression b.1 - (b.1 - a.2) = b.1 - (b.1 - b.2)
  ```
  The first rewrite destroys the pattern of the second. Use `rw [h.2, h.1]`.
* `tsum_pos` → ``error: Unknown identifier `tsum_pos` `` (it exists only for
  `ℝ≥0`, `InfiniteSum/ENNReal.lean:471`). `le_tsum` → ``Unknown identifier``:
  the real-valued form is the protected `Summable.le_tsum`.
* `((h0.add h1).add h2).tsum_add h2` →
  ```
  error: Did not find an occurrence of the pattern
    ∑' b, (wAbs .. 0 b ^2 + wAbs .. 1 b ^2 + wAbs .. 2 b ^2 + wAbs .. 2 b ^2)
  ```
  `Summable.tsum_add` takes the summability of the two *summands*, so the chain is
  `(h0.add h1).tsum_add h2` then `h0.tsum_add h1`.
* `(conv_summable h2 A i k).mul_left _` — the placeholder was unified with the
  ambient real `r`, leaving
  ```
  ⊢ r * wTot r 0 A l * wAbs r 0 A i (k - l) = wTot r 0 A l * wAbs r 0 A i (k - l) *
      periodicFrequencyWeight k ^ (-1 / 2 + r * (1 / 2)) * wAbs r r A i k
  ```
  and `ring` failing. Always give `Summable.mul_left` its constant.
* `Complex.conj_ofReal'` → ``Unknown constant``. For an **integer** cast the
  lemma is the generic `map_intCast`.

### 2.5 Design choices that avoided work

* **`torusOrderDown r r A = A` was never needed.** Proving it would require a
  datum extensionality argument through the multiplier; instead
  `wAbs_self : wAbs r r A i k = ‖A.1 i k‖` gives the top-order energy directly
  from `lp.norm_rpow_eq_tsum` on `A.1 i`, and `PiLp.norm_apply_le` bounds it by
  `‖A‖`.
* **The `j`-sum of the convection is absorbed into the coefficient function**
  (`wTot r s A k = ∑ⱼ wAbs r s A j k`) at the pointwise stage, through one
  `Summable.tsum_finsetSum`. The alternative — keeping `∑ⱼ` outside and moving it
  through `∑'ₖ` — needs the same exchange plus six separate applications of the
  trilinear lemma instead of two.
* `(a+b+c)² ≤ 3(a²+b²+c²)` gives `‖wTot‖_{ℓ²} ≤ √3 ‖·‖`, rounded to `2` so that
  the constant stays rational: `15 = 3 · (2 + 3)`.
* The statement is parameterized by `r` and `s` with `hrs : s = r - 1` and proved
  after `subst`, so the integer form (`torusPairingBound_nat`, `s := (m:ℝ)`,
  `r := (m:ℝ)+1`) needs no rewriting of `(m:ℝ)+1-1` under a dependent proof
  argument.

## 3. The exact residual

**Nothing in this module is conditional**: there is no `sorry`, no axiom, and no
named `Prop` input. What the lane does *not* deliver, and what `eq:Rhigh` still
needs on top of it:

1. **Fact (a) of lane 322's §3 is untouched** — time differentiability of the
   coefficient path and the momentum equation in datum form (Section 4's
   SL1/SL2). `hRhigh` is the conjunction of (a) and (b); this lane closes (b)
   only. U12a remains open.
2. **The physical identification of the convection datum at real order.**
   `torusPairingBound(_enorm, _profile)` bounds the pairing of
   `torusConvectionDatumReal hr A A` — which *is* the convection by lane 328's
   construction of the symbol — against the velocity datum. Turning that into a
   statement about the physical field `(u·∇)u` needs
   `IsPeriodicDatum (r-1) (fun x ↦ convectionDivergenceT u t x) (torusConvectionDatumReal hr A A)`.
   The order-3 case exists (`MildPressure.periodicFourierCoeff_convection_eq_torusConvectionDatum`,
   lane 326, via the periodic convolution theorem), and lane 328's
   `torusConvolutionCLM_real_reweight` / `_coeff_three` transport the real-order
   symbol onto reweighted data, so the ingredients are all present; the
   general-order statement is not proved anywhere and is the natural next small
   lane. It is **not** needed if the consumer works on the coefficient carrier,
   which is where `eq:Rhigh`'s pairing naturally lives.
3. **No optimality.** `C(s) = 15 · 4^{s/2} · (∑ₖ W(k)^{-2})^{1/2}` is explicit but
   crude: the `4^{s/2}` is Peetre's, the `3` counts components, the `5 = 2+3`
   counts the two halves of the split with the `√3 ≤ 2` rounding. No lower bound
   and no sharp-constant claim is made.
4. The `ℓ¹` step is stated at `H²` because `∑ W^{-2} < ∞`; the same proof gives
   any order `> 3/2` (`torusInverseWeight_summable` is proved in that generality),
   but the module only instantiates `2`.

## 4. Commands

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PairingBound
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/PairingBound.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/pairing_bound_closes.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_pairing_bound.lean
make check
```
