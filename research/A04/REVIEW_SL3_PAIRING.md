# Review — lane 076, task A04, sub-lemma SL3 steps 1–2 (Laplacian pairing)

Reviewer: opus (lane-review, light & strict).  Commit under review: `b14ba40`
(`[076-A04] SL3 steps 1-2: skew-adjointness of the angular directional derivative
and self-adjointness of the order lowering on L²`).  Worktree:
`.claude/worktrees/076-A04-sl3-pairing`.  Read/build only; no repo file other than
this one was written.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is sound and the delivered statements are faithful.  The module builds,
elaborates with zero warnings at the default heartbeat budget, is `sorry`-free,
all 10 declarations depend only on `[propext, Classical.choice, Quot.sound]`, and
`make check` passes.  The factorization `D = U ∘ M_s ∘ U⁻¹` is a genuine
structural `rfl` (not an `s` coincidence), the carrier is the right one, and the
minus sign is load-bearing — I falsified the "wrong reason" hypothesis by running
the identical proof script against the false self-adjoint sign and watching it
fail (see F0-probe below).

The notes are: **two substantive gaps in the step-3 briefing** (F1, F2), which
make the remaining work *larger* and differently-shaped than
`ATTEMPTS_SL3_PAIRING.md` §"What still remains" suggests, plus three cosmetic
items.  No finding requires a change to any proved statement, and nothing here
blocks the merge.

---

## Findings

### F1 — Medium.  The step-3 plan omits the datum-order reconciliation, which *is* the remaining mathematical content.

**Location:** `research/A04/ATTEMPTS_SL3_PAIRING.md` §"What still remains", bullet
"Step 3 — the Laplacian datum assembly"; mirrored in
`formalization/NSFormalization/Section4/A04/LaplacianPairing.lean:33-35` and
`Section4/A04/LaplacianDatum.lean:53-58`.

The plan says the `m/m+1/m+2` bookkeeping is collapsed by
`Paper3.mid_symbol_order_independent` (`D01/DerivativeDatum.lean:207`).  That
lemma collapses the **operator** index only: it says every
`angularDirectionalDerivative s a` has the same symbol.  It says nothing about
the **datum** index, and the data at different orders are genuinely different
elements of `Lp ℂ 2 volume` (they differ by the Bessel weight — that is the whole
point of `angularRealization s` depending on `s`).

Concretely, run the plan through:

* `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))`  (the plan's assembly);
* `G = datum_m u`, so this lane's theorem gives
  `⟪G, datum_m(Δu)⟫ = -∑ⱼ ⟪D_j (datum_m u), D_j (datum_{m+2} u)⟫`;
* but `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum`
  (`LaplacianDatum.lean:130`) delivers the right-hand side as
  `∑ⱼ ‖D_j (datum_{m+1} u)‖²`.

So a step is missing, namely (with `v = ∂ⱼu`)

`⟪datum_{m-1} v, datum_{m+1} v⟫ = ‖datum_m v‖²`,

i.e. `⟪Λ⁻¹w, Λw⟫ = ‖w‖²` for the real positive lowering multiplier `Λ`.  This is
**exactly** what this lane's `inner_angularOrderLowering` is for — which means
that theorem is not an "optional companion" (as both the module docstring :29 and
the ATTEMPTS call it) but a required input, and the ATTEMPTS never says so.

**Fix (documentation only, for the next worker):** rewrite the step-3 bullet to
name the pieces.  All but one are already in tree:

* `D01.isSobolevDatum_unique` (`D01/ForceClass.lean:286`) — needed to say
  `datum_m u` *is* the lowering of `datum_{m+1} u`, not merely *a* datum.
* `A03.lowerDatum` / `A03.coe_lowerDatum` (`A03/RealAngularProduct.lean:140,144`)
  and `A03.IsScalarSobolevDatum.lower` (`A03/ScalarTameProduct.lean:116`) — the
  order-lowering datum fact (scalar form; a `RealVectorSobolev` analogue is a
  componentwise wrapper via `A03.isSobolevDatum_iff`).
* **Not in tree:** an order-independence lemma for the *lowering* middle symbol
  (`angularWeightSymbol r · sobolevBesselWeight (r-s) · angularWeightSymbol (-s)`
  depends only on `r - s`), or equivalently a commutation
  `angularDirectionalDerivative ∘ angularOrderLowering = angularOrderLowering ∘
  angularDirectionalDerivative`.  Either one is ~3 lines from
  `Paper3.weight_product_order_indep` (`D01/DerivativeDatum.lean:192`), but it has
  to be written.

### F2 — Medium.  The `re` step is neither definitional nor tooled, and the ATTEMPTS gives it one clause.

**Location:** `research/A04/ATTEMPTS_SL3_PAIRING.md` §"What still remains"
("… combines this skew-adjointness … with the real-subspace `re` and `PiLp 2`
componentwise bookkeeping …").

The delivered theorems are on the **complex** inner product of
`Lp ℂ 2 volume`.  `hlap` is consumed by `A04.inner_energy_assembly`
(`A04/HighEnergy.lean:101-110`), which is stated over
`[InnerProductSpace ℝ E]` and instantiated at `E = RealVectorSobolev m`, i.e. the
**real** inner product.  I checked what that instance actually is:

```
#synth InnerProductSpace ℝ (Lp ℂ 2 (volume : Measure Space))   -- L2.innerProductSpace
#synth InnerProductSpace ℝ (RealSobolevHilbert (1 : ℝ))        -- realSobolevInnerProductSpace 1
```

so the real inner product on the carrier is `MeasureTheory.L2.innerProductSpace`
at `𝕜 = ℝ` (`∫ ⟪f ξ, g ξ⟫_ℝ`), **not** `Inner.rclikeToReal ℂ`.  Consequences,
both verified by probe:

* `(inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y)` on `Lp ℂ 2 volume` is **not**
  `rfl` (probe E failed with a type mismatch);
* `real_inner_eq_re_inner` (Mathlib `InnerProductSpace/Basic.lean:959`) does
  **not** apply — it is stated for `Inner.rclikeToReal 𝕜 E`, and Lean reports the
  mismatch against `L2.instInner…` explicitly.

So the bridge needs either `MeasureTheory.integral_re`
(`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:164`) plus an
integrability side condition, or a direct re-proof of skew-adjointness in the real
`L2.inner_def`.  Nothing in tree does this: a grep over
`formalization/NSFormalization/Section4/` finds no real↔complex inner bridge on an
`Lp`/datum carrier.

**Fix:** one honest paragraph in the ATTEMPTS naming the instance path
(`Paper3.realSobolevInnerProductSpace` = `Submodule.innerProductSpace` over
`L2.innerProductSpace ℝ`, then `PiLp.innerProductSpace` for the `Fin 3` product)
and the chosen route.  Worth also recording the alternative the next worker may
prefer: state and prove the skew-adjointness *directly* on
`RealSobolevHilbert` / `angularDirectionalDerivativeReal` with the real
`L2.inner_def` and the same pointwise symbol argument (`angularDirectionalDerivativeReal_coe`,
`D01/DerivativeDatum.lean:141`, is `rfl`), which sidesteps the `re`/integral swap
entirely.  That is arguably the statement this lane should have delivered.

### F3 — Low.  Self-contradictory sentence in the module docstring.

**Location:** `formalization/NSFormalization/Section4/A04/LaplacianPairing.lean:33-35`:
"This module supplies step 1 (and step 2) only; steps 2/3 of the route … remain".
Steps 2 is both supplied and remaining.  **Fix:** "step 3 … remains".

### F4 — Low.  Mis-transcribed lemma in the pitfalls list.

**Location:** `ATTEMPTS_SL3_PAIRING.md` §"Pitfalls", 4th bullet: "`(angularWeightEquiv s).symm y
= angularWeightMap (-s) y` by `rfl` (`angularWeightEquiv_symm_apply`)".  The cited
lemma (`Paper3/AngularSobolevCoordinates.lean:288`) states
`(angularWeightEquiv s).symm k = angularWeightEquiv (-s) k`.  The `rfl` claim is
true either way (both unfold to `angularWeightMap (-s)`), but the transcription is
wrong.

### F5 — Low (cosmetic).  Missing doc comments.

`angularOrderLowering_eq_dilation_mid` (:133) and `angularOrderLoweringMid_coeFn`
(:139) carry no `/-- … -/`, unlike their directional counterparts (:55, :63).  No
linter complains; purely a symmetry nit.

### F6 — Info.  Namespace vs directory.

The new declarations land in `namespace NSFormalization.Paper3` from a
`Section4/A04/` module.  This matches the existing precedent
(`Section4/D01/DerivativeDatum.lean` defines `Paper3.angularDirectionalDerivative`
the same way), so it is consistent; flagged only because a `Paper3/`-directory
grep will not find these.

---

## Checks passed (the positive record)

### Statement fidelity (check 2)

* **The carrier is the right one; no weight is missing.**
  `Paper3.SobolevHilbert s` is an `abbrev` for `Lp ℂ 2 volume`
  (`SobolevHilbertModel.lean:21`) — the Sobolev order selects the *realization*
  (`angularRealization s`), never the norm.  On the manuscript side,
  `Source.RealSobolev.FourierData = Lp ℂ 2 volume` (`RealSobolev.lean:17`),
  `RealSobolevHilbert s = realSubspace s` (`:121`) is the conjugate-symmetric
  closed ℝ-subspace with the *induced* inner product, and
  `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s) = PiLp 2`
  (`Paper3/RealVectorPositiveDensity.lean:15`,
  `Source/FiniteHilbertBochner.lean:11`).  So the `H^m` inner product carries no
  extra Bessel weight — the weight is already inside the datum — and adjointness
  on the plain `Lp ℂ 2 volume` inner product **is** the `H^m` statement, modulo
  the real-restriction of F2 (`∑ⱼ re ⟪·,·⟫_ℂ` on the three components).

* **The factorization is a genuine, structural `rfl`.**  Read from the sources:
  `cyclesToAngular s := (angularWeightEquiv s).trans
  angularFrequencyDilation.toContinuousLinearEquiv`
  (`Paper3/AngularTameProduct.lean:11-12`), and
  `angularDirectionalDerivative s a := (cyclesToAngular (s-1)).toCLM.comp
  ((sobolevDirectionalDerivative s a).comp (cyclesToAngular s).symm.toCLM)`
  (`D01/DerivativeDatum.lean:62`).  Unfolding gives literally
  `U ∘ (W_{s-1} ∘ σ_a ∘ W_{-s}) ∘ U⁻¹`; the `s-1` and `-s` indices of
  `angularDirectionalMid` are *forced by the definition*, not a coincidence of
  `s`, and the same holds for `angularOrderLoweringMid` with `r`/`-s`.  The one
  non-obvious defeq — `(e.toContinuousLinearEquiv).symm` vs
  `e.symm.toContinuousLinearEquiv` — is `LinearIsometryEquiv.toContinuousLinearEquiv_symm`,
  a `rfl` at Mathlib `Analysis/Normed/Operator/LinearIsometry.lean:675-676`,
  exactly as the ATTEMPTS claims.

* **The sign is load-bearing; it is not true for the wrong reason.**  This was the
  sharpest question, so I ran it rather than argued it (probe file in `/tmp`, not
  committed).  Feeding the *identical* proof script to the false sign
  `⟪x, M_s y⟫ = ⟪M_s x, y⟫` reduces, after `simp only [RCLike.inner_apply, hy, hx]`
  and `rw [map_mul, mid_symbol_imaginary]`, to

  ```
  ⊢ σ ξ * y ξ * conj (x ξ) = -(σ ξ * y ξ * conj (x ξ))
  ```

  and `ring` fails ("The `ring` tactic failed to close the goal").  The false
  top-level sign likewise fails to typecheck against `inner_angularDirectionalMid`.
  So the `RCLike.inner_apply` orientation `⟪z,w⟫ = w * conj z` is not smuggling in
  a symmetric statement; the `conj σ = -σ` input is doing real work.  The operator
  is also visibly nonzero — `Paper3.angularRealization_directionalDerivative`
  (`D01/DerivativeDatum.lean:69`) shows it realizes the actual distributional
  `∂_a` — so skew- and self-adjointness genuinely cannot both hold.

* **Against the paper.**  eq:Rhigh is
  `paper/sections/appendix-a-local-theory.tex:132-137`; its dissipation term is
  `ν‖∇u‖²_{H^m}`.  Instantiating the delivered theorem at `g = D_a f` gives
  `⟪f, D_a D_a f⟫ = -⟪D_a f, D_a f⟫ = -‖D_a f‖²` — the correct sign and shape for
  `hlap`, whose consumer `inner_energy_assembly` accepts the `≤` weakening.

### Consistency (check 3)

* Single import, `NSFormalization.Section4.A04.LaplacianDatum`.  This is a
  `formalization/` module, not `Contracts/*`, so the contract import policy does
  not apply; `experiments/check_contracts.py` passes inside `make check`
  regardless.
* No restatement of any Paper3/D01 definition.  Every symbol
  (`angularWeightSymbol`, `sobolevDirectionalSymbol`, `sobolevBesselWeight`) and
  every operator (`angularWeightEquiv`, `sobolevDirectionalDerivative`,
  `sobolevOrderLowering`, `angularFrequencyDilation`) is used from upstream;
  the symbol facts come from `D01/DerivativeDatum.lean` §3.5.
* `angularDirectionalMid` / `angularOrderLoweringMid` are new.  A grep over
  `formalization/NSFormalization/` for a middle-operator definition or any prior
  adjointness lemma about these operators finds nothing — no mirror, no
  duplication.

### Honesty of ATTEMPTS (check 4)

Every cited declaration was opened at its cited line and matches:

| citation | verified |
|---|---|
| `Paper3.mid_symbol_imaginary` `DerivativeDatum.lean:183` | ✓ |
| `Paper3.lowering_symbol_real` `:175` | ✓ |
| `Paper3.cycles_symbol_imaginary` `:162`, `angularWeightSymbol_conj` `:169`, `weight_product_order_indep` `:192`, `mid_symbol_order_independent` `:207` | ✓ |
| `angularFrequencyDilation` `Paper3/AngularFourierDilation.lean:80` (a `≃ₗᵢ[ℂ]`) | ✓ |
| `SobolevHilbert` abbrev `Paper3/SobolevHilbertModel.lean:21` | ✓ |
| `⟪x,y⟫_𝕜` notation, Mathlib `InnerProductSpace/Defs.lean:86` | ✓ |
| `RCLike.inner_apply` = `y * conj x`, Mathlib `InnerProductSpace/Basic.lean:911`; `inner_apply'` the swap at `:915` | ✓ |
| `LinearIsometryEquiv.toContinuousLinearEquiv_symm` `rfl`, Mathlib `LinearIsometry.lean:675` | ✓ |

The three recorded pitfalls are all real:

1. **`RCLike.inner_apply` orientation** — confirmed verbatim in this Mathlib rev
   (`: ⟪x, y⟫ = y * conj x`, `@[simp]`, `rfl`).  Real hazard, correctly described.
2. **Do not blanket-`simp only [map_mul]`** — real.  `mid_symbol_imaginary` and
   `lowering_symbol_real` are both stated with `conj` of the *whole* triple
   product, so distributing `conj` over the three factors would leave no match.
   The single `rw [map_mul, …]` peels only the outer product, as claimed.
3. **`M_s` multiplication vs `U` change-of-variables** — real and the right design
   call; there is indeed no dilation coefficient function in tree, and
   `LinearIsometryEquiv.inner_map_map` makes one unnecessary.

Only F4 above is a transcription slip.

---

## Commands and results

All run inside `.claude/worktrees/076-A04-sl3-pairing`, after
`. scripts/lean-env.sh` and `export LEAN_NUM_THREADS=6`; `lake` only from
`verification/`, one process at a time.

1. `bash scripts/lean-install.sh` → exit 0 (idempotent, no reinstall).
2. `cd verification && lake build NSFormalization.Section4.A04.LaplacianPairing`
   → `Build completed successfully (9892 jobs).`, exit 0.  One replayed
   deprecation warning from **upstream** `Paper3/SobolevDirectionalDerivative.lean:103`
   (`SchwartzMap.smul_apply`), pre-existing, not from this module.
3. `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/LaplacianPairing.lean`
   → **empty output**, exit 0 (zero warnings, default heartbeat budget, no
   `set_option`).
4. `cd verification && lake env lean ../research/A04/axioms_sl3_pairing.lean`
   → all **10** declarations report exactly
   `[propext, Classical.choice, Quot.sound]`:
   `angularDirectionalMid`, `angularDirectionalDerivative_eq_dilation_mid`,
   `angularDirectionalMid_coeFn`, `inner_angularDirectionalMid`,
   `inner_angularDirectionalDerivative_right`, `angularOrderLoweringMid`,
   `angularOrderLowering_eq_dilation_mid`, `angularOrderLoweringMid_coeFn`,
   `inner_angularOrderLoweringMid`, `inner_angularOrderLowering`.
5. `grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats'
   formalization/NSFormalization/Section4/A04/LaplacianPairing.lean`
   → no match (exit 1).
6. `make check` → exit 0 (plan check, contract import policy, contract policy
   tests 13/13, work queue: "30 work items: ownership, contract registration and
   task cards consistent").
7. Reviewer probes, written to `/tmp/rev076/` only (nothing added to the repo):
   * false-sign falsification of `inner_angularDirectionalMid` and of
     `inner_angularDirectionalDerivative_right` → both fail as expected (F0-probe,
     reported under "Statement fidelity");
   * `#synth InnerProductSpace ℝ (Lp ℂ 2 volume)` → `L2.innerProductSpace`;
     `#synth InnerProductSpace ℝ (RealSobolevHilbert 1)` →
     `realSobolevInnerProductSpace 1`;
   * `(inner ℝ x y : ℝ) = RCLike.re (inner ℂ x y)` by `rfl` → **fails**;
     `real_inner_eq_re_inner ℂ` → **does not apply** (instance mismatch).  This is
     the evidence for F2.

---

## Is step 3 ready to brief?

Not quite — it needs one more pass before a worker should be turned loose on it.
What the plan gets right is the shape: the Laplacian datum really is assembled by
`isSobolevDatum_partialDeriv` twice plus `D01.isSobolevDatum_add` over the three
directions, the right-hand side really is
`A04.gradientSobolevENorm_toReal_sq_eq_datum_sum`, `≤` really does suffice because
`inner_energy_assembly` weakens with `0 ≤ ν`, and the operator-order bookkeeping
really is vacuous by `mid_symbol_order_independent`.  Those four claims I checked
and they hold.

What is missing is precisely the part that is *not* bookkeeping.  After
skew-adjointness fires, the two sides sit at different **datum** orders
(`⟪D_j datum_m u, D_j datum_{m+2} u⟫` against `‖D_j datum_{m+1} u‖²`), and closing
that is where `inner_angularOrderLowering` — this lane's second deliverable, which
the record files under "optional" — has to be used, together with datum uniqueness
and an order-independence (or commutation) lemma for the lowering multiplier that
nobody has written yet (F1).  Separately, the `re` step is a real obstacle rather
than a bookkeeping clause: the real inner product on this carrier is
`L2.innerProductSpace` at `𝕜 = ℝ`, not `rclikeToReal ℂ`, so neither `rfl` nor
`real_inner_eq_re_inner` gets you from the delivered complex theorems to `hlap`
(F2).  A worker briefed only by the current last section would discover both of
these the hard way, and would plausibly conclude — correctly — that the *real*
statement on `angularDirectionalDerivativeReal` should have been the deliverable.

Recommendation: merge as is (the Lean is right and the scope was honestly bounded),
and fold F1 + F2 into the ATTEMPTS' last section before the step-3 lane is opened.
Size estimate for step 3 after that rewrite: **M**, not S–M.
