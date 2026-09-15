# A04 unit G1 — sub-lemma SL3 (dissipation identity on the datum carrier)

Lane 066, task A04, sub-lemma SL3 of `research/A04/G1_SPLIT.md` (§ "SL3 — Laplacian /
dissipation identity", :127-150).  Target: `hlap : ⟪G t, L⟫ ≤ -(gradientSobolevNormAt m u t)²`
in `RealVectorSobolev (m:ℝ)`, the hypothesis `A04.inner_energy_assembly` consumes.

Line citations below were re-checked after the review revisions (they were off by +10..+16 in
the first draft, then shifted again by the symbol lemmas added in §"What closed").

## Modules produced (build clean, `sorry`-free, standard axioms only)

- `formalization/NSFormalization/Section4/D01/DerivativeDatum.lean` (new; the ∂ⱼ-datum
  step, **shared with D01/P2** — placed in D01 as the split allows).
- `formalization/NSFormalization/Section4/A04/LaplacianDatum.lean` (new; SL3-specific:
  `gradientSobolevNormAt` and the gradient identification).
- `research/A04/axioms_sl3.lean` — `#print axioms` audit over **all 21 public declarations** of
  the two modules; each depends only on `propext, Classical.choice, Quot.sound`.

Build: `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.DerivativeDatum NSFormalization.Section4.A04.LaplacianDatum` → `Build completed successfully`.  `lake env lean` on each module gives **empty output** (zero warnings), at the **default** heartbeat budget (no `set_option`).

## What closed

### Plan step 1 — the derivative datum (route (i), the multiplier CLM). CLOSED.

The order-`m` datum of `∂ⱼz` is a fixed bounded Fourier multiplier of the order-`(m+1)`
datum of `z`, the multiplier by the angular symbol `iξⱼ(1+‖ξ‖²)^{-1/2}`.  The operator is the
existing cycles CLM `Paper3.sobolevDirectionalDerivative` (symbol `2πi⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}`)
conjugated by `Paper3.cyclesToAngular`, the `angularOrderLowering` template.

- `Paper3.angularDirectionalDerivative (s) (a) : Lp ℂ 2 →L[ℂ] Lp ℂ 2` (`DerivativeDatum.lean:62`).
- `Paper3.angularRealization_directionalDerivative` (`:69`):
  `angularRealization (s-1) (D h) = ∂_{a}(angularRealization s h)` — realization of the
  physical distributional derivative, transported from `sobolevRealization_directionalDerivative`.
- `Paper3.angularDirectionalDerivativeReal (s) (a) : RealSobolevHilbert s →L[ℝ] RealSobolevHilbert (s-1)`
  (`:134`) — the real-restricted CLM, plus `angularDirectionalDerivativeReal_coe` (`:141`).
- `D01.isSobolevDatum_partialDeriv` (`:245`): for a smooth square-integrable field `Z`
  (`EulerLpTranslation.SmoothL2Field`, the `ClassicalSolutionR` slice class) and any
  order-`(m+1)` angular datum `A` of `Z.field`,
  `IsSobolevDatum m (A03.partialDeriv j Z.field) (WithLp.toLp 2 fun i => angularDirectionalDerivativeReal (m+1) eⱼ (A i))`.
  Proof via `angularRealization_directionalDerivative` + `D01.angularRealization_of_isSobolevDatum`
  (`:232`, the datum realizes the physical distribution) + `physicalDistribution_directionalField`
  + `componentField_directionalField`.  This is `datum_m(∂ⱼz) = (iξⱼ(1+‖ξ‖²)^{-1/2})·datum_{m+1}(z)`.

### Symbol facts for the next SL3 lane (added on review). CLOSED, machine-checked.

Writing `angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹` (`U = angularFrequencyDilation`
unitary; `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` three multiplications), the pointwise symbol facts the
pairing identity needs are now in tree, in `DerivativeDatum.lean`:

- `Paper3.cycles_symbol_imaginary` (`:162`): `conj σ_a(ξ) = -σ_a(ξ)` — pure imaginarity of the
  cycles directional symbol (the fact skew-adjointness needs; see Snags).
- `Paper3.mid_symbol_imaginary` (`:183`): the directional **middle** symbol is purely imaginary
  → `angularDirectionalDerivative` is `L²`-skew-adjoint.
- `Paper3.lowering_symbol_real` (`:175`): the order-lowering middle symbol is real →
  `angularOrderLowering` is `L²`-self-adjoint.
- `Paper3.mid_symbol_order_independent` (`:207`, via `weight_product_order_indep` `:192`): the
  directional middle symbol does not depend on the order, so all `angularDirectionalDerivative s a`
  are the *same* map.
- helper `Paper3.angularWeightSymbol_conj` (`:169`): the angular Bessel weight symbol is real.

### Plan step 3 — the dissipation norm def and the gradient identification. CLOSED.

- `A04.gradientSobolevNormAt (s) (u) (t)` (`LaplacianDatum.lean:87`): restates
  `research/A04/Spec.lean:190` over the local `A03.gradientSobolevENorm`
  (`columnsSobolevENorm s (fun j => partialDeriv j v)`, definitionally
  `Contracts.V1.TameProduct.gradientSobolevENorm`).
- `A04.gradientSobolevENorm_toReal_sq_eq_sum` / `gradientSobolevNormAt_sq_eq_sum`
  (`:96`, `:112`): `‖∇z‖²_{H^s} = ∑ⱼ ‖∂ⱼz‖²_{H^s}` (real `.toReal`, finiteness hypothesis).
- `A04.gradientSobolevENorm_toReal_sq_eq_datum_sum` (`:130`): the identification **in operator
  terms** — `‖∇Z‖²_{H^m} = ∑ⱼ ‖angularDirectionalDerivativeReal (m+1) eⱼ (A)‖²`, i.e. the
  right-hand side `-∑ⱼ ‖D_j(datum_{m+1} u)‖²` of the dissipation identity, through the ∂ⱼ datum
  of step 1.  On review, `hfin` is now **derived internally** from `hA` (a datum norm is never
  `⊤`, `enorm_ne_top`), and the final step uses `toReal_enorm`; this compiles at the **default**
  heartbeat budget, so the earlier `set_option maxHeartbeats 400000` is gone.

## How reality preservation was handled

The multiplier maps the conjugate-reflection real subspace `Source.RealSobolev.realSubspace`
to itself because the symbol is odd and purely imaginary:

- `Paper3.conj_sobolevDirectionalSymbol_neg` (`:83`): `conj(σ_a(-ξ)) = σ_a(ξ)` — the odd ×
  imaginary combination, which is exactly what reality preservation needs.  (This is **weaker**
  than pure imaginarity at a point; the pointwise `conj σ = -σ` that skew-adjointness needs is
  the separate `cycles_symbol_imaginary` `:162`.)  Proof: `inner_neg_left`, `Complex.conj_I`,
  `Complex.conj_ofReal`, `map_ofNat`, then `ring`.
- `Paper3.realSymmetry_sobolevDirectionalDerivative` (`:91`): the cycles operator commutes with
  `realSymmetry`, by `sobolevDirectionalDerivative_coeFn` pulled back through
  `measurePreserving_neg`, the `realSymmetry_sobolevOrderLowering` template.
- `Paper3.realSymmetry_angularDirectionalDerivative` (`:112`) transports to the angular operator
  via `cyclesToAngular_realSymmetry` and `cyclesToAngular_symm_realSymmetry` (`:104`).
- `Paper3.angularDirectionalDerivative_mem_realSubspace` (`:124`) codRestricts to
  `angularDirectionalDerivativeReal`.

## Snags (negative examples)

- **`map_ofReal` is not a lemma name.**  `#check @map_ofReal` → `unknownIdentifier`.  For
  `conj (↑r : ℂ) = ↑r` use `Complex.conj_ofReal`, and `conj (2 : ℂ) = 2` is `map_ofNat`.
  (`DerivativeDatum.lean:85-86`, `:164`.)
- **`norm_num` silently collapses `x ^ (2:ℝ)` to `x ^ (2:ℕ)`.**
  `example (x : ℝ) : x ^ (2:ℝ) = x ^ (2:ℕ) := by norm_num` succeeds.  So in the gradient
  reduction the `← Real.rpow_natCast (…) 2` guard is placed **before** the bare `norm_num`
  (`LaplacianDatum.lean:99-101`), and the per-term step then uses `ENNReal.toReal_pow` on the
  resulting `ℕ`-power.  (Upstream `AngularFourierDilation.lean:70` handles the same hazard.)
- **`whnf` heartbeat overshoot on a phantom order.**  In
  `gradientSobolevENorm_toReal_sq_eq_datum_sum`, closing the per-term goal with
  `← ofReal_norm` + `ENNReal.toReal_ofReal (norm_nonneg _)` overshot the default budget by
  <0.5 % (the reviewer bisected: FAIL at 200100, OK at 201000): `norm_nonneg _` leaves the
  carrier's `NormedAddCommGroup` instance as a metavariable, and reconciling it against the datum
  term's instance forces a delta-unfold of `realSubspace` (which ignores its order argument, so
  `(m:ℝ)+1-1 =?= (m:ℝ)` fails first-order).  The first draft masked it with
  `set_option maxHeartbeats 400000`; the reviewer's fix removes both the `set_option` and the
  redundant `hfin` hypothesis, replacing the two rewrites by the one-shot
  `toReal_enorm : ‖x‖ₑ.toReal = ‖x‖` — compiles at the default budget.  (Typed-`have` and
  dropping the statement's type ascription do **not** help; only `toReal_enorm` / a trailing
  `simp` do.)
- **`ring` prints "Try this: ring_nf" (non-fatal) when `ring1` fails but `ring_nf` closes.**
  The two order/regrouping steps in the symbol lemmas emitted this note (exit 0, but noisy).
  Replaced `ring` by explicit `mul_mul_mul_comm` / `mul_right_comm` there so `lake env lean` on
  the module is truly empty.

## What remains (the SL3 gap — corrected per review; size S–M)

The full `hlap` needs the **pairing identity** `⟪G t, L⟫ = -∑ⱼ ‖D_j(datum_{m+1} u)‖²`
(≤ suffices — `inner_energy_assembly` weakens `hlap` to `≤` with `0 ≤ ν`).  The RHS is already
delivered (`gradientSobolevENorm_toReal_sq_eq_datum_sum`); the LHS pairing reduces to:

1. **Skew-adjointness of `angularDirectionalDerivative`** on `L²`, `⟪a, D_j b⟫ = -⟪D_j a, b⟫`.
   Do it on the **middle** operator `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` only: its a.e. coefficient
   function is the product of the **three existing** `_coeFn` lemmas — `angularWeightMap_coeFn (s-1)`,
   `sobolevDirectionalDerivative_coeFn s a`, `angularWeightMap_coeFn (-s)`
   (`= (angularWeightEquiv s).symm`) — the middle symbol is purely imaginary by
   `Paper3.mid_symbol_imaginary` (now in tree), and `MeasureTheory.L2.inner_def` +
   `integral_congr_ae` finish.  Then transport across the unitary `U = angularFrequencyDilation`
   with `LinearIsometryEquiv.inner_map_map`.  **No a.e. coefficient function of the dilation is
   needed** — there is none in tree and it would be an awkward change of variables; the first
   draft wrongly proposed chasing it.  Size **S–M**; this is the only genuinely new analytic step.
2. **Self-adjointness of `angularOrderLowering`** (real middle symbol,
   `Paper3.lowering_symbol_real`), the same way.  Size **XS** given step 1.
3. **Laplacian datum** `datum_m(Δu) = ∑ⱼ D_j(D_j(datum_{m+2} u))`, from
   `isSobolevDatum_partialDeriv` (twice, via `partialDeriv j Z.field = (Z.directionalField eⱼ).field`)
   + datum additivity `D01.isSobolevDatum_add`.  **There is no order bookkeeping**: by
   `Paper3.mid_symbol_order_independent` all `angularDirectionalDerivative s a` are the same map,
   so orders `m/m+1/m+2` never diverge (the first draft wrongly called this "intricate / genuinely
   different maps").  Size **M**.
4. Real-subspace `re` and `PiLp 2` componentwise-sum bookkeeping.  Size **S–M**.

**Overall size S–M**, not the L the first draft implied.  Template:
`Source/OrdinaryViscousStability.lean:32` proves the **order-0** identity in exactly this shape
(`laplacian_pairing`; `laplacian_pairing_nonpos` is the `≤` form) on the jet carrier from a
physical integration by parts — the sanity target for step 3 (it does not transport to order `m`,
since the datum-carrier norm is the `H^m` norm, not `L²`).  Nothing is blocked on unowned upstream;
all inputs are on `erenup/integration`.

**Divergence from `G1_SPLIT.md` (recorded for the split's owner):** §SL3 recommends the
"pin-the-representative" route (`A03.representative_ae` + `angularRealization_boundedRepresentative`).
The symbol/adjointness route above is the better one — the datum-carrier inner product *is* the
angular `L²` inner product of Fourier data, so "integration by parts" there is literally "the
symbol is imaginary" — but the divergence should be reflected back into `G1_SPLIT.md`.

## Commands run

- `bash scripts/lean-install.sh` → `== OK`.
- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.DerivativeDatum NSFormalization.Section4.A04.LaplacianDatum` → `Build completed successfully (9891 jobs)`; `lake env lean` on each module → empty.
- `cd verification && lake env lean ../research/A04/axioms_sl3.lean` → 21 declarations, each `[propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0.
