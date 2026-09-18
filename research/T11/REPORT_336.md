# REPORT 336 — T11 U12b, the tame pairing bound (and `higherOrderBound` closed)

Lane `336-T11-U12b-pairing-bound`, branch `erenup/336-T11-U12b-pairing-bound`
(based on integration + lanes 322/327/328 + **merged lane 335**, needed for
`convectionFieldT` / `torusGradientNormAt` / `higherOrderBound_of_pairingBound`).
**Complete, unconditional.** No `sorry`, no axiom, no named `Prop` input.

## 1. 证了哪个定理 (what was proved)

**Main.** `NSFormalization.Section3.T11.torusPairingBound_advection` — the tame
estimate at the pairing level, in the exact spelling lane 335 consumes:

> for `m ≥ 3`, a velocity slice `u(t,·)` with order-`m` datum `Gm`, order-`(m+1)`
> datum `Gm1`, and with `Nm` the order-`m` datum of the **physical advection**
> `convectionFieldT u = (u·∇)u`,
> `|⟪Gm, Nm⟫_{H^m}| ≤ C(m) ‖u(t)‖_{H²} ‖u(t)‖_{H^m} ‖∇u(t)‖_{H^m}`,
> `C(m) = torusPairingConstant m = 15 · 4^{m/2} · (∑ₖ (1+4π²|k|²)^{-2})^{1/2}`.

`torusPairingBound_slice` is the same with the convolution identity discharged
from smoothness and periodicity of the slice; `torusPairingBound_classical` is
lane 335's `hpair` **verbatim**; and

**`torusHigherOrderBound` is the `higherOrderBound` field of
`PeriodicContinuationAPI` (`research/T11/probes/api_on_canonical.lean:112-121`),
proved unconditionally** — lane 322 reduced it to `eq:Rhigh`, lane 335 reduced
`eq:Rhigh` to the pairing bound, and this lane proves the pairing bound.

**Also proved, unconditionally:**

| theorem | content |
|---|---|
| `torusInverseWeight_summable` | `∑ₖ W(k)^{-r} < ∞` for **every real `r > 3/2`**; the tree only had `r = 3`, and `r = 2` is what makes the `H²` low factor (rather than `H³`) legitimate |
| `torusTrilinearConvolution` | `∑_{k,l} X(k)Y(l)β(k-l) ≤ ‖X‖_{ℓ²}‖Y‖_{ℓ²}‖β‖_{ℓ¹}` on `Z³ × Z³` — one Cauchy–Schwarz against the convolution measure |
| `torusWeightPeetre` | Peetre `W(k)^a ≤ 4^a(W(l)^a + W(k-l)^a)` at a real exponent |
| `torusWeightPeetre_grad` | Peetre **with one derivative**: `W(k)^a|2π(k-l)| ≤ 4^a(W(l)^a|2πl| + W(k-l)^a|2π(k-l)|)` — the region split `\|l\| ≤ \|k-l\|` vs `>`, and the only reason the third factor is `‖∇u‖_{H^m}` and not `‖u‖_{H^{m+1}}` |
| `velocityCoeffT_advection` | the Fourier coefficient of `(u·∇)u` is `∑ⱼ ∑ₗ û ⱼ(l)·2πi(k-l)ⱼ·û ᵢ(k-l)` (convolution theorem + derivative rule) |
| `advection_component` | `(u·∇)uᵢ = ∑ⱼ uⱼ ∂ⱼuᵢ` |
| `torusPairingBound(_nat, _of_reweights, _enorm, _profile)` | the companion estimate for lane 328's canonical (divergence-form) convection datum, third factor `‖u‖_{H^{m+1}}`, on the carrier and in `periodicSobolevENorm` / `torusSobolevNormAt` |
| `torusProjectedPairing_eq`, `torusProjectedPairingBound` | the Leray projector does not change the pairing against a solenoidal datum, so the bound transfers to the projected convection datum |
| `torusRealPairing_comm`, `torusRealPairing_sub` | the two algebraic facts about lane 322's pairing that the projection argument needs |

The divergence-free cancellation `⟪(u·∇)v, v⟫_{L²} = 0` is **not** used anywhere.

## 2. Lean 里现在有什么 (what is in Lean now)

* `formalization/NSFormalization/Section3/T11/PairingBound.lean` — 1751 lines,
  33 named declarations (31 public + 2 named local instances) and 30 private
  helpers, namespace `NSFormalization.Section3.T11`.  New imports beyond T11:
  none (it imports `ConvolutionBoundReal` and lane 335's `EnergyIdentity`).
* `research/T11/probes/pairing_bound_closes.lean` — lane 335's `hpair` and the
  `higherOrderBound` field copied **verbatim** and discharged; the older
  `hRhigh`-nonlinear-term and reweight shapes; and a non-vacuity block at the
  nonzero solenoidal shear datum `2 e₂ cos(2πx₀)` (two conjugate modes `±(1,0,0)`)
  where the right-hand side is strictly positive and the projected form applies.
* `research/T11/axioms_pairing_bound.lean` — `#guard_msgs`-checked `#print axioms`
  for all 33 named declarations, each exactly
  `[propext, Classical.choice, Quot.sound]`.
* `research/T11/ATTEMPTS_PAIRING_BOUND.md` — route, reuse audit, every failed path
  with its exact error text, the lane-335 course correction, and what is not
  delivered.

Nothing existing was modified; no contract, binding or test was touched.

## 3. 缺口是什么 (the gap)

None in the sense of assumptions: every statement is unconditional.  What is not
delivered (full detail in `ATTEMPTS_PAIRING_BOUND.md` §3b):

1. **No optimality** of `C(m) = 15·4^{m/2}·(∑ W^{-2})^{1/2}`.
2. The `ℓ¹` step is exported only at `H²`, although
   `torusInverseWeight_summable` proves the ingredient for every `r > 3/2`.
3. `torusProjectedPairingBound` needs a solenoidal partner datum (the
   unprojected and advection forms need nothing).
4. The advection form and lane 328's divergence form are proved separately and
   are not identified with each other (they agree for solenoidal `u`); nothing
   downstream needs the identification.

A warning worth carrying forward: `‖u‖_{H^{m+1}}` and `‖∇u‖_{H^m}` are **not**
interchangeable in `eq:Rhigh` (they differ by the zero mode), so a pairing bound
proved with the additive Peetre inequality alone does not discharge `hpair`.  The
region split is what supplies the gradient norm.

## 4. 跑了什么命令、什么结果 (commands and results)

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PairingBound
  → ✔ [9995/9995] Built … Build completed successfully (0 errors, 0 warnings from this module)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/PairingBound.lean
  → clean (no output)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/pairing_bound_closes.lean
  → clean: `hpair` and `higherOrderBound` close verbatim, non-vacuity holds
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_pairing_bound.lean
  → clean: 33 #guard_msgs axiom prints all match
make check   (worktree root)
  → architecture checks OK; test_contract_policy 13/13 OK;
    check_work_queue: 45 work items consistent
```

Axiom audit: all 33 named declarations print exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`/`admit`/`axiom`/
`native_decide`; no `set_option maxHeartbeats` anywhere in the module.

## Review corrections (codex, ACCEPT-WITH-NOTES)
Per `research/T11/REVIEW_336-T11-U12b-pairing-bound.md` §3: the inverse-weight summability "not in tree" claim is qualified (the tree had the `r = 3` case); the private-helper count is 59 (the report said 30); the only missing bridge is the coefficient-carrier identification of the advection and divergence forms (nothing downstream needs it). Lean content unchanged.
