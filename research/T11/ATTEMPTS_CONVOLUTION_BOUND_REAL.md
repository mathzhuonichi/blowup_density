# ATTEMPTS — lane 328 (T11 / U9d1a): real-order convolution bound

Target: generalize lane 317's `H³ × H³ → H²` projected-convection bound to every real
order `r ≥ 3`. No named input was allowed for this lane; none was introduced.

## Route taken (worked)

1. **Real-exponent Peetre.** `weightR_le_max : W k ≤ 4 * max (W l) (W (k-l))` from
   `Paper1.PeriodicWeightShift.weight_add_le l (k-l)` (`W k ≤ 2 (W l + W (k-l) - 1)`) plus
   `a + b ≤ 2 max a b`; then `Real.rpow_le_rpow` + `Real.mul_rpow` + a `max_cases` split give
   `weightR_peetre : W k ^ r ≤ 4 ^ r * (W l ^ r + W (k-l) ^ r)` for every real `r ≥ 0`.
   The constant `4` is sharp for this route (`k = 2m`, `l = m` has `W(2m)/W(m) → 4`).
2. **Summability.** `W ≥ 1` and `-r ≤ -3` give `W ^ (-r) ≤ W ^ (-3)` by
   `Real.rpow_le_rpow_of_exponent_le`; comparison with the existing
   `Paper1.PeriodicInverseWeightSummable.summable_weight_rpow_neg_three` (already in `rpow`
   form — no new lattice work was needed).
3. Everything else is lane 317's argument verbatim with `^ (3 : ℕ)` replaced by real `rpow`:
   `(x ^ (a/2)) ^ 2 = x ^ a` is isolated once as `weightR_half_sq`, and
   `W ^ a * W ^ b = W ^ (a+b)` as `ofReal_weightR_mul`, which keeps the kernel algebra to `ring`.
4. **Order transport.** One lemma does both jobs: `torusConvectionSymbolReal_reweight` proves
   that on reweighted data the order-`r'` symbol is `W(k)^((r'-r)/2)` times the order-`r` symbol
   (termwise inside the `tsum`, `reweight_pair`). Instantiating `r := 3` and pulling the
   order-three reweight through `persistenceDown r 3 hr` (lane 319) gives the coefficient
   identity against lane 317's `torusProjectedConvectionSymbol`; instantiating generally gives
   the reweighting-compatibility lemma `torusConvolutionCLM_real_reweight`.

## Obstacle hit and how it was handled (the only one)

**Elaborating the nested bilinear type at the index `r - 1` does not terminate.** Writing

```lean
def f (r : ℝ) : Type := PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev r →ₗ[ℝ] PeriodicSobolev (r-1)
```

fails with

```
error: failed to synthesize
  MulAction ℝ ↥(PeriodicSobolev (r - 1))
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

Measurements (scratch files, all with the two local `NormedAddCommGroup`/`NormedSpace` instances):

| shape | result |
|---|---|
| `PeriodicSobolev 3 →ₗ PeriodicSobolev 3 →ₗ PeriodicSobolev 2` (literals) | OK |
| `PeriodicSobolev r →ₗ PeriodicSobolev (r-1)` (single arrow) | OK |
| `PeriodicSobolev r →ₗ PeriodicSobolev r →ₗ PeriodicSobolev t` (two free vars) | OK |
| `PeriodicSobolev r →ₗ PeriodicSobolev r →ₗ PeriodicSobolev (r-1)` | **fails** |
| the same with `synthInstance.maxHeartbeats 200000`, `maxHeartbeats 400000` | **still fails** |
| the same with parameterless local instances | **still fails** |
| the same with an extra `local instance (s) : Module ℝ (PeriodicSobolev s)` | **still fails** |
| `PeriodicSobolev r →ₗ PeriodicSobolev r →ₗ PeriodicSobolev (outOrd r)`, `outOrd r := r - 1` opaque | OK |

Diagnosis: `PeriodicSobolev` is a phantom `abbrev` for `realPeriodicSubmodule`, so the instances
for the two indices are interchangeable, and the nested `LinearMap`/`ContinuousLinearMap` module
instances make the elaborator test `r =?= r - 1`; `whnf` on `Real` subtraction is what diverges.
Two free variables (`r`, `t`) or an opaque `outOrd r` fail that test immediately, which is why
those shapes elaborate.

Resolution, with no weakening of any statement: the bundled map is built as
`torusConvolutionCLM_realAt (r t : ℝ) (hr : 3 ≤ r) : PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev t`,
and the lane's object is `torusConvolutionCLM_real r hr := torusConvolutionCLM_realAt r (r-1) hr`,
whose inferred type is `… →L[ℝ] … →L[ℝ] PeriodicSobolev (r-1)` (instantiation, not a fresh search).
The index is recorded in the source by
`example (r) (hr) (A B : PeriodicSobolev r) : PeriodicSobolev (r-1) := torusConvolutionCLM_real r hr A B`,
which elaborates (single-level type). All *unbundled* statements — `torusConvectionDatumReal`,
`torusProjectedConvectionDatumReal`, their coefficient identities and their norm bounds — are stated
directly at the honest index `r - 1`.

## Rejected / not needed

- `(a+b)^s ≤ 2^(s-1)(a^s+b^s)` (real convexity) would give `2^(2r-1)` instead of `4^r = 2^(2r)`
  in the Peetre constant, i.e. exactly lane 317's `32` at `r = 3` instead of `64`. Not worth a
  convexity lemma: no optimality is claimed for the constant, as at order three.
- Re-deriving lattice summability of `W^(-r)` from scratch: unnecessary, the `rpow` form of the
  inverse-cube theorem was already in `Paper1/PeriodicInverseWeightSummable.lean`.
- Re-using lane 317's private helpers (`scalar_energy`, `product_energy`, `datum_ext`, …): they are
  `private`, so they are re-proved here verbatim under `…R` names. The two local instances are
  renamed (`convolutionRealNormedGroup/Space`) to avoid the same-namespace clash recorded in
  `logs/LESSONS.md` for anonymous/duplicated instance names.

## Residual

None for this unit's statement. What is *not* claimed: no optimality of
`torusConvolutionConstant_real`, no `r < 3`, and no statement about the two-space Picard contract
at orders other than three (`torusTwoSpaceContract_nonempty'` stays an order-three object; the
order-`r` map re-discharges `TorusConvolutionInput` through `torusConvolutionInput_ofReal`).
