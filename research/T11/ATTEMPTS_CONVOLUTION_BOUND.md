# 317 / U9c — convolution bound attempts

## Result

`torusConvolutionInput : TorusConvolutionInput` is proved unconditionally.
No residual named input. The exact projected convolution is realized on the
complete real H³/H² carriers, with no solenoidality or finite-support premise.

## Search and route

Read the binding split (§0–§4), reconciliation (§0–§3), implementation candidates,
existence route, canonical symbols, and the named-instance lesson.
The mandated `grep -rn` covered `Paper1/Periodic*.lean`, all `Section3/`,
`Section4/{A01,A02,A04,D01}`, and `vendor/HeliCorgi/Formal/`.
It found finite-support discrete/weighted Young estimates, the full lattice
`PeriodicInverseWeightSummable.summable_inverse_weight_cube`, the weight-shift
inequality, and the canonical Leray contraction. No claim that these ingredients
were absent was made. The whole-space Young results have different carriers.

The proof avoids extending finite-support Young estimates. Set

```
W(k) = 1 + 4π² ∑ᵢ kᵢ²
K(j,k,l) = W(k) ‖periodicDerivativeSymbol j k‖ W(l)^(-3/2) W(k-l)^(-3/2)
D = 64 * ∑' k, (W(k)^3)⁻¹
```

1. `‖periodicDerivativeSymbol j k‖² ≤ W(k)` and
   `W(k)^3 ≤ 32 * (W(l)^3 + W(k-l)^3)` give
   `K(j,k,l)^2 ≤ 32 * ((W(l)^3)⁻¹ + (W(k-l)^3)⁻¹)`.
2. The inverse-cube theorem and `l ↦ k-l` give `∑' l, K(j,k,l)^2 ≤ D`.
3. Cauchy–Schwarz (`lp.tsum_mul_le_mul_norm`, exponents 2 and 2) yields
   `‖scalarConvection a b j k‖² ≤ D * ∑' l, ‖a l‖² * ‖b(k-l)‖²`.
4. The bijection `(k,l) ↦ (l,k-l)` makes the sum of the right-hand product
   exactly `D * ‖a‖² * ‖b‖²`. Summability is proved before each comparison.
5. Sum the three tensor entries and three output components. The convenient
   vector bound is `9 * sqrt D * ‖A‖ * ‖B‖` (not an optimal constant).
6. Conjugation and `l ↦ -l` prove the real submodule condition. Reuse the
   canonical Leray contraction. Prove both additivity and both real homogeneity
   identities, then apply `LinearMap.mkContinuous₂`.

## Actual failed elaborations and fixes

- Dependency cache initially lacked `LocalExistence.olean`:
  `error: object file '.../Section3/T11/LocalExistence.olean' of module NSFormalization.Section3.T11.LocalExistence does not exist`.
  Built the canonical dependency closure from `verification/`.
- A cast around a real power was insufficient:
  `failed to synthesize instance of type class HPow ℂ ℝ ?m.21`.
  Fixed by explicitly typing the real power as `ℝ` before casting to `ℂ`.
- Guessed theorem names were rejected:
  `Unknown identifier tsum_mul_le_Lp_mul_Lq`, `Unknown identifier star_tsum`,
  `Unknown constant lp.coe_sum`.
  Actual APIs are `lp.tsum_mul_le_mul_norm`, `Complex.conj_tsum`, and `lp.coeFn_sum`.
- Inferring the function in `Summable.comp_injective` exhausted even a local
  400000-heartbeat diagnostic attempt:
  `(deterministic) timeout at whnf, maximum number of heartbeats (400000) has been reached`.
  Supplying `(i := fun p : PeriodicFrequency × PeriodicFrequency ↦ (p.2,p.1-p.2))`
  fixed the problem; that declaration now uses the default heartbeat limit.
- Rewriting through the nested `lp` coercion reported:
  `The target expression is not type-correct under the implicit transparency level`.
  Used explicitly typed functions and equality transitivity for `Equiv.tsum_eq`.
- `leray_exists_contraction` was not imported transitively:
  `Unknown identifier leray_exists_contraction`.
  Added the canonical `Section3.T10.Leray` import to the new module.
- Strict message whitespace rejected four axiom messages despite identical
  axiom sets: `Docstring on #guard_msgs does not match generated message`.
  Used the existing lane convention `#guard_msgs (whitespace := lax)`.
- A temporary attempt to print imported private declarations by a textual name
  containing `.0.` failed with `unexpected token '.'; expected command`.
  Private declarations were first inspected inside a temporary source copy.
  The committed conformance file invokes the built-in `#print axioms` command
  with `Lean.mkIdent` and the actual numeric name component, auditing all 42
  named declarations. `run_elab` initially gave `CommandElabM Unit` versus
  `TermElabM Unit`; `run_cmd` is the correct command elaboration context.

Only `torusConvectionDatum_norm_le` uses a commented declaration-local
`maxHeartbeats 400000`, for nested finite-vector/lp norm elaboration. No global
heartbeat change, admissions, extra axioms, or unchecked decision procedure.

## Non-vacuity

The module and probe exhibit two nonzero constant-mode data with
`torusConvolutionCLM A B = 0`, and the probe instantiates the exact two-space
contract at viscosity 1. These are tests of the constructed map, not assumptions
used to prove its global bound. All input pairs, including nonconstant modes,
are covered by the unconditional coefficient identity.
