# Lane 204 — signed energy passage

The exact imported `CylinderSignedEnergyPassage` is now proved for general
solenoidal data, without another analytic hypothesis. Existing Lean modules
are unchanged. Only the requested envelope/limit row of A3_SPLIT is updated.

## Successful proof

1. `regularized_full_energy_hasDerivAt` supplies the derivative of the full
   squared word norm, with coefficient **−2ν** on the entire gradient square.
   `signed_transport_zero` specializes the finite-Sobolev metric transport
   theorem to the identity metric, whose first coefficient bound is zero.
   `signed_source_pairing_le` uses the regularized divergence and pressure
   constraints, pressure orthogonality, and family Cauchy–Schwarz. Its forcing
   is exactly the source-plus-transport-plus-pressure family, without hFB.
2. `signed_scalar_integral` divides by the positive epsilon-regularized root
   and applies FTC with derivatives only in the interior. The finite-level
   theorem retains **−ν**, covers t=0 and t=T, and proves integrability.
3. `signedApproximationRoot_tendsto` uses the vendor's uniform value-family
   convergence. `signedApproximationForcing_tendsto` supplies the actual
   source and pressure restrictions from lane 198 for the SAME U, then uses
   `regularizedWeightedForcing_tendsto`. The varying coefficient
   r_n/sqrt(r_n²+ε²) converges uniformly. Subinterval L² pairings pass its
   product with the strong forcing limit to the integral.
4. `signed_scalar_multiplier_tendsto` proves joint continuity of a varying
   continuous scalar weight acting on L². The key estimate is
   `norm((M c_n)v_n − (M c)v_n) ≤ norm(c_n−c) * norm(v_n)`.
   The norm map is Lipschitz on L². A subinterval pairing of the weighted norm
   with the norm therefore proves `signed_weighted_square_limit`, including
   integrability of the limiting weighted square.
5. `signedGradientOperator` collects every word and its four first derivatives
   into a genuine `PiLp 2` family. The finite regularized dissipation is its
   squared norm on `maximalApproximation`. The limiting squared norm is
   `energyGradientNorm U` squared a.e., including the explicit reindexing of U.
   The finite-level coordinates prepend a direction; the target appends one.
   `Fin.consEquiv` and `Fin.snocEquiv` show these enumerate the same full family
   at each order. Thus the sum is EXACT, with no comparison constant or dropped
   coordinate. No derivative-commutation assumption is needed.
6. Apply the weighted-square theorem to the uniformly convergent inverse-root
   paths and the strongly convergent gradient family. This proves
   `maximal_weighted_dissipation_limit` for any continuous u and any strong
   maximal limit, even without a PDE premise. Integrate the signed difference,
   pass both endpoint roots and both integral terms to their limits, and apply
   lane 203's absorption/epsilon-removal and finite-energy compositions.

## Routes not used

* A uniform L¹ bound is NOT a common pointwise integrable majorant. Consequently
  the proposed dominated-convergence shortcut would need an additional
  argument. The finished proof uses strong L² pairings and the multiplier
  estimate above, never assumes a common dominator, and does not require a
  pointwise-convergent subsequence.
* `EulerTimeLpSubinterval.integral_energy_subinterval_limit` has no dissipative
  slot. Its unchanged statement cannot retain the negative square. Its
  subinterval pairing identities ARE reused; a new weighted-square passage
  supplies the missing operation.
* Lane 203's whole-window unweighted square-integral theorem alone does not
  imply convergence with a varying denominator on subintervals. The new
  theorem proves precisely that stronger conclusion.
* A provisional weighted-gradient convergence predicate was considered during
  development. It was removed after proving the multiplier and full-family
  identities. The delivered module has no residual convergence predicate or
  unproved analytic input.
* No estimate on every n-indexed forcing family is inferred from hFB. hFB is
  used only by the final imported limiting absorption theorem.
* No all-order classical constructor, differentiability of an arbitrary Lp
  representative, or trace of U at a single endpoint is assumed.

Searches covered Section4/{D01,A03,A04,A01,C01}, the vendor energy/word/TimeLp
files, and Mathlib Lp/FTC APIs. The lane-201 review route, lane-203 report and
attempts were read. No REVIEW_203 file is present in this checkout.

## Resolved diagnostics

```
failed to synthesize Module ℝ ↥(SobolevSpace 1 ?m.122)
Unknown identifier `EulerLiftedPressure.pressure_pairing_zero`
Invalid field `mono_set`: ... Integrable.congr ...
Invalid `←` modifier: `M` is a let-declaration name to be unfolded
failed to prove nonzeroness, but it would be possible to prove nonnegativity
```

Specify the `SobolevWord 2` type before elaborating `wordOperator`; pressure
orthogonality belongs to `EulerLiftedGradientSpace`; expose restricted-volume
integrability as `IntegrableOn` before using `mono_set`; use `change` to expose
local multiplier notation rather than reverse unfolding; and explicitly type
`sqrt((r t)^2+ε^2) ≠ 0` in the inverse continuity proof. None required a
heartbeat override. The final module and conformance file have no errors or
warnings.

## Conformance and negative control

All 27 module declarations and four named zero-data helpers print exactly
`[propext, Classical.choice, Quot.sound]`. The zero-data example has S=1 and
uses uniqueness to cover every competitor before applying the new finite-energy
export. It is not certification of a general analytic premise. A nonzero
scalar path x(t)=exp(−2t), ν=ε=1 exercises the retained negative dissipation.
A scalar control shows doubling the dissipative coefficient is invalid.

A scratch mutation changes only −ν*d to −2ν*d in the finite-level conclusion,
leaving its proof unchanged. Lean rejects it at the final scalar-FTC conversion
with `Type mismatch: After simplification, term H ...`, displaying −ν in the
proved expression and −2ν in the requested conclusion. Mutation sources/logs
remain in gitignored tmp; no failed or placeholder proof is committed.

The repository mutation suite separately passes its infrastructure controls.
Gate details and remaining global scope are in REPORT_204.md.
