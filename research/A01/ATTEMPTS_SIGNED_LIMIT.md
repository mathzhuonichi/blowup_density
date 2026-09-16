# Lane 203: signed-limit attempts

The result is conditional, not closure of the general-data signed passage.
No existing Lean module was edited. The explicitly requested A3-M2 record is
updated. No all-order constructor is used.

## Positive results

* Strong time-L² convergence preserves the integral of the squared norm.
* The same result holds after every bounded spatial linear map, with literal
  pointwise representatives under the integral (not just equivalence classes).
* Applying the genuine bounded word block to `energy_maximal_limit`'s
  approximation sequence gives `maximal_word_square_integral_limit` for
  **every word through q+2**, including the gradient of every energy word.
* `signed_quotient_absorption` keeps `-ν*g²` until Young absorption and divides
  by `sqrt(r²+ε²)` only after proving it positive. It proves the stronger
  upper bound `k²/(4ν)*r+b`, independent of epsilon, for `b≥0`.
* A single unabsorbed signed integral premise now implies lane 201's exact
  `CylinderSignedRootLimit` conclusion by integral monotonicity and epsilon
  removal. There is no bound on each n-indexed forcing family in this proof.
* Zero-data conformance proves the premise for all competitors and all maximal
  limits on windows up to S=1. Uniqueness makes the competitor zero; uniqueness
  of the strong limit makes U zero; its gradient representative is zero a.e.
  The example actually applies `finiteMildEnergy_of_forcingBound'`.

## Exact remaining input and intended nonzero-data route

`CylinderSignedEnergyPassage` in SignedLimit.lean is the only new analytic
predicate. Its complete statement is reproduced in REPORT_203.md. It is
independent of E, A and hFB. It asks for integrability and the unabsorbed signed
regularized-root inequality, for every positive epsilon, using the SAME U.
It does not request differentiability of an arbitrary Lp representative.

The supply should start from `regularized_full_energy_hasDerivAt` and use the
transport and pressure cancellations in vendor `MildMajorantEnergy.lean`.
At fixed epsilon, uniform convergence of the value family/root controls the
inverse denominator (bounded by 1/epsilon); strong convergence of forcing
and derivative words controls the remaining products. The new word theorem
establishes the unweighted whole-window square passage. The subinterval,
varying-denominator gradient passage and its assembly with those cancellations
are NOT proved here. They are isolated together as the standard signed
regularized integral estimate, rather than assumed separately as independent
inputs. The zero example is a conformance check, NOT certification of this
predicate for nonzero data.

## Negative routes / limits of the requested statement

1. Vendor `integral_energy_subinterval_limit` has no dissipative square slot.
   Feeding it the root inequality after dissipation has been dropped cannot
   recover that square. No attempted replacement of its forcing argument can
   fix this logical loss. The closest A04 square-root primitive theorem also
   needs everywhere interior derivatives, which a general TimeLp limit does
   not provide. Searches included Section4/{D01,A03,A04,A01,C01} and the vendor
   energy/TimeLp modules, not only Mathlib.
2. hFB is a bound on the limiting forcing family; it does not imply the
   analogous bound for each n. This lane never uses it that way. No extra
   lane-200 uniform regularized bound is needed for the conditional theorem:
   hFB is applied only after the signed limiting estimate is supplied.
3. The request omits a scalar sign condition. At r=0, k=g=z=0, b=-1, the tame
   premise is `0≤0` but the proposed quotient bound is `0≤-1`. This is checked
   in Lean. Thus the proof explicitly requires `0≤E*‖F‖`. This scalar example
   is NOT asserted to be a constructed nonzero PDE counterexample. For the
   finite-energy application, `mildNormConstant q≤E` already implies the sign.
4. hFB alone cannot provide lane 201's initial normalization: when F=0 its
   definition loses E entirely. The final export therefore retains hE.
5. A norm-square limit for one bounded word is not by itself the signed
   epsilon-weighted energy passage. The report does not label that gap closed.

## Compiler diagnostics (resolved)

```
error: not a positivity goal
Tactic `apply` failed: could not unify the conclusion of `@add_le_add_left`
Unknown identifier `EulerMildTopWord.mapPath`
Unknown identifier `intervalIntegrable_congr_ae_restrict`
error: don't know how to synthesize placeholder for argument `f`
```

Use nonnegative-square arithmetic for r²≤r²+ε², `add_le_add_right` for the
left fixed summand, the actual namespace `EulerMildWordEquation.mapPath`,
and `intervalIntegrable_congr_ae` on uIoc. Introduce the two let bindings in
the passage definition with `dsimp only` before introducing t and ht.
The mapped convergence proof also needs `Function.comp_apply` before rewriting
the a.e. integral identity. No heartbeat override was necessary.
