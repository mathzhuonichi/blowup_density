# Lane 198 — energy premises

## Positive results

The actual competitor is used on its given closed window; no all-order
constructor or extension past the horizon is used. Every vendor premise is
constructed, so there is no additional named premises assumption.

* `energy_velocity_divergenceFree` applies the vendor heat preservation theorem
  to the actual projected quadratic coefficients and the solenoidal datum.
  The same velocity serves as transport. Cylinder Sobolev embedding supplies
  its pointwise a.e. bound.
* `energy_maximal_limit` uses the vendor maximal-regularity theorem directly.
  The local owner's wrapper returns restriction and integrability, but omits
  the approximation convergence; the vendor theorem supplies both.
* `ForcedSourceUpgrade.sourceTime_restriction` already is the required
  Navier–Stokes source restriction. Reuse it rather than duplicating it.
* `energyRawTime_restriction` and `energyPressureTime_restriction` are new.
  Pressure is the positive gradient projection of `force - advection`.
  This sign makes projected source plus pressure equal the raw residual in
  the vendor forcing-word convention. No time derivative at t=0 is involved.
* `energy_estimate_of_representatives` specializes the vendor theorem to the
  constant identity metric, c=1, scale=1, direction=0, radius=1 and order=0.
  All spatial derivative bounds of the metric vanish, so a=b=0 and k=1.
  The family is Unit × SobolevWord(q+1), containing every ordered word through
  q+1. It directly enumerates the full cutoff, corresponding to external
  cutoff N=q−5 with N+6=q+1; it does not use the correction wrapper's
  external/base decomposition or its CorrectionData/SpatialBudget inputs.
* `energyRootPath_apply` identifies this family norm with lane 196's
  `euclideanWordNorm` exactly. Thus its proved norm comparisons apply.
* `mild_energy_estimate_of_cylinder` assembles these facts, for arbitrary
  smooth force paths (in particular the canonical `C01.forcePath hf`).
* `finiteMildEnergy_of_estimate` is conditional on exactly the two explicitly
  defined lane-199 targets, not on an unproved premises package.

## Named-input satisfiability

`ha` is the restriction of standard initial solenoidality to the datum.
`hF` is continuity of each spatial Sobolev jet of the prescribed force on the
closed horizon, satisfied by the canonical physical force export.
`hu` is the standard projected mild equation restricted to the chosen window.
The lower-level representative theorem's `hu`/`hp` are ordinary divergence
and gradient constraints restricted to time slices; `hU` is strong maximal
approximation convergence, and `hF`/`hP` are a.e. restrictions of the same
Bochner fields, all discharged in the cylinder theorem.
`ForcingFamilyBound` restricts a tame full-word forcing pairing bound to
actual competitors and their strong maximal limits.
`EnvelopeConversion` restricts the desired dissipative energy-majorant
construction to those same competitors with the proved integrated estimate
and the tame pairing bound; it includes the still-unproved recovery of a
usable dissipative inequality.
Neither lane-199 predicate requires smoothness of the chosen Lp representative,
endpoint differentiation, nor constancy past the horizon. Both are checked
on zero data for all competitors and all maximal limits, using uniqueness.
A general nonzero proof of either predicate is not supplied here.

## Negative routes and diagnostics

The owner wrapper alone cannot supply vendor `hU`: it discards the convergence
component. Replacing a.e. restriction by that convergence without proof would
be an interface error; use `exists_maximal_mild_limit` instead.

The Euler correction `signedPressureTime_restriction` takes CorrectionData
and its coefficient jets. It does not accept the Navier–Stokes coefficients.
Our direct Leray projection avoids that mismatch and preserves the endpoint.

An arbitrary abstract inequality root(t)-root(s) ≤ integral Z cannot restore
heat dissipation: root=1, Z=0, derivative=0, nu=1 and g=1 obey the root bound
but violate `(1/2)*0 + 1*1^2 ≤ 0`. The final arithmetic contradiction is checked
in the conformance file. Consequently `EnvelopeConversion` is not claimed to
be an automatic scalar consequence; lane 199 may need a stronger signed limit.

Resolved compiler errors:

```
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
```

The large raw-source rewrite was split into typed congruence and map-subtraction
steps. Four declarations use commented local 400000 limits; none exceeds the cap.

```
Tactic `rfl` failed: ... energyValueFamily ... is not definitionally equal to ... euclideanWordNorm
```

Use `boundedWordBlock_value` to identify each actual word before reflexivity.

```
Type mismatch: After simplification ... value ... energyPressurePath ...
```

Expose the projection and use `value_truncateOperator` before congruence.
No unresolved compiler error or additional named premise remains.

An audit-formatting probe reported `Unknown option pp.width`; using the
Lean `format.width` option restored the successful conformance check.
