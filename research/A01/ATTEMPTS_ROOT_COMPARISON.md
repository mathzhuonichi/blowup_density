# Lane 201 — root comparison attempts

## Successful route

`scalar_differential_comparison` multiplies w by exp(-∫α). Its derivative is
(d-αw)exp(-∫α) ≤ 0 in (0,T). Closed-interval continuity makes the product
antitone on [0,T], including T=0. No derivative at either endpoint is assumed.

`scalar_integral_comparison` uses z=c+∫(αr+b), with r≤z. Since α≥0,
(z-y)'=α(r-y)≤α(z-y). Apply the preceding lemma to z-y. The root only needs
continuity; it may vanish. `energyComparison_unique_on_Icc` applies the differential
lemma in both directions and does not require α≥0. `positive_root_absorption`
is the exact k²/(4ν) Young division for r>0.
`regularized_root_comparison_limit` passes ε↓0 through sqrt(r²+ε²)
and the explicit comparison solution, using the right-neighborhood filter.
Both r=0 and c=0 are allowed; no division by the limiting root occurs.

The cylinder assembly uses `energy_maximal_limit`, the SAME returned U in
`ForcingFamilyBound`, and the single `CylinderSignedRootLimit` hypothesis.
It obtains the initial value directly from the mild identity at zero and
uses `euclideanWordNorm_bounds` and `mildNormConstant q ≤ E`. The conclusion
is lane 199's unmodified `CylinderRootComparison`; composition gives the
unmodified `FiniteMildEnergy` conclusion.

## Negative routes and exact remaining fact

1. Lane 198's integrated root estimate has discarded viscosity. With scalar
root=1, Z=0, its increment estimate holds, but d=0, ν=g=1 violates the
signed dissipative inequality. This arithmetic example is checked. It does
not refute the existential envelope predicate or assert a PDE counterexample.
2. `ForcingFamilyBound` bounds the limiting family, not each regularized
forcing family. Applying it directly to lane 199's n-indexed identity is not
a valid specialization. The residual explicitly asks for the absorbed
integrated root inequality for that same limit and a.e. forcing estimate.
No signed dissipation limit or uniform regularized tame bound is claimed proved.
3. Initial normalization is separate: E appears in `ForcingFamilyBound` only
as E*‖F‖, whereas comparison at zero asks for root(u₀)≤E*‖u₀‖. If F=0,
the forcing predicate is independent of E. The kernel-checked scalar example
has 1*0≤0 but 1≰energyComparison 0 0 0 0. This identifies the missing
normalization, not a constructed nonzero PDE counterexample. The assembly
states `mildNormConstant q ≤ E` explicitly; it is not concealed in the
analytic predicate. E,A remain fixed before all windows and competitors.
4. The residual and both assembly theorems now explicitly require solenoidal
initial data. This scopes the missing signed passage to the incompressible
route needed for transport and pressure cancellation. The imported
`ForcingFamilyBound` and `CylinderRootComparison` interfaces remain unchanged.

The exact single analytic hypothesis is the definition
`CylinderSignedRootLimit` in RootComparison.lean and reproduced in REPORT_201.
It is proved in the conformance file for every zero-data competitor, every
maximal limit, arbitrary E,A, and every horizon up to 1, using finite-order
mild uniqueness. The finite-energy assembly is applied with both inputs
constructed. No all-order constructor or classical-solution energy lemma is
used on a mild path.

## Resolved compiler diagnostics

```
Unknown identifier `TimeLp`
Unknown identifier `𝓝`
Tactic `rewrite` failed: Did not find an occurrence of the pattern deriv z t
Unknown identifier `mul_nonpos_iff_of_pos_right`
Type mismatch ... (cylinderEnvelopeDriver hq hT A u ^ 2) x ...
Type mismatch ... zero_sob (q + 1) ... expected ... =ᵐ[liftMeasure 1] ...
```

Opened EulerTimeLp/EulerRegularizedTopBlocks and scoped Topology; gave the
derivative target an explicit `change`; used positive-factor order
cancellation; simplified `Pi.pow_apply`; replaced recursive `ext` by one
`ContinuousMap.ext`. No heartbeat override was needed. No unresolved Lean
error remains after the final gates. Build warnings are replayed upstream
warnings; direct checking of the new module is silent.
