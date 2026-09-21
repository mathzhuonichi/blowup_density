# Lane 188 — whole-horizon mild uniqueness

## Successful route: causal differences on finite windows

The new module proves `mildUniqueness : MildUniqueness` with exactly the predicate
from `CommonHorizon.lean`; no smallness, norm cap, regularity, divergence, or
invariance assumption is added. In fact `quadratic_mild_unique` handles arbitrary
continuous `Coefficients` at any finite Sobolev order (period one).

Set `R := max ‖u‖ ‖v‖` and `L := C.ballLipschitz R`. The actual quadratic
Lipschitz estimate is `EulerQuadraticSource.Coefficients.apply_sub_bound`, with
nonnegativity from `Coefficients.ballLipschitz_nonneg`. The difference `d := u-v`
satisfies `d = convolution (commonSource C u - commonSource C v)` by the vendor's
`convolution_sub` and `convolution_eq_interval`; its source `f` satisfies
`‖f t‖ ≤ L * ‖d t‖`.

`volterra_window_bound` proves the missing quantitative estimate directly from
`causalIntegrand` and its Bochner integrability theorem. If `d` vanishes through
`a`, and `0 ≤ b ≤ S`, `b ≤ a+δ`, `δ ≤ S`, then

```
‖d.comp (timeInclusion hbS)‖ ≤
  (kernelMass δ k * L) * ‖d.comp (timeInclusion hbS)‖.
```

For `r > δ`, either the causal indicator vanishes or `t-r ≤ a`, so the source
vanishes. For `r ≤ δ`, the shifted time stays in the prefix `[0,b]` and the
prefix supremum bounds the difference. Integration against the indicator of
`Iic δ` gives exactly `kernelMass δ k`, including the endpoints. No restart
identity or assumption about competitors being in the local solver's ball is
needed.

`volterra_eq_zero` propagates this estimate by natural-number induction with
`b := min ((n+1)*δ) S`. At zero, the interval integral vanishes. At each step,
`N ≤ c*N`, `0 ≤ N`, and `c < 1` force `N=0`. The Archimedean property gives a
finite `n` with `S < n*δ`, including the endpoint `S` in the conclusion.

The viscosity kernel uses `heatKernel_joint_continuous`, `heatKernel_bound`,
`parabolicKernelBound_nonneg`, and `parabolicKernelBound_integrable`.
`exists_positive_time_budget ν 0 L 1 S` supplies `0 < δ ≤ S` with
`(δ + 2*parabolicConstant ν*sqrt δ)*L < 1`;
`parabolicKernelBound_integral` identifies this with `kernelMass δ k * L < 1`.
This is the difference-window route, using finite induction rather than a first
supremum-of-agreement argument.

## Other route considered: restart and pasting

The search covered `vendor/NavierStokesAndEuler/Euler/`, local `Source/`, and
`Section4/{A01,A02,A04}/` with `grep -rnE` for
`unique|restart|shift|translate|concat`. Relevant vendor files were then read:
`QuadraticHeatLocal`, `VolterraUniqueness`, `VolterraConvolution`,
`VolterraFixedPoint`, `QuadraticCoefficients`, `SobolevHeatKernel`,
`SobolevHeatVolterra`, and `QuadraticMildPasting`.

`mild_solution_unique` requires `kernelMass T k * L < 1` on its entire input
interval and bounds on both competitors. `glue_quadratic_mild` proves forward
pasting from an already supplied restarted equation. Applying that theorem alone
does not derive the restarted equation for an arbitrary competitor. The
A02/A04 restart results concern classical solutions. The causal-difference
argument bypasses deriving a reverse restart identity and needs only the
existing singular-kernel integral definitions. This is a choice of proof route,
not a claim that restart identities cannot be proved from the tree.

## Lean diagnostics and fixes

The first draft left the indicator endpoint implicit:

```
error: don't know how to synthesize implicit argument `s`
error: don't know how to synthesize implicit argument `a`
```

Fix: specify `measurableSet_Iic (a := δ)` when proving integrability of the
truncated scalar majorant.

Passing a bare inequality to `indicator_of_mem` inferred the wrong set:

```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  indicator (Real.le✝ r) ?f δ
```

Fix: use `show r ∈ Iic δ from hrδ` (and the corresponding nonmembership form).
An attempted global `indicator_nonneg` also used membership for a different
bound variable; a pointwise split on `r ≤ δ` resolves it. The unused nonnegative
prefix hypothesis is named `_hb`; no linter is disabled. All diagnostics are
resolved. No heartbeat override was needed.

## Conformance and scope

Seven public theorems print exactly `[propext, Classical.choice, Quot.sound]`.
The audit proves `∃! u` solving the actual equation with zero datum and zero
force, for every positive viscosity and horizon, with witness the zero path.
The three primed common-carrier theorems instantiate the existing consumers
with `mildUniqueness`; the bounds and smooth-force premises remain as stated in
lane 186. No existing Lean module or vendor file is changed. The explicitly
requested A3-U row is the sole existing record edited. No push, merge, or rebase.
