# Lane 253 — spatial flux cancellation

## Read and reconciled

Read lane 251's complete `ForceCellIntegral.lean`, report and attempts; lane
247's `GridLemmas.lean`; the residual definitions in Contracts/V1/Data and
Packet; R42 support/smoothness/divergence fields and `inserted_equation_slab`;
Paper3 compact, force and time observation lemmas; A01/ConvectionDivergence
and A04/AdvectionDivergence; Mathlib derivative support and integration by
parts; paper `04-whole-space.tex:305–320`; CLAUDE, HANDOFF §0, LESSONS first
40 lines and NEXT_SESSION. Also searched Section4/D01,A03,A04,A01,C01 for
existing derivative/integral infrastructure.

The brief's gauge-free wording differs from this checkout: the actual
`pressureDifference_support` directly supports `pε−π`, and the pressure
formula already chooses the compact representative. No `c(t)` witness is
needed. A separate unconditional theorem proves that subtracting any spatial
constant `c(t)` leaves the pressure gradient unchanged, even without time
regularity of `c`.

## Successful proof

1. `compact_directional_integral` integrates a compact smooth vector field's
   directional derivative against the scalar constant 1, using Mathlib's
   `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`. It proves
   integrability as well as zero integral. `compact_flux_integral` sums this
   over the three coordinate directions. The suggested theorem name
   `integral_fderiv_eq_zero_of_hasCompactSupport` was not found in the pinned
   Mathlib; integration by parts supplies precisely the needed result.
2. `tensorDifference_compact` puts the tensor difference's support inside
   `tsupport (u−v)`: outside that support, `u=v`, hence `u_i • u−v_i • v=0`.
   This avoids imposing compact support on either background individually.
3. `advectionDifference_integral` applies A01's already proved conservative
   form separately to both divergence-free velocities. Linearity of fderiv
   turns the difference into derivatives of the compact tensor difference.
4. `pressureGradientDifference_integral` uses vector fluxes
   `(p−q) • e_i`. `laplacianDifference_integral` uses fluxes
   `fderiv (u−v) e_i`; `HasCompactSupport.fderiv_apply` supplies their compact
   support. Both yield integrability and zero mean.
5. `residualDifference_integral` expands the exact ν-scaled residual,
   subtracts the two time derivatives by interior differentiability, and
   integrates only differences. Integrability of the residual and the three
   spatial differences gives integrability of the temporal difference by
   algebra. Thus no totalized-integral loophole is used.
6. For an actual R42 record, the two momentum equations identify the residual
   difference with the force correction. The latter's smoothness and slice
   support prove integrability and that restriction to any containing cell
   changes no integral. This is a convenient alternative to separately
   restricting every flux and the time derivative; it uses **no zero-integral
   statement about force** and is not circular. The generic residual lemma
   then discharges the exact lane-251 input. Reference regularity and
   divergence are restricted from `[0,T+δ)`; time differentiation is only at
   `0<t<T`.
7. Lane 251 handles time zero by positive-time support and the temporal mean
   by compact differentiation under the integral. Its two conditional force
   conclusions now apply with `compactMomentumIntegral A`.

## Exact discharged input

`compactMomentumIntegral A` has type:

```lean
∀ ε ∈ Ioc 0 A.ε₀, ∀ (grid : Grid) (k₀ : Fin 3 → ℤ),
  A.ball ⊆ grid.cell k₀ → ∀ t ∈ Ioo 0 A.T,
  (∫ x in grid.cell k₀,
    (NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (A.velocity ε) (A.pressure ε) t x -
     NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π t x)) =
  (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t)
```

There is no remaining named hypothesis. `force_gridObservation_eq'` retains
only the original R47 regular-force assumption `hg : MemForceR A.g`.

## Failed/revised Lean routes

- Opening all of Contracts.V1 together with the upstream operators caused
  `Ambiguous term coordinateVector`, `advection`, and `spatialDivergence`.
  Use selective opens, including the contract's `Space` alias explicitly.
- Unannotated derivative integrability left
  `IsFiniteMeasureOnCompacts ?m` stuck. Specify `Integrable ...` with volume.
- `image_eq_zero_of_notMem_tsupport` inferred a subtraction function instead
  of the spatial slice. Specify `f := fun x => u x - v x`.
- `fderiv_sub` rewrites subtraction of functions, while the goal contains a
  lambda subtraction. Use `fderiv_fun_sub`; explicitly type the tensor
  product differentiability hypotheses to match the projected coordinates.
- `Integrable.const_smul` does not exist in this pin; use `Integrable.smul`.
- `convert` on an integrability expression generated an incidental topology
  equality (`PiLp.topologicalSpace ... = ...toTopologicalSpace`). Use
  `Integrable.congr` with pointwise algebra instead. For the integral
  decomposition `erw` resolves the equivalent instance presentations, and
  `Pi.smul_apply` exposes the scalar-multiple integrand.
- `ContinuousLinearMap.sub_apply` is deprecated; use `sub_apply` to preserve
  the required zero-output direct Lean check.

## Non-vacuity and scope

The audit has four examples: actual R42 force zero mean at scale `A.ε₀` and
time `A.T/2`, the exact residual identity at that scale/time, actual force
observations with `hg`, and an arbitrary pressure with the nonconstant gauge
`t²`. Positive scale and interior time follow from the record's strict
positivity fields. These are applications to the actual insertion record,
not a replacement by a zero field (incompatible with its blowup field).
They do not independently construct an R42 record.

Only four new deliverable files; no existing module, contract, test, report,
NEXT_SESSION or shared ledger edited. No new registration or complete R47
family assembly is claimed. Every theorem uses default 200000 heartbeats.
