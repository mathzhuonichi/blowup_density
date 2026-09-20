# Lane 168 — A01 constructor pressure P3 report

## Outcome after review

The three notes in `REVIEW_168-A01-pressure-p3.md` are applied.

- N1: `momentum_of_projected` no longer takes the redundant pointwise
  `hprojected` binder. For the explicitly defined `G = R - ∂ₜu`, the required
  pointwise identity follows algebraically from incompressibility,
  `convectionDivergence_eq_advection`, and the definitions. The genuine
  mild/Leray projected input is the datum equality used by
  `pressureGradient_pressureOfVelocity_lerayComplement`.
- N2: the `hjoint` input to `pressure_smooth_of_velocity_smooth` is an
  additional global, endpoint-compatible regularity hypothesis on `G`. It is
  not implied by c3 plus `MemForceR`; B1/T1 must still prove an
  endpoint-compatible version.
- N3: `ConstructorPressure` is currently in no registered contract closure,
  so `make test` does not compile it. It must join the next registered A01
  contract closure after merge.

## Construction and theorem inventory

All names below are in `NSFormalization.Section4.A01`. The module defines

```lean
momentumResidualOfVelocity ν f velocity
  = f - (velocity · ∇)velocity + νΔvelocity

pressureGradientOfVelocity ν f velocity
  = momentumResidualOfVelocity ν f velocity - ∂ₜvelocity

pressureOfVelocity ν f velocity
  = RadialPotential.pressurePotential
      (pressureGradientOfVelocity ν f velocity).
```

It proves:

- `pressureOfVelocity_basepoint` — the fixed gauge `p(t,0) = 0`;
- `pressureGradientOfVelocity_memLp` — `MemLp` closure under the residual/time
  derivative difference;
- `pressureGradient_pressureOfVelocity` — pointwise `∇p = G` for a smooth,
  symmetric-Jacobian slice;
- `pressureGradient_pressureOfVelocity_lerayComplement` — the order-zero
  constructor-side Leray-complement datum identity;
- `pressureGradient_pressureOfVelocity_lerayComplement_order` — its lift to
  every natural Sobolev order carried by the residual;
- `pressure_gradient_memLp_slice` and `pressure_gradient_memLp` — the slice and
  full c9 rows;
- `pressureOfVelocity_slice_smooth` — spatial smoothness of each pressure
  slice;
- `pressure_smooth_of_velocity_smooth` — c4 from the additional global,
  endpoint-compatible `hjoint` hypothesis;
- `momentum_of_projected` — c7 momentum without a separate pointwise projected
  hypothesis;
- `pressureOfVelocity_zero` — zero force and velocity give zero pressure.

The final statement of `momentum_of_projected` is:

```lean
theorem momentum_of_projected {T : ℝ} (ν : ℝ) (f velocity : VelocityField)
    (hvelocity : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDivergence velocity t x = 0)
    (hgradient_smooth : ∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ ∞
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)))
    (hgradient_symm : ∀ t ∈ Ioo (0 : ℝ) T,
      RadialPotential.HasSymmetricJacobian
        (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual
        ν velocity (pressureOfVelocity ν f velocity) t x = f (t, x)
```

## Mathematical boundary

The radial construction is non-circular: it uses only `velocity`, `f`, and
the upstream two-sided `temporalDerivative`, not an existing pressure or
`ClassicalSolutionR`. The existing consumer-side theorem
`D01.isSobolevDatum_pressureGradient_lerayComplement` is therefore not used.

The genuine projected input remains

```lean
orderZeroDatum htime =
  orderZeroDatum hres -
    Leray.lerayComplement 0 (orderZeroDatum hres).
```

Together with the residual and time-derivative `MemLp` hypotheses, it pins
the datum of `G` to `(I-P)` of the residual. Separately, slice smoothness and
`RadialPotential.HasSymmetricJacobian G(t,·)` realize `G` pointwise as the
gradient of the radial potential. The current tree still lacks the converse
realization theorem that would turn an arbitrary Leray-complement datum into
such a pointwise smooth, symmetric-Jacobian field.

For c4, the exact extra input is

```lean
hjoint : ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity).
```

This is global and endpoint-compatible. c3 supplies only `ContDiffOn` on the
half-open future slab, while `MemForceR` supplies force regularity on the
future domain. Those hypotheses do not establish the global two-sided
regularity of the `fderiv` used by `temporalDerivative` at `t = 0`.

## Verification

All Lean commands were run from `verification/` after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorPressure
```

Exit 0; run silently, with zero captured output.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorPressure.lean
```

Exit 0; exactly zero output.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_pressure_p3.lean
```

Exit 0. All 14 audited declarations reported exactly
`[propext, Classical.choice, Quot.sound]`; the zero-pressure non-vacuity
example also typechecked.

From the worktree root, after sourcing `scripts/lean-env.sh`:

```text
$ make check
```

Exit 0. The architecture, contract-policy, and work-queue checks passed.
