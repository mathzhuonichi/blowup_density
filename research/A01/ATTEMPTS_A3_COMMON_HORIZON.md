# Lane 186 — A3-U common horizon

## Positive result

`CommonHorizon.lean` supplies one ordinary carrier on the prescribed `[0,S]`,
conditional on **one** additional analytic proposition, `MildUniqueness`.
The datum and force at every order are the canonical `ordinarySobolev` and
`sobolevPath` values. Both unrestricted and invariant a-priori bounds work.
`compatible_carriers_hall` exports lane 178's existential interface verbatim.
The stronger primary theorems fix the datum and force in their statements.

Proof route: restriction commutes with heat by `value_injective` and
`heatOperator_value`; the nonlinear source follows from
`scalarProduct_of_value_eq` and the literal Leray value formula. Restrict the
ordinary heat integral using `intervalIntegral_comp_comm` and
`shiftedHeat_continuous`. The vendor's `mildPath_truncate` then proves restriction
of the gained mild path without redoing singular-kernel integrability.
`lower_forced_mild` lowers any canonical order-p solution to any `6 ≤ q ≤ p`.
Fix the ordinary path returned at order six, lower each higher solution to seven,
and apply `MildUniqueness`. `value_restrictOperator` yields the desired descent.
The original high-order solution retains its supplied angular invariance.

The continuation API also requests a nonnegative radius and an initial norm cap.
No such assumptions are added: internally use `max (R q) ‖u₀‖`; the original
bound implies this enlarged bound. The conclusion does not assert that the
chosen solution has norm bounded by the enlarged radius only: the original
bound can of course be applied again to its mild equation.

## Remaining analytic input (not hidden in hall)

`MildUniqueness` quantifies over positive ν,S, arbitrary order-seven initial datum,
continuous order-six forcing, and two continuous order-seven mild paths on
`[0,S]`; their two genuine forced Duhamel equations imply equality of the paths.
It has **no** ball-size or horizon-smallness premise. It is a definition of a
proposition and an explicit theorem parameter, not an added logical axiom.
This lane does not prove its inhabitance. Thus this is a conditional reduction,
not unconditional completion of A3-U or a proof of local existence from bounds alone.

Read/search audit: `grep -rnE 'restrictOperator|quadraticDuhamel|mild_solution_unique'`
covered all of `Section4/{A01,A02,D01}`, `Source/`, and the requested
`QuadraticHeatLocal*`, `CylinderSobolevSpace*`, `MeanOrdinaryLift*` vendor files,
including `OrdinaryCylinderDescent.lean`. Additional vendor searches covered
restriction, source/product compatibility, heat, uniqueness and pasting modules.
`VolterraUniqueness.mild_solution_unique` was read: it requires
`hsmall : kernelMass T k * L < 1` as well as both path norm bounds.
It cannot directly discharge the unrestricted predicate on a prescribed S.
`Source.OrdinaryViscousUniqueness.velocity_unique` instead requires all-order
smooth fields, physical time derivatives, pressures and PDE identities, so using
it here would reintroduce the constructor obligations. The finite-window
continuation code carries invariance but does not export arbitrary-competitor
uniqueness. The remaining task is to iterate local contraction on shifted
windows with a radius bounding both continuous paths, using quadratic pasting.
No claim is made that this fact is mathematically unavailable or false.

The time-smooth force premise `hfs` is consumed unchanged, not proved.
Paper context was checked with
`sed -n '66,76p' paper/sections/appendix-a-local-theory.tex`.

## Diagnostics and fixes

Initial broad rewrites produced:

```
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (400000) has been reached
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
```

These were implementation problems, not evidence for the analytic gap.
Explicit `congrArg₂` and `calc` steps, and bundling the source in `commonSource`,
closed them. Three declarations retain commented local 400000-heartbeat limits.
No global limit was raised.

An over-eager `ext t` descended through the continuous path and Sobolev array
into Lp representatives, yielding:

```
Type mismatch
  restrict_sobolev h (F t)
...
but is expected to have type
  ... =ᵐ[liftMeasure 1] ...
```

Use `ContinuousMap.ext` explicitly. A `let v := ...` in the target must be
reduced before `intro t`; otherwise `t` is the path rather than the time.
All these diagnostics are resolved. There is no final Lean error corresponding
to `MildUniqueness`: its proof remains an explicit obligation.

## Conformance

The audit prints the standard three axioms for all eleven public declarations.
It includes an unconditional positive-horizon all-order zero mild family and a
second example explicitly using canonical smooth `a := zeroField`, `F := zeroField`.
Neither example assumes `MildUniqueness` or a bound. See `REPORT_186.md` for gates.
