# T24 Ua2 attempts (lane 402)

## Closed declaration

`formalization/NSFormalization/Section3/T24/AffineDivergence.lean` proves the
exact Ua2 `divergence_free` clause over raw packet fields.  At each fixed
`t ∈ Ico 0 1`, raw packet smoothness gives a globally smooth spatial slice
`x ↦ U (t,x)`, while `AffineAdmissible` gives the same for `b`.  The vendor
theorem `NavierStokes.ResidualCalculus.spatialDivergence_add` therefore applies,
and the result is the sum of the raw packet divergence clause and the
admissible perturbation's divergence clause.

The registered-spelling probe uses the selected `Bindings.packet nu hnu`, with
its `velocity_smooth` and `divergence_free` fields as the only raw inputs.  It
also checks that the zero field is an admissible perturbation and closes the
same registered Ua2 conclusion for that concrete choice.

## Differentiability check

The candidate simplification of dropping `hvelocity_smooth` does not follow
from the available additivity result.  The vendor theorem has the signature

```text
spatialDivergence_add ...
  (hu : DifferentiableAt ℝ (fun y ↦ u (t,y)) x)
  (he : DifferentiableAt ℝ (fun y ↦ e (t,y)) x) : ...
```

`AffineAdmissible` supplies `he`, but the raw divergence equation alone does
not supply `hu`; the raw packet `velocity_smooth` clause supplies it.  Thus the
smoothness premise is retained rather than silently assuming linearity of the
totalized `fderiv` at a nondifferentiable point.

## Honesty and axiom audit

No named input, placeholder proposition, `sorry`, `admit`, `axiom`,
`native_decide`, or heartbeat override was introduced.  The axiom audit prints
exactly `[propext, Classical.choice, Quot.sound]` for the new theorem.
