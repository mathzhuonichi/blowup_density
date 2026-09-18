# T14 proof attempts

## Successful route

The proof module imports `NSFormalization.Source.PacketEnergy` and keeps the
formalization layer independent of `Contracts.*`. The registered force clause
gives `HasCompactSupport f`; projecting `tsupport f` with `Prod.snd` supplies
the fixed compact spatial carrier required by `l2Sq_continuousOn` and
`packet_energy`. For each `0 < t < 1`, the velocity/pressure/PDE clauses are
restricted from `preSingularDomain` to `slab 0 t`. The source interval estimate
is converted with `intervalIntegral.integral_of_le` and
`integral_Ioc_eq_integral_Ioo`. The work equality uses
`primitive_regular` and `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
on the square of the interval primitive. The endpoint `t = 0` is discharged
by the zero-initial-velocity clause and empty set integrals.

## Tried routes and exact diagnostics

1. The first namespace setup opened both `NavierStokes.ProblemStatement` and
   `NavierStokesR3.ProblemStatement`. Lean rejected every unqualified field
   type with:

   ```text
   error: Ambiguous term
     VelocityField
   Possible interpretations:
     NavierStokesR3.ProblemStatement.VelocityField : Type
     NavierStokes.ProblemStatement.VelocityField : Type
   ```

   The final module opens only the base `NavierStokes.ProblemStatement` and
   qualifies the R³ residual/support predicate.

2. Applying `ring` directly after `convert (hNderiv s hs).pow 2 using 1`
   attempted to solve generated typeclass/function equalities and produced:

   ```text
   error: `ring_nf` made no progress on the goal
   error: Tactic `apply` failed: could not unify the conclusion of @funext
   with the goal Real.instAddCommGroup = Real.normedCommRing.toCommRing.toAddCommGroup
   ```

   The derivative target was instead changed explicitly to the interval
   primitive function, then `simpa` was used on `HasDerivAt.pow`.

3. Converting the set integral to an interval integral before proving the
   pointwise integrand equality made `setIntegral_congr_fun` inapplicable:

   ```text
   Tactic `apply` failed: could not unify the conclusion of
   setIntegral_congr_fun measurableSet_Ioc with the goal
   ∫ (x : ℝ) in 0..t, ... = ∫ (s : ℝ) in 0..t, ...
   ```

   The final proof first establishes an `Ioc` set-integral equality, then
   rewrites the left endpoint integral to the interval integral.

4. In the canonical probe, direct `simpa` between contract and source energy
   quantities failed because the contract definitions are only connected by
   their registered `rfl` bridges:

   ```text
   Type mismatch: After simplification, term he has type
   ... NavierStokesR3.CompactEnergy.l2Sq ...
   but is expected to have type
   ... l2Sq ...
   ```

   Adding `BlowupDensity.Bindings.l2Sq_eq` and
   `BlowupDensity.Bindings.dissipation_eq` to the probe's `simpa only` closes
   the bridge. The force primitive bridge is `rfl` by
   `accumulatedForce_eq_module`.

No residual theorem gap remains. There are no `sorry`, `admit`, `axiom`, or
`native_decide` declarations in the delivered files.
