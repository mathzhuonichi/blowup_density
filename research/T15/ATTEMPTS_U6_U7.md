# T15 U6/U7 attempts

## Successful proof routes

- `unboundedSpeed`: `Source.PacketScaling.speed_unbounded_at_target`, applied
  to `zeroPastField_speed hspeed`, gives the Euclidean scaled blow-up at
  `place.T`.  `place.eps_time` supplies `ε² ≤ place.T`.  A witness whose norm
  is greater than the positive threshold is nonzero, so
  `scaledVelocity_slice_subset_cube` puts its spatial point in
  `fundamentalCube`; `velocity_singleCopy` then transfers the same norm
  inequality to `periodizedScaledVelocity`.
- `force_mem`: `parabolicForce_smooth` and
  `parabolicForce_positive_support` transport the raw smoothness and compact
  positive-time support.  `scaledForce_supportedInCube` packages U2's strict
  slice support for `contDiff_periodize`; `unitSpatialPeriodsOn_periodize`
  gives periodicity.  The compact time witness is
  `Prod.fst '' tsupport (scaledForce ...)`, and
  `Paper1.PeriodicBridge.time_support_periodize` proves that periodization
  introduces no new support time.

Neither proof module needed a failed proof attempt, a named input, or a
repackaged residual goal.

## Failed checks and exact diagnostics

1. The first probe check was run before Lake had produced the two new object
   files.  Exact output:

   ```text
   ../research/T15/probes/blowup_force_mem_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/442-T15-U6-U7-blowup-force-mem/formalization/.lake/build/lib/lean/NSFormalization/Section3/T15/Blowup.olean' of module NSFormalization.Section3.T15.Blowup does not exist
   ```

   Resolution: build
   `NSFormalization.Section3.T15.Blowup` and
   `NSFormalization.Section3.T15.ForceMem` from `verification/` first.

2. The first elaboration after that build omitted `open scoped ContDiff` in
   the probe and left the closure-mono intermediate untyped.  Exact output:

   ```text
   ../research/T15/probes/blowup_force_mem_closes.lean:35:32: error: expected token
   ../research/T15/probes/blowup_force_mem_closes.lean:46:18: error(lean.unknownIdentifier): Unknown identifier `hfsmooth`
   ../research/T15/probes/blowup_force_mem_closes.lean:77:7: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     tsupport ↑bfmBump
   in the target expression
     closure (Function.support bfmField) ⊆ closure (Function.support ↑bfmBump)

   hsub : Function.support bfmField ⊆ Function.support ↑bfmBump
   h : closure (Function.support bfmField) ⊆ closure (Function.support ↑bfmBump)
   ⊢ tsupport bfmField ⊆ Metric.closedBall 0 (1 / 4)
   ../research/T15/probes/blowup_force_mem_closes.lean:121:37: error: expected token
   ../research/T15/probes/blowup_force_mem_closes.lean:210:14: error(lean.unknownIdentifier): Unknown identifier `bfmForce_smooth`
   ```

   Resolution: open the `ContDiff` scoped notation and ascribe
   `h : tsupport bfmField ⊆ tsupport (⇑bfmBump)` before rewriting by
   `bfmBump.tsupport_eq`.  The unknown identifiers were downstream parser
   errors and disappeared with the notation fix.

## Residual gaps

None.  The two canonical fields close from the raw packet clauses stated in
the theorem signatures, and the probe supplies both literal field-type checks
and an explicit geometric instance.
