# U7 attempts

## Verified outcome (lane 435 continuation)

The original scaffold identified two blockers. The first is false, and the
second was stated too broadly:

1. No extra radius field is needed. The threaded T16 witness gives
   `place.Kstar ⊆ D.plateau` and
   `D.plateau ⊆ ball 0 D.θRadius` (`plateau_subset_ball`), so
   `D.θRadius` is already a positive packet-carrier radius. The choice

   ```lean
   diffSupportRadius data =
     max data.D.θRadius (packetCarrierRadius data)
   ```

   therefore reduces to `D.θRadius`. Moreover
   `potential.eps_space : ε * D.θRadius < r` and
   `correction.ball_in_chart : ball x₀ r ⊆ ball chartCenter chartRadius`
   prove the exact `diffSupport_in_chart` field.

2. The packet-support bridge exists. In `probes/u7_closes.lean`,
   `T15.scaledVelocity_tsupp_subset`, compactness of `place.Kstar`, and
   `T16.latticeLift_sliceSupport_closed` prove the periodized packet bound.
   `correction_slice_support` proves the matching sharp bound for `w_ε`, and
   `tsupport_add` closes the exact velocity-difference target. The probe has
   zero output.

The remaining obstruction is an interface erasure, not a missing bridge.
`Contracts.V1.Packet.PacketImportAPI` contains

```lean
carrier_compact : IsCompact carrier
velocity_support : ∀ s ∈ Ico (0 : ℝ) 1,
  tsupport (fun y : Space => velocity (s, y)) ⊆ carrier
```

and Spec-level conversion can compose `velocity_support` with
`place.carrier_subset`. Canonical `T15.scalingStatement` also takes both facts
as premises. But canonical `T15.ScalingAPI` stores neither fact, and
`T18.InsertionData` stores only the raw set/fields plus `ScalingAPI`. Thus the
exact residual available to the bridge is

```lean
∀ s ∈ Ico (0 : ℝ) 1,
  tsupport (fun y : Space => data.packetVelocity (s, y)) ⊆ data.place.Kstar
```

and it is not a projection of `data`. A direct projection attempt gives:

```text
/tmp/u7_residual.lean:11:21: error(lean.invalidField): Invalid field `velocity_support`: The environment does not contain `NSFormalization.Section3.T15.ScalingAPI.velocity_support`, so it is not possible to project the field `velocity_support` from an expression
  data.scaling
of type
  NSFormalization.Section3.T15.ScalingAPI data.packetVelocity data.packetPressure data.packetForce data.carrier
    data.energyBound data.dissipationBound data.place
```

Because the lane rules prohibit editing existing modules and prohibit adding a
named input, the exact parameter-free canonical theorem
`velocityDifference_support (data : InsertionData)` cannot be declared in this
lane. The minimal upstream repair is to retain the raw packet velocity-support
clause in `InsertionData` (or in `ScalingAPI`); `Kstar_compact` already removes
the need to retain `carrier_compact` for U7.

## Superseded codex scaffold assessment

The canonical `ScalingAPI` currently has no packet-carrier radius field or direct support theorem for the periodized velocity. `velocity_singleCopy` only gives equality on the fundamental cube. Consequently the support inclusion and chart inclusion cannot be discharged from the available records. The attempted module records the exact target statements.
