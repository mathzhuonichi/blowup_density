# U7 attempts

## Lead ruling resolution (lane 435 continuation fix)

The canonical theorem now follows the lead ruling: the raw packet support
clause is an explicit premise of `velocityDifference_support`, and
`InsertionData` is unchanged:

```lean
theorem velocityDifference_support (data : InsertionData)
    (hsupp : ∀ s ∈ Ico (0 : ℝ) 1,
      tsupport (fun y : Space ↦ data.packetVelocity (s, y)) ⊆ data.carrier) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : Space ↦ velocity data ε (t, x) -
        data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀
            (ε * diffSupportRadius data))
```

The premise deliberately uses `data.carrier`, not `data.place.Kstar`: this is
token-for-token the support target of the registered
`PacketImportAPI.velocity_support`.  The proof composes it with
`data.place.carrier_subset` to obtain the `Kstar` form and then uses retained
`Kstar_compact`, exactly as the T15 placement bridge requires.

`probes/u7_closes.lean` models U12 assembly from a registered
`P : PacketImportAPI ν`.  Its `InsertionData` has packet velocity and carrier
definitionally equal to `P.velocity` and `P.carrier`, so the support field is
closed by

```lean
NSFormalization.Section3.T18.velocityDifference_support data
  P.velocity_support
```

with no residual premise.  Thus the ruling is: **explicit raw premise; U12
assembly discharges it from `PacketImportAPI.velocity_support`; a later MAINT
may add the clause to `InsertionData`** if the canonical interface is revised.

## Pre-ruling verified outcome (superseded by the lead ruling above)

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

At this stage the lane treated any named input as forbidden, so the
parameter-free theorem could not be declared.  The subsequent lead ruling
supersedes that restriction for this field by requiring precisely the explicit
raw premise documented above; no record mutation is needed.

## Superseded codex scaffold assessment

The canonical `ScalingAPI` currently has no packet-carrier radius field or direct support theorem for the periodized velocity. `velocity_singleCopy` only gives equality on the fundamental cube. Consequently the support inclusion and chart inclusion cannot be discharged from the available records. The attempted module records the exact target statements.
