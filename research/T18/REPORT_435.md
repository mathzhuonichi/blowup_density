# REPORT 435

## 1. Theorems with exact statements

`Section3/T18/Support.lean` now proves, without extra inputs:

```lean
def packetCarrierRadius (data : InsertionData) : ℝ := data.D.θRadius

def diffSupportRadius (data : InsertionData) : ℝ :=
  max data.D.θRadius (packetCarrierRadius data)

theorem diffSupportRadius_pos (data : InsertionData) :
  0 < diffSupportRadius data

theorem correction_slice_support (data : InsertionData) :
  ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t : ℝ,
    tsupport (fun x : Space => data.D.correction ε (t, x)) ⊆
      periodicSet (Metric.ball data.place.x₀
        (ε * diffSupportRadius data))

theorem diffSupport_in_chart (data : InsertionData) :
  ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    Metric.ball data.place.x₀ (ε * diffSupportRadius data) ⊆
      Metric.ball data.place.chartCenter data.place.chartRadius
```

It also proves `packetCarrierRadius_spec`, `diffSupportRadius_eq`, and the
slice-to-spacetime support helper. The exact `velocityDifference_support`
field is not declared; the gap is below.

## 2. Files

- `formalization/NSFormalization/Section3/T18/Support.lean`: completed radius,
  chart, and correction-support proofs.
- `research/T18/probes/u7_closes.lean`: proves the exact
  velocity-difference support target conditional on the one erased raw packet
  clause, using `scaledVelocity_tsupp_subset`,
  `latticeLift_sliceSupport_closed`, and `tsupport_add`.
- `research/T18/axioms_u7.lean`: audits every completed public theorem.
- `research/T18/ATTEMPTS_U7.md`: verified residual and exact Lean error.
- `research/T18/T18_SPLIT.md`: U7 status updated honestly.

## 3. Gap with exact error text

The Spec packet record has `velocity_support`, and `place.carrier_subset`
turns it into support in `Kstar`. Canonical `ScalingAPI` and `InsertionData`
do not retain that clause. The exact residual is

```lean
∀ s ∈ Ico (0 : ℝ) 1,
  tsupport (fun y : Space => data.packetVelocity (s, y)) ⊆ data.place.Kstar
```

A direct projection produces:

```text
error(lean.invalidField): Invalid field `velocity_support`: The environment does not contain `NSFormalization.Section3.T15.ScalingAPI.velocity_support`, so it is not possible to project the field `velocity_support` from an expression
  data.scaling
of type
  NSFormalization.Section3.T15.ScalingAPI data.packetVelocity data.packetPressure data.packetForce data.carrier
    data.energyBound data.dissipationBound data.place
```

This corrects both scaffold claims: a usable carrier radius is already
threaded, and all periodization/support bridges exist. Completion requires an
edit to an existing canonical record, which this lane explicitly forbids.

## 4. Commands and results

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Momentum` —
  success, 10021 jobs.
- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T18.Support` —
  success, 10018 jobs.
- `lake env lean ../formalization/NSFormalization/Section3/T18/Support.lean` —
  zero output.
- `lake env lean ../research/T18/probes/u7_closes.lean` — zero output.
- `lake env lean ../research/T18/axioms_u7.lean` — all six completed theorems
  print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — success; 13 policy tests passed and 45 work items were
  consistent.

## Superseded codex scaffold report

### Theorems

Added `diffSupportRadius` and `diffSupportRadius_pos` in `Section3/T18/Support.lean`.

### Files

Added Support.lean, `probes/u7_closes.lean`, `axioms_u7.lean`, and `ATTEMPTS_U7.md`.

### Gaps

`velocityDifference_support` requires a packet-support bridge absent from `ScalingAPI`; `diffSupport_in_chart` requires the specified carrier radius `R_K`, absent from `PlacementData`. Lean errors identify the remaining type/goal failures.

### Commands/results

`lake build NSFormalization.Section3.T18.Insertion` passes. `Support` does not compile because the two missing API facts leave unsolved goals.
