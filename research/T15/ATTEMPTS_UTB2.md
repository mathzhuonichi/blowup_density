# U-TB2 attempts (lane 363)

## Successful route

The useful general statement is the `MemLp` version:

```lean
periodicSobolevENorm_zero_eq_of_memLp
  (z : SpatialField)
  (hp : IsPeriodicSpatial z)
  (hz : MemLp (torusLift z) 2 periodicTorusMeasure) :
  periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure
```

`parseval_backward z hp hz` supplies an order-zero datum `A`.  The proof of the
infimum equality is written out with `iInf_le_of_le` for `A` and `le_iInf` for
an arbitrary datum `B`; `datum_unique 0 z B.1 A B.2 hA` collapses the latter to
the selected datum.  `parseval_forward z A hA hz` then identifies the selected
datum norm with the physical norm.  This is stronger than the smooth-only
statement and directly follows the T10 definitions.

For `SmoothPeriodicT z`, the local helper `memLp_torusLift_smooth` obtains the
vector `MemLp` fact componentwise from `Paper1.memLp_torusLift`; the public
smooth theorem applies the general result.  The companion `periodicSobolevENorm_zero_ne_top`
uses `MemLp.eLpNorm_lt_top` after rewriting by the identity.

## Rejected / unnecessary routes

- Reusing the pre-existing T10 `sobolevENorm_zero_eq` would close the target,
  but would only alias an earlier theorem and would hide the requested `iInf`
  and uniqueness bridge.  The T15 module therefore does not import `ForcePaths`.
- A separate smooth-datum construction is unnecessary for the stronger theorem:
  `parseval_backward` already constructs the unique order-zero datum from the
  stated physical hypotheses.

## Verification observations

- The local `ContDiff` scope must be opened alongside `ENNReal`; otherwise the
  notation `∞` is parsed as an `ENNReal` infinity instead of the smoothness
  index expected by `ContDiff`.
- The probe's nonzero check uses `congrArg (fun y : Space => y 0)` on the
  equality `coordinateVector 0 = 0`, since `Space` is a `PiLp` value rather
  than a function equality accepted by `congrFun`.
