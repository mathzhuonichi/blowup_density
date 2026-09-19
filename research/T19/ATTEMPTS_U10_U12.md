# T19 U10/U11/U12 attempt log

## Result

All three implementation theorems closed on the first compiled proof attempt.
The first canonical probe run omitted the notation scope needed by `ℝ≥0∞` and
reported exactly:

```text
../research/T19/probes/projection_closes.lean:14:21: error: expected token
```

Adding `open scoped ENNReal` resolved the parser error; it did not change any
theorem or proof.

## Successful route

- U10 uses `fixedInitialDensity` and repackages its force membership and
  lifespan bound with the fixed initial-data membership.
- U11 proves both set inclusions. The reverse inclusion uses the zero force,
  the parameters `s = 0` and `r = 1`, and U10.
- U12 reads the imposed first-coordinate equality in the forward direction.
  In the reverse direction it proves directly that the zero initial datum and
  zero force belong to their canonical classes, then invokes U10 with the same
  concrete parameters.

No named input, placeholder, local axiom, heartbeat override, or goal
repackaging was used.
