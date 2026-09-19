# T21 lane 472 attempts: N0--N10 and N12

## `memForceT_sub`: direct simplification of function subtraction

The first version tried to close the goal directly with
`memForceT_add hf (memForceT_neg hg)` and
`simpa only [sub_eq_add_neg, Pi.neg_apply]`.  Lean unfolded subtraction on
the function space but did not eta-expand function addition.  Exact build
error:

```text
error: NSFormalization/Section3/T21/Ball.lean:37:2: Type mismatch: After simplification, term
  T18.memForceT_add hf (memForceT_neg hg)
 has type
  MemForceT fun z => f z + -g z
but is expected to have type
  MemForceT (f + -g)
```

Resolution: first `change` the target to
`MemForceT (fun z ↦ f z - g z)`, then the same simplification is
definitionally aligned with the T18 supplier.
