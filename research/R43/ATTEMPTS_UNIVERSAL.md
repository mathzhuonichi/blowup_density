# Lane 225 — attempts

1. Read the exact RCritical1API statement and lane 223 endpoint/review.
   The requested finite-horizon interpretation is not the spec: the target is
   infinite lifespan under homogeneous sum smallness.
2. Checked C01 V4, its binding, and MaximalEndpoint. The general initial
   gradient term and initial L² budget are already present; no local budget
   substitute or new continuation hypothesis is needed.
3. Generalized Paper1's scalar bootstrap wiring using C01's existing general
   square-root comparison. Kept the initial value in N, avoiding any division
   by y or any assumption that it is positive.
4. Initial Lean attempts exposed elaboration details:
   `√((y ^ 2) 0)` requires `Pi.pow_apply` before `Real.sqrt_sq`;
   the primitive N must be explicit when supplying its initial inequality;
   `add_le_add_right` supplies the required fixed-left-addend inequality
   in this imported vocabulary. All were resolved.
5. A first arithmetic proof left `1 < trilinearConst / trilinearConst`;
   giving `ne_of_gt trilinearConst_pos` explicitly to field_simp closed it.
   Removed a redundant ring tactic to make direct compilation silent.
6. ENNReal prefix assembly proves the initial norm is finite from the actual
   sum-smallness hypothesis before rewriting ofReal_toReal.
7. Composed slice absorption, maximal-family absorption, the existing general
   H² endpoint budget, A02.exists_maximal', and A04's unconditional fixed-force
   continuation. No mathematical gap or fallback assumption remains.
8. Conformance checks cover all nine implementation declarations, the recovery
   theorem, the copied spec norm and its bridge, and the Data-vocabulary
   universal theorem: 13 exact standard-three reports. Both non-vacuity
   examples compile. Build replays existing dependency warnings; direct Lean
   checking produces zero bytes.
