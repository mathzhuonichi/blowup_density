(Second review after the rework commit `5b4d9ad`; the first REJECT concerned the clause count and is addressed by `forced_global_of_boundInv` + probe `fix173_consumer_match.lean`.)
1. Confirm token identity of the conclusions of `forced_global_of_boundInv` vs `Continuation.forced_global_of_bound_unconditional` and of `localTheory_on_prescribed_horizon_of_boundInv` vs `Horizon.localTheory_on_prescribed_horizon` (rerun the consumer-match probe and diff the printed types with `#check`).
2. Confirm the only hypothesis change is `HasAprioriBound → HasAprioriBoundInv` (invariance added to the quantified `u`) and that the core helper is not exported as the main theorem anywhere in records.
3. Non-vacuity example exercises the seven-clause export.
