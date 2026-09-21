# B4T attempts (lane 508)

The protected B0/B2/B3 modules are unchanged. New adapters are in
`Section3/T11/H1Restart.lean`; entrypoints.json is the authorized existing-file
registration. The R³ module in lane 507 was read, not copied.

1. Gradient bridge: `memLp_gradientTensor`, `Real.sqrt_sq`, and
   `ENNReal.ofReal_toReal` close the exact B2 carrier conversion.
   Initial direct compilation found H1Bridges.olean missing; building the
   required closure solved this (10674 jobs).
2. Spatial H¹/H² bridges: use vector Parseval and the existing homogeneous
   gradient/Laplacian Fourier sums, including the zero mode.
3. Force scope: B2's final theorem requires `forceClassT`. Positive shifts
   preserve smoothness/periodicity but need not vanish near time zero.
   The classical regularity supplier `periodicLocalRegularity_of_classical'`
   only requires force smoothness and is usable after shifting.
