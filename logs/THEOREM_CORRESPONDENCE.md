# Theorem correspondence and equivalence review

All 34 numbered theorem, proposition, lemma, and corollary statements in the two source manuscripts have a destination in the merged article. Six repeated results are shared, leaving 28 distinct numbered results. The comparison script checks coverage, labels, bibliography use, and normalized mathematical expressions in the statement bodies; it does not verify proofs.

| Source | Original label | Merged result | Statement comparison |
|---|---|---|---|
| Paper 1 | `thm:main` | Theorem 3.1 | Mathematical expressions unchanged |
| Paper 1 | `lem:calculus` | Lemma A.1 | Shared formulation; reviewed below |
| Paper 1 | `prop:local` | Proposition 2.1 | Shared formulation; reviewed below |
| Paper 1 | `thm:packet` | Theorem 1.1 | Original OpenAI notation and full conclusion restored; reviewed below |
| Paper 1 | `lem:packetenergy` | Lemma 2.2 | Mathematical expressions unchanged |
| Paper 1 | `lem:localization` | Lemma 3.2 | Mathematical expressions unchanged |
| Paper 1 | `prop:scaling` | Proposition 3.3 | Mathematical expressions unchanged |
| Paper 1 | `lem:potential` | Lemma 3.4 | Mathematical expressions unchanged |
| Paper 1 | `lem:correction` | Lemma 3.5 | Mathematical expressions unchanged |
| Paper 1 | `thm:insertion` | Theorem 3.6 | Mathematical expressions unchanged |
| Paper 1 | `cor:boundary` | Corollary 3.14 | Positive time margin made explicit; reviewed below |
| Paper 1 | `prop:density` | Proposition 3.7 | Mathematical expressions unchanged |
| Paper 1 | `cor:mixed` | Corollary 3.10 | Mathematical expressions unchanged |
| Paper 1 | `cor:closure` | Corollary 3.11 | Mathematical expressions unchanged |
| Paper 1 | `prop:projection` | Proposition 3.12 | Mathematical expressions unchanged |
| Paper 1 | `prop:critical` | Proposition 3.8 | Mathematical expressions unchanged |
| Paper 1 | `cor:nondensity` | Corollary 3.9 | Mathematical expressions unchanged |
| Paper 1 | `prop:affine` | Proposition 3.15 | Mathematical expressions unchanged |
| Paper 1 | `prop:multiple` | Proposition 3.16 | Mathematical expressions unchanged |
| Paper 1 | `prop:conservative` | Proposition 3.17 | Mathematical expressions unchanged |
| Paper 1 | `lem:critical-embeddings` | Lemma B.1 | Mathematical expressions unchanged |
| Paper 3 | `thm:Rmain` | Theorem 4.1 | Mathematical expressions unchanged |
| Paper 3 | `lem:Rlocal` | Proposition 2.1 | Shared formulation; reviewed below |
| Paper 3 | `thm:packet` | Theorem 1.1 | Original OpenAI notation and full conclusion restored; reviewed below |
| Paper 3 | `lem:packetenergy` | Lemma 2.2 | Mathematical expressions unchanged |
| Paper 3 | `lem:potential` | Lemma 3.4 | Mathematical expressions unchanged |
| Paper 3 | `lem:correction` | Lemma 3.5 | Mathematical expressions unchanged |
| Paper 3 | `thm:Rinsert` | Theorem 4.2 | Mathematical expressions unchanged |
| Paper 3 | `prop:Rcritical1` | Proposition 4.3 | Mathematical expressions unchanged |
| Paper 3 | `prop:Rcritical2` | Proposition 4.4 | Mathematical expressions unchanged |
| Paper 3 | `cor:Rclasses` | Corollary 4.5 | Mathematical expressions unchanged |
| Paper 3 | `prop:Renergy` | Proposition 4.6 | Mathematical expressions unchanged |
| Paper 3 | `thm:Rgrid` | Theorem 4.7 | Mathematical expressions unchanged |
| Paper 3 | `lem:critical-embeddings` | Lemma B.1 | Mathematical expressions unchanged |

## Shared formulations

1. **Sobolev multiplication (Paper 1, Lemma `lem:calculus`; merged Lemma A.1).** The two original periodic product bounds and critical embeddings remain explicit. The whole-space product estimate formerly proved inside Paper 3's local-existence proof is now stated in the same lemma. The proof uses the integrability of the order-minus-four Fourier weight, or summability of that weight on the periodic lattice. All original applications have integer order at least three, and the shared product estimate is also proved for order two. Mean-zero hypotheses apply to the homogeneous periodic embeddings, not to the inhomogeneous product estimate.
2. **Local theory (Paper 1, Proposition `prop:local`; Paper 3, Lemma `lem:Rlocal`; merged Proposition 2.1).** The statement covers both original data classes, with their respective pressure conventions, and is unchanged by the appendix reduction. Appendix A now applies Tao's published 2013 forced local theory on a common interval for all Sobolev orders. It explains the proof-level extension from Schwartz to smooth Sobolev data, recovery of time smoothness, viscosity scaling, and removal of the periodic mean. Applying the theory to the projected force and restoring the original pressure gradient avoids an unsupported scalar-pressure L2 requirement. The short difference-energy uniqueness proof, higher-order energy estimate, and restart argument under the squared H2 time-integrability criterion remain explicit. No whole-space Poincare inequality is used.
3. **Local cutoff and correction.** The displayed statements and estimates from both originals agree. They are proved once in the torus construction. Section 4 explicitly identifies their local Euclidean content and reuses it without periodization; the whole-space negative-order estimates are proved separately. The ball, compact support, active time interval, and smooth force extension across T remain the same.
4. **Critical embeddings.** The two source appendices were byte-identical before editorial normalization. Their shared Lemma B.1 is unchanged. Appendix B now cites Tao's homogeneous Sobolev inequality and Taylor's compact-manifold embedding instead of reproducing the maximal-function and potential-kernel development. The Euclidean homogeneous realization, Fourier convention conversion, mean-zero torus spectral gap, and derivative estimates remain explicit. This reduction received a separate independent source-applicability review.

5. **External theorem at the start of the introduction.** At the user's request, Theorem 1.1 now reproduces the full statement of OpenAI's Theorem 1.1, using its original lower-case velocity, pressure, and force notation, its compact set, viscosity, time interval, and explicitly named spatial norms. The final assertion excluding a smooth global solution with uniformly bounded kinetic energy is included. This statement was checked against the rendered first page of the saved official PDF. After the statement, one chosen solution is renamed (U, P, F) for use in the existing proofs. This explains the two additional non-identical statement comparisons, one for each original manuscript; the mathematical input used by the downstream proofs is unchanged.

## Proof review

The post-audit semantic revision explicitly binds `delta > 0` in Corollary
3.14 and writes the assumed reference interval as `[0,T+delta]`. The
compatible smooth no-slip reference remains an assumption; the construction
uses `2 epsilon^2 < delta`. Its conclusion, force class, initial velocity,
boundary values, and Sobolev norm convention are unchanged. This accounts for
one additional statement requiring contextual comparison with the original
source. Against the immediately preceding reviewed manuscript, the other 27
numbered statement bodies are unchanged up to whitespace. All 106 compiled
label numbers are unchanged. The six semantic clarifications and their
verification are recorded in `REVISION_20260912.md` and
`POST_REVISION_SEMANTIC_REVIEW_20260912.md`.

- **External input.** The compact force, velocity, pressure, initial condition, and unbounded-speed assertion were checked against the official source Theorem 1.1. The construction of that external theorem is cited, not reproved or newly certified here.
- **Scaling.** The equation retains the same viscosity. The velocity energy and dissipation norms scale as epsilon to the one-half power. The force scale is 2/q - 3/2 - s; the background force correction has one extra power of epsilon.
- **Exact insertion.** Curl of the explicit local vector potential equals the reference velocity. The smooth cutoff is one on an open neighborhood of the compact support throughout the active interval. Both cross-advection terms therefore vanish pointwise, including at support boundaries by smoothness. The correction force depends only on the smooth reference and cutoffs.
- **Lifespan.** Smoothness on every closed interval before T and local uniqueness give lifespan at least T; unbounded speed excludes continuation through T. Arbitrary-force density uses the separate case in which the reference already breaks down by T.
- **Critical periodic estimate.** The force need not have mean zero. The spatial mean is integrated separately, and its transport term is skew-adjoint in the homogeneous energy identities. Critical smallness absorbs convection; the H1 estimate gives squared H2 integrability after adding back the bounded mean.
- **Critical whole-space estimates.** Ordinary L2 energy controls low frequencies separately. The L1 homogeneous critical estimate yields global regularity under the original smallness condition, including a small critical initial velocity. The L2 inhomogeneous estimate yields regularity on a fixed horizon, with radius c times viscosity to the three-halves power times an exponential depending on that horizon.
- **Negative orders.** Homogeneous profile scaling is invoked only for -3/2 < s < 0. Lower inhomogeneous orders follow by monotonicity from an intermediate order; the homogeneous energy-force assertion uses s = -1, where integrability at the origin is valid.
- **Completed spaces.** Spatial approximation, the low/high-frequency cutoff estimate in homogeneous H-minus-one, real-vector approximation, and positive-time compact Bochner approximation remain in the proof. The background is not required to have finite homogeneous norm when only its compact difference is measured.
- **Secondary results.** Mixed-norm sufficient conditions, trajectory closure, extended-data projections, interior no-slip insertion, affine velocity variations with a quadratic force map, finitely many singular regions, conservative-force exclusion, and exact pre-T grid averages remain present. The grids may each have infinitely many cells, but only a finite number of grids is prescribed.
- **Review level.** The overall consolidation received a source-to-source mathematical and editorial review by the authoring agent. The later appendix reduction also received an independent agent review of source applicability and logical bridges, recorded in `APPENDIX_REDUCTION_INDEPENDENT_REVIEW_20260912.md`. This limited review does not certify the full manuscript. Structural checks, matching expressions, and successful LaTeX compilation are evidence of document integrity, not formal proof certification or a journal referee report.
