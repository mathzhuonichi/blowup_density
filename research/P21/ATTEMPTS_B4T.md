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

## Closed proof route

All 23 exported theorems in the module are kernel-checked; `h1RestartT` is
proved, not a predicate, and has no auxiliary theorem/input hypothesis.
Each closed lemma was committed separately with the lane prefix.

- Vector `hasSum_freqEnergyT` plus the homogeneous gradient/Laplacian sums
  close the full H¹/H² identities. The zero-order sum retains the mean.
  Combining these with B0's exact identities gives all three requested
  component-energy equalities, including ordered Hessian = Laplacian.
- `enstrophy_differential_on_IccT'` discharges exactly B2's three hypotheses.
- Classical Sobolev path continuity and termwise energy differentiation give
  continuity on Ico and differentiability on Ioo, at every integer order.
  Finiteness follows from `periodicSobolevENorm_ne_top_smooth` on each slice.
- The force cap is an L² NORM cap; the scalar B3 force-energy parameter is
  `(forceL2CapT f S).toReal ^ 2`, not its unsquared value.
- `weightedEnergyIdentity_smoothT` and `enstrophy_differential_smoothT`
  generalize the B2 assembly inside this module. They use the already proved
  `energyIdentity_of_classical`, B2's physical pairing conversions, nonlinear
  bound and scalar Young assembly. Only smoothness and spatial periodicity
  of the force are used, so positive translates are permitted.
- `uniform_periodicHTwo_running_boundT` uses B3 with c=ν, C=Cν,
  K=K.toReal², F=cap.toReal² and D=min d 1. One D and B precede both shift and
  datum. Y(0) is rewritten with `w.initial`. Compact continuity of Z supplies
  integrability before converting the real bound to a lintegral bound.
- `uniform_periodicHTwo_endpoint_boundT` uses the proved B3
  `enstrophy_endpoint_lintegral`, directly matching the continuation carrier.
  It does not need the stronger Bochner `enstrophy_endpoint_integral` theorem.
  No measurability or integrability assumption has been silently dropped:
  compact integrability was used before taking the endpoint lintegral limit.
- The registered `extendsBeyondH3` cannot be applied to a generic positive
  translate: its forceClassT premise need not hold. The second route follows
  its proved lower-level argument: `torusPairingBound_slice`,
  `energyIdentity_of_classical`, and `torusGronwallChain` give an H³ bound for
  ANY globally smooth periodic force with finite H² dissipation. The smooth
  force datum path is continuous, and its integral on [0,R] bounds all shorter
  forcing integrals. `periodicQuantitativeLocalInputH3`, successive applications
  of `forceSobolevENormT_timeShift_le`, and `glueClassicalSolutionT` then give a
  strictly larger horizon for a shifted test force. This is
  `shifted_horizon_extensionT`; pressure overlap is unnecessary for the
  lifespan contradiction, but the returned object is a full classical
  solution. No assumed continuation input is introduced.
- `exists_maximal_smoothT` instantiates the existing Paper1 maximal gluing
  with `exists_classical_of_picard`; its construction does not use test-force
  support. The positive maximal endpoint cannot be ≤D, by the preceding
  endpoint integral and horizon extension. The supremum definition bounds
  every realized horizon, giving the contradiction.
- The conclusion uses δ=D (strict lifespan inequality is already proved).
  `periodicLocalRegularity_of_classical'` supplies all three bundle fields
  from shifted force smoothness; no new uniqueness or patching argument is
  needed for regularity.

## Actual elaboration failures and resolutions

1. An H¹ `convert` left equality of sums using `h1FreqEnergy` versus its
   expanded angular-weight expression: `error: unsolved goals`. Unfolding
   `T20.h1FreqEnergy` and `velocityCoeffT` closes the exact remaining equality.
2. `summable_homogeneous_total hm` reported that `0 < m` was supplied where
   `0 ≤ m` was expected. Passing `(s := m) hm.le` fixed it.
3. Directly rewriting the natural-order energy identity with real-order H¹
   pairings reported `Tactic rewrite failed: Did not find an occurrence of
   torusRealPairing G F`. The existing B2 cast-normalization pattern
   (`IsPeriodicDatum`, `Nat.cast_one`, `torusRealPairing`) closes this seam;
   it is isolated in `inhomogeneousEnergyIdentity_smoothT`.
4. Untyped force-slice continuity gave `don't know how to synthesize implicit
   argument f`. An explicit `Continuous (fun x => f (t,x))` type fixes t.
5. The lintegral conversion needed `dsimp only` after
   `setLIntegral_congr_fun`; otherwise the rewrite could not see the beta-redex.
6. A midpoint positivity proof initially omitted `ht.2`; linarith needs both
   0≤t and t<S. `hc.intervalIntegrable` also requires explicit endpoints 0 S.
7. The contract solution structure lives in `Contracts.V1.TorusLocalTheory`,
   not `TorusData`. The probe now uses the actual structure conversion and
   regularity equivalence from the existing binding.
8. A `fail_if_success` wrapper did not capture an elaboration-time unsolved
   finite-cap proof. The final mutation is instead checked with `#guard_msgs`,
   expecting exactly `error: unsolved goals / ⊢ False` when specializing at ⊤.

No residual mathematical goal remains for B4-T³. B5's endpoint theorem and
registration remain separate. No claim about the stronger L¹-only
`PeriodicQuantitativeLocalInput'`, rough H¹ data, or the old selected H³
horizon is made. No per-declaration heartbeat override was needed.

## Final verification

The full module builds (10674 jobs). All 23 theorem axiom sets were checked
for exact equality with the standard set, not merely absence of forbidden
axioms. The contract-shaped consumer and a generated probe against the literal
Targets.lean Prop both compile. A second temporary probe verifies B5's entire
existing restartBeyond proof with the single supplier replacement.

Required article audit: 72 declarations / 27 entries / zero forbidden results.
`make check` (all 11 policy tests), `make test` (11027 jobs), mutation suite,
and paper/reader gates all pass. The inherited policy regression mentioned in
older lane reports is not present in this checkout. Required audit and graph
regeneration refresh stale generated artifacts against the inherited
unchanged authoritative source; no new article status is assigned by this
lane. Generated PDFs were restored, since no paper source was edited.
