# B4 attempts

- Read the COMMON rules, assessment, split and B0/B1/B3 reports and target.
- Normalization correction: `Source.angular_partial_norm_sq` explicitly cancels
  `2π`; the correct B1 parameter is κ=1. B0's force cap is a norm, so its square
  bounds the physical squared force energy.
- Direct support-free route: `D01.FiniteOrderNorm.norm_raise_sq_eq`, using
  `weakDerivs_smooth`, `smoothField_weakDeriv_pairing`, and datum uniqueness.
  `sobolevEnergy_succ_smooth` compiled without any support hypothesis.
- Initial direct compilation failed because B0's .olean was not installed;
  building the dependency closure resolved this.
- Existing-file edit authorized by brief: entrypoints.json registers new modules.
  No lane 503/504/506 source has been edited.

## Closed route and interfaces

1. Support-free successor identity: obtain integer-order data for the field and
   its physical directional derivatives using `weakDerivs_smooth`; use
   `memLp_coord_smul_datum` and `isSobolevDatum_raise`, then
   `norm_raise_sq_eq`. This closes the direct weak-derivative/Fourier route.
   Compact approximation was unnecessary, so no unsupported density claim is used.
2. Order zero: T22's exact `sobolevENorm_zero_eq_eLpNorm` and C01's
   `eLpNorm_toReal_sq_eq_l2Sq`. Order one: successor at zero and
   `gradientSq_eq_sum`. Order two: successor at one and A05's
   `sum_integral_hessian`. The B1 gradient-norm bound is equality by
   `PiLp.norm_sq_eq_of_L2` and `I02.eLpNorm_two_eq_ofReal_sqrt`.
3. `enstrophy_differential_on_Icc'` invokes B1's parameterized theorem at κ=1.
   Its Cν is `(2*C₀^(3/2))^4/(ν/2)^3 + (1+ν) + (1+2/ν)`.
   No reviewed B0/B1/B3 file was changed.
4. Time continuity follows from the existing datum-path norm continuity.
   Interior differentiability follows by local equality with the physical
   inhomogeneous energy. Integer-order slice norms are finite by datum uniqueness.
5. The force bound is **the square** of `(forceL2CapR f S).toReal`, since B0's
   cap is the L² norm, not its square.
6. B3 provides d and M. Use D=min d 1 and the explicit uniform real bound
   B=(K.toReal²+Cν*(1+M)^3*D+Cν*forceCap.toReal²*D)/ν.
   Convert compact real integrals to nonnegative integrals using slice finiteness.
7. At the endpoint use B3's `enstrophy_endpoint_lintegral`. Its integrand is
   `ofReal Z`, so an explicit `ofReal(toReal norm²)=norm²` conversion is made
   on every slice. This avoids falsely assuming global measurability of a
   classical field at times where its specification imposes no conditions.
   The conclusion bounds `squaredHTwoIntegral` itself, which is what continuation needs.
8. A02's `exists_maximal'` and `maximalLifespanR_pos` give the finite-endpoint
   contradiction through `extendsBeyond_of_memForceR'`. The strict inequality
   permits δ=D itself. No bound on the old selected A01 horizon is asserted.
9. Arbitrary classical regularity uses `classical_hasSmoothSobolevPath` and
   A01's general pressure-recovery, projected-equation and pressure-potential
   theorems. The smooth-path theorem internally uses uniqueness on overlapping
   selected carrier windows. No new uniqueness/gluing assumption is introduced.
10. `h1RestartAt` supplies B5's per-time inequality using the proved
    `shiftedLocalExtension` and `w.restart_datum`.

## Resolved compile findings

- `simp`/`rw` did not unfold the nested slice/datum carriers at the default
  transparency; explicit `change` or `convert ...; rfl` closes the definitional
  seams. Natural-order casts similarly need `norm_num` when identifying Y/Z.
- An initially underconstrained barrier elaboration exceeded 200000 heartbeats.
  Explicit local types and corrected addition monotonicity resolved it; **no
  heartbeat override remains**.
- `IntegrableOn` needs an explicit measure/type annotation before applying
  compact-interval integrability.
- B3's endpoint lintegral theorem consumes real Z through `ofReal`; applying it
  directly to an ENNReal integrand failed with `could not unify the conclusion`.
  The proved local finiteness conversion resolves this, without endpoint values.
- Existing `ClassicalSolutionR` structures in A02 and contracts are distinct.
  The exact target probe uses `maximalPartial_ofA02` and
  `localTheoryV2_regularity_ofA02`; ordinary vocabulary remains definitionally equal.
- Creating Targets.olean outside verification requires `lean -R .. -o ...`.
- Mathlib's zero Lp witness is `MemLp.zero`, not `memLp_zero`.

No residual Lean goal or analytic hypothesis remains in B4. The mutation probe
clears `hnorm` and checks that the identical restart supplier application fails;
with the bound restored it succeeds. It makes no claim that an unrestricted
uniform global result has been disproved.

## Repository gates

The required fresh article audit passed (72 declarations, 27 entries, zero
forbidden axioms). `make check` initially found the inherited stale dependency
graph; regeneration from unchanged `proof_graph.json` resolved it. Audit target
changes likewise reflect the inherited guide, not a B4 coverage decision.
The generated `AXIOM_AUDIT.json` and `DEPENDENCY_GRAPH.md` refreshes are the only
additional blueprint edits. `make check`, `make test`, `make test-mutations`,
`make paper`, and `git diff --check` all passed. Generated PDF churn was restored.

The separately executed bound-deletion mutant exited 1 at
`⊢ sobolevENorm 1 a ≤ K` (`Tactic assumption failed`); the positive probe exits 0.
All 17 printed theorem axiom sets were also mechanically compared to the exact
three-element allowed set, beyond the standard-only TestSupport checks.
