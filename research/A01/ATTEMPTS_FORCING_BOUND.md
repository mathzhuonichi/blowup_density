# Lane 200 — forcing-family bound attempts

## Result and limitation

The lane proves exact a.e. identification of lane 198's Z, exact cancellation
of its Leray source and pressure complement, the physical source-family bound,
and assembly of `ForcingFamilyBound` from ONE spatial hypothesis:
`CylinderCommutatorBound q hq`. General-data closure is not claimed.
The exact residual and theorem signatures are in `REPORT_200.md` and the new
module. `A q` is an explicit candidate conditional on that residual; it is not
a proved general-data tame constant. `E q` is the proved source constant.

Interface note, scoped to the revisions actually checked: at reviewed HEAD
`494e1d4` against integration `5ca3bea`, and after rebasing onto integration
`79b3677`, `ForcingFamilyBound` has arguments `hq hν a F hF E A` and no `ha`.
The conclusion in `forcingFamilyBound_of_cylinder` therefore uses exactly
`ForcingFamilyBound hq hν a F hF (E q) (A q)`. This must be rechecked if that
imported declaration changes in a later revision.

## Positive route

1. `RegularizedForcingRepresentative.weighted_forcing_ae` specializes to the
   same Unit/full `SobolevWord (q+1)` family, weights one, identity metric.
2. `leray = id - sobolevGradientProjection` implies source + pressure = raw
   force minus asymmetric transport. Their word arrays cancel BEFORE a norm
   is taken. There is no extra pressure constant or projection boundedness gap.
3. Reindex the actual `U : TimeLp T (SobolevSpace 1 (2+q))` using the existing
   `reindexMaximalTime`. Its representative is supplied by `coeFn_compLpL`.
   This yields the exact nonlinear array
   `transport(word U) - word(asymmetricTransport u (restrict U))`.
4. The physical source array has norm at most `mildNormConstant q * ‖f‖`,
   by lane 196's `euclideanWordNorm_bounds` and the continuous path sup norm.
5. The genuine maximal limit restricts to u a.e. by
   `maximal_limit_restriction`. Apply the spatial residual at those elements,
   identify its gradient square sum with `energyGradientNorm U`, apply the
   family triangle inequality, then multiply by the nonnegative energy root.

All carriers remain finite-order. Neither smooth representatives nor a
`ClassicalSolutionR` nor the all-order constructor is used in this chain.

## Negative routes / analytic gap

* `inner_energy_Rhigh` is signed Hilbert-space energy assembly with a nonlinear
  pairing hypothesis. It gives no upper bound on a forcing vector's norm.
  `outerProductTame` and `outerSobolevNormAt_le` are tensor norm bounds, not
  commutator-family norm bounds. The real conversion also requires explicit
  finite order-two and order-m datum norms. They were NOT silently applied to
  an Lp representative or to a mild path. Those bridges and the quantitative
  finite-order commutator estimate remain inside the single spatial residual.
* `BaseTransportL2.transport_base_L2` assumes smooth cylinder representatives
  and all-order word MemLp, and only treats words of length at most six.
  Our full family includes q+1, at least seven. Instantiating its smooth/all-order
  hypotheses from the given finite-order elements is not a legitimate shortcut.
* `SobolevTransportCommutator.externalCommutator_ae` and
  `externalCommutator_sumNorm`, `ExternalTransportCommutator` and
  `BaseTransportCommutator` provide valuable word identities / base and Gevrey
  estimates. Their bounds do not directly have the required low-order-7 times
  full-gradient-family shape and this explicit A. A quantitative extension /
  interpolation and finite-regularity approximation argument remains necessary.
* Searches covered vendor filenames, declarations and commutator docstrings,
  and `Section4/{D01,A03,A04,A01,C01}`. Nearby A03 tame products, A04 signed
  assembly and A01 `outer_tame_low` were read. No claim that all relevant
  analytic ingredients are absent is made: the missing result is the exact
  finite spatial inequality printed in the report.
* `16` in the target is the fixed lane-198/order-two-cap normalization, applied
  to the order-7 restriction (the lowered order-6 mild carrier). This lane does
  not assert a physical order-two descent/finiteness theorem for arbitrary V.
* The requested `research/A01/REVIEW_199-A01-envelope.md` is absent in this
  checkout (`cat: ...: No such file or directory`; filename search confirms).
  `REPORT_199.md`, `REVIEW_198-A01-energy-premises.md` §3 and the prompt's
  lane-200 route were used. No other worktree was accessed to obtain it.

## Satisfiability and negative examples

`CylinderCommutatorBound` quantifies over compatible finite Sobolev elements;
it asks for a spatial norm inequality, not smoothness of arbitrary Lp values,
not a continuation, and not an all-order realization. Its quantification is
stronger than restriction to actual mild competitors (no solenoidality or
angular invariance is used). Its general nonzero proof, including sufficiency
of the candidate A, remains open. Zero does NOT certify that global hypothesis.

The conformance file proves the exact `ForcingFamilyBound` target on zero data
for every competitor by finite mild uniqueness, for every maximal limit.
It separately proves that the new commutator and its spatial inequality vanish
on zero finite elements. A scalar negative check verifies that a signed
pairing bound need not give a norm bound. These tests do not prove the global
spatial residual and are not presented as doing so.

## Compiler diagnostics and fixes

Resolved diagnostics (no remaining compiler error):

```text
Unknown identifier `gevreyWeightPath`
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (400000) has been reached
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ... (ContinuousLinearMap.compLpL ... (leray ...)) ...
typeclass instance problem is stuck
  HAdd ?m.514 ?m.515 ?m.518
```

Open the right vendor namespace; split the literal representative, projection
cancellation and array algebra into separate lemmas; use typed `congrArg₂`
and transitivity instead of rewriting deeply nested dependent Sobolev terms.
Three commented declaration-local heartbeat limits are 400000; none exceeds
that value. The module's final direct Lean run is silent.
