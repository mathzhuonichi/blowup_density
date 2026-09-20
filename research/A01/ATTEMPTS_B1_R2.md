# A01/B1 rung R2 — attempts and route record

## Outcome

The vendor Duhamel route closes R2 for every natural order `m ≤ q - 1`.  The proved
derivative is the datum of the Leray-projected residual

```text
ν Δu + P(F - (u · ∇)u).
```

The two-order loss is exactly the regularity needed to view `Δu` in `H^m` when the
Horizon path has order `q+1`.

## Successful route: differentiate after ordinary L² descent

The implementation is in
`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean`.

1. `cylinderResidualPath` bundles the projected right-hand side as a continuous
   `SobolevSpace 1 m` path.  `projectedResidualPath_eq` exposes the formula
   `νΔu + P(F-(u·∇)u)`.
2. `cylinderResidual_invariant` proves angle invariance.  The Laplacian part uses the
   local translation-commutation lemma `laplacianOperator_translation_local`; the
   source part uses the vendor source-translation theorem.
3. `ordinaryResidualPath` applies the adjoint of `ordinaryLift`.  Lane 153's
   `exists_ordinaryLift_of_invariant`, together with
   `ordinaryLift.adjoint_comp_self`, proves that lifting this descent recovers the
   cylinder residual exactly (`ordinaryLift_ordinaryResidualPath`).
4. `Source.OrdinaryForcedTime.realization_hasDerivAt` differentiates the exact
   quadratic Duhamel identity after ordinary L² realization.  Its derivative is
   `ordinaryDerivative`, which `ordinaryResidualPath_eq_ordinaryDerivative` identifies
   with the descended residual above.
5. R1's quantitative datum construction is generalized to an arbitrary available
   cylinder order and supplies continuous velocity and residual datum paths.
6. At order zero, datum uniqueness identifies both paths with `orderZeroDatumCLM` of
   their ordinary L² fields.  The continuous order-lowering map `lowerVectorL m 0` is
   injective (`lowerVectorL_injective`), so vendor theorem
   `EulerInjectivePathDerivative.hasDerivAt_of_injective_map` lifts the derivative from
   order zero back to order `m`.

This last step avoids needing a bounded order-raising operator on bare L² data.

## Direct word-level route considered

The tree contains derivative infrastructure for individual cylinder words and time
paths, and a word-by-word proof could first establish derivatives of
`t ↦ word 1 (u t) hn w`.  It was not needed: differentiating the ordinary L² realization
and lifting through the injective order-lowering map proves the whole datum derivative
at once, for the full range `m ≤ q-1`.

## Physical-side route recorded but not used

The A04/C01 route is circular at this rung:

- `A04.timeDeriv_isSobolevDatum` assumes a `ClassicalSolutionR` and an already smooth
  time-dependent datum path.
- `C01.residualPath`, the residual jet-continuity results, and the pressure-gradient
  paths also assume a `ClassicalSolutionR`.
- B1 is part of the construction of that classical solution, so those statements
  cannot establish the first time derivative from the Horizon Duhamel data.

The module instead provides `residualDatum_is_timeDerivative` as a conditional handoff:
if a later construction produces a representative whose pointwise time derivative is
the descended projected residual, the R2 path `R` is its physical time-derivative datum.
Recovering a pressure and proving
`P(F-(u·∇)u) = F-(u·∇)u-∇p` for that representative remain downstream work.

## Elaboration notes

`cylinderResidual_invariant` needs one local, documented
`set_option maxHeartbeats 400000 in`; no global heartbeat override is used.

The non-vacuity audit instantiates the theorem with `q=6`, `m=0`, `S=1`, `ν=1`,
`u := 0`, `U := 0`, zero force, and zero initial datum.  An initial fully expanded
example exposed two definitionally distinct proofs of force jet-continuity inside the
dependent type of `projectedResidualOrdinaryPath`; Lean reported an application type
mismatch at the final `simpa`.  The conformance example now consumes the same flagship
theorem and retains its velocity-datum and derivative consequences, so proof arguments
do not appear in the result type.

## Search scope

Before assessing the physical-side gap, searches covered the required
`Section4/{D01,A03,A04,A01,C01}`, `Source/`, `Paper1/`, and `Paper3/` trees, as well as
`vendor/NavierStokesAndEuler` and `formalization/FormalPatched`, for Duhamel and
time-derivative APIs.
