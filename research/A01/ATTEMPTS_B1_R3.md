# Attempts and proof record — B1 rung R3 (lane 178)

## Successful route

The proof stays in the genuine cylinder Sobolev scale until the time bootstrap is complete.
At target order `k ≥ 6`, `reducedResidualPath_eq` rewrites R2's residual as

```text
ν Δ (u restricted to H^(k+2))
  + P_k (f restricted to H^k - B_k(u restricted to H^(k+1), u restricted to H^(k+1))).
```

`advection 1 hk` is already a bounded bilinear map.  Mathlib's
`ContinuousLinearMap.hasDerivWithinAt_of_bilinear` therefore supplies the literal product
rule, with no pointwise representative and no tame-norm limit argument.  The Laplacian is a
bounded linear map from order `k+2` to `k`.  Induction through
`contDiffOn_succ_iff_derivWithin` proves `cylinderPath_contDiffOn` in the exact range
`k + 2*j ≤ q+1`.

The datum descent is a second induction on `j`.  The within derivative of an invariant
cylinder path is invariant: apply the bounded translation map to the derivative and use
`derivWithin_congr` plus uniqueness on `Icc`.  Its ordinary path is the adjoint descent of
its cylinder value.  R1 selects continuous data for the original path; the induction
hypothesis selects a smooth datum path for the derivative.  After lowering both to order
zero, datum uniqueness identifies them with `orderZeroDatumCLM`.  The existing injective
path-derivative theorem then lifts the derivative through `lowerVectorL p 0`.  Taking
`k = max 6 m` and lowering once more gives
`max 6 m + 2*j ≤ q+1`.

`reducedResidualDerivativePath` and `residualPath_hasDerivAt` separately record the first
differentiated residual:

```text
ν Δu_t + P(f_t - B(u_t,u) - B(u,u_t)).
```

## Alternatives rejected

- Differentiating Fourier data coordinate-by-coordinate was unnecessary and would duplicate
  the order-zero/injective-lift mechanism already verified in R2.
- Rewriting advection through the dependent `restrict_asymmetricTransport` compatibility
  theorem repeatedly exhausted elaboration heartbeats.  The final `restrict_advection` proof
  applies `value_injective` and compares the literal scalar-product values instead.
- Broad dependent `rw` chains across Sobolev restriction witnesses caused deterministic
  `isDefEq` timeouts.  The final proofs pin the target order explicitly and use short `calc`
  chains.  The six documented per-declaration heartbeat budgets are `400000`, never global.
- A physical representative/C01 residual route is circular here: the relevant C01/A04
  results start from `ClassicalSolutionR`, while R3 is part of constructing that solution.

## Force bridge and all-order search

The mandated recursive search was run with `grep -rnE` over all of
`Section4/{D01,A03,A04,A01,C01}`, `Source/`, `Paper1/`, `Paper3/`, `vendor/`, and
`FormalPatched/`.  The relevant hits were inspected, including:

- `Section4/A01/ForceBridge.lean:64`, where `forcePath_of_memForceR` supplies
  `C01.forcePath hf` and only `∀ n, Continuous (fun t => (F t).jetLp n)`;
- `Section4/D01/ForceClass.lean:96-190`, where `MemForceR` supplies a `C∞` *datum* path at
  every order;
- `Euler/CylinderPathProduct.lean`, which constructs spatial products but does not convert a
  smooth ordinary angular datum path into time smoothness of `sobolevPath F hF q`;
- `Section4/A01/Horizon.lean:97-154`, whose `HasAprioriBound` and prescribed-horizon theorem
  are stated at one fixed cylinder order.

No declaration in those searched roots proves

```text
MemForceR f -> ContDiffOn ℝ ∞
  (extendPath S hS.le (sobolevPath (C01.forcePath hf) hF q)) (Icc 0 S),
```

and no declaration turns `∀ q, HasAprioriBound ...` into compatible order-`q` carriers
realizing one fixed ordinary path `U`.  Consequently the module exposes the cylinder force
smoothness as `hfs` for the finite arbitrary-`j` result, proves the unconditional `C¹` result
from the original Horizon continuity input, and states the all-order theorem under an honest
`hall` hypothesis containing smooth forces, exact Duhamel carriers, angle invariance, and the
same ordinary `U` at every order.

The manuscript lines were read directly with
`sed -n '71,76p' paper/sections/appendix-a-local-theory.tex`; they state the repeated-time-
differentiation argument and one-sided initial derivatives, but do not provide the missing
formal bridge above.

## Elaboration incidents resolved

During development, before explicit order annotations were added, Lean inferred the order of
`ordinaryResidualPath` from the proof `hkq : k+4 ≤ q+1` and selected `m = k+2`.  The resulting
goal compared order-`k+2` and order-`k` residuals.  All such calls now specify `(m := k)`.
There is no remaining Lean error in the module.
