# Lane 227 — endpoint assembly attempts

## Scope and successful route

New implementation: `formalization/NSFormalization/Section4/R44/Endpoint.lean`.
Existing Lean modules, contracts, bindings, and tests were not edited.
The authorized existing Markdown updates are `R44_SPLIT.md` and `COMPARISON.md`.

The sole named analytic input is `RCritical2Differential w hf`. It contains one
real derivative function E', its interval integrability on every `0 ≤ b < T`,
and the S1 derivative plus eq:Rcritical2 inequality on `Ioo 0 T`. It does not
contain force-path assumptions, continuity, a prefix bound, an L³ gate, an H²
budget, a continuation clause, or the final conclusion. In particular, no
integrability at a possibly singular terminal T is required. This is the
compact-window interpretation of the split's `Pieces` integrability requirement.

The universal choices are explicit:

- `theta = min R43.criticalConst (1 / (100 * (A05.criticalL3Const + 1)^3))`;
- `C₂ = 2`, `C₃ = 4`;
- `radiusCoefficient = theta / (4*(C₃+1))`, `radiusRate = C₂+1`;
- `radius ν S = radiusCoefficient * ν^(3/2 : ℝ) * exp (-(radiusRate*ν*S))`.

These are fixed before ν, S, and f. Their positivity and radius smallness are
proved. The nonlinear S1c/S1d lane still owes the differential inequality at
these fixed choices; this lane does not assert that the inequality follows
from the PDE. The extra theta restriction leaves a small cubic-embedding
threshold; the endpoint uses only its positivity and the proven C01 gate.

The successful chain is:

1. Lower `MemForceR`'s order-two datum path with `lowerVectorL 2 (-1/2)`.
   Its norm is the physical B on future slices. This proves continuity.
2. Datum uniqueness makes every admissible negative-order datum path equal
   almost everywhere on `forceTimeMeasure`. Thus the infimum defining the
   force norm equals the eLpNorm of any one measurable realizing path.
   `D01.eLpNorm_two_sq`, the real-integral/lintegral identity, and restriction
   monotonicity prove `∫₀ᵇ B² ≤ forceNorm.toReal²`.
3. `energyVelocity_smooth` supplies Y's continuity on `[0,b]`. `projIcc`
   extends it continuously to all real times without assuming regularity
   outside the classical interval. Transfer derivatives by eventual equality.
4. Use `radius_forces_gronwall_small`, exponential monotonicity for `b ≤ S`,
   and `criticalSquaredNormBound_radius`. The conclusion is the stronger
   `Y ≤ theta*ν/2`, including the left endpoint and the closed compact window.
5. Use A05's homogeneous L³ embedding and the contractive
   Bessel-to-homogeneous map to bound the homogeneous norm by the actual
   inhomogeneous H^(1/2) norm. `R43.criticalL3_gate_enorm` closes C01's gate.
6. Transfer to A02's maximal family. Reuse `R43.maximal_h2TimeIntegral`
   (C01 V4, uniform Ioc budget, directed-union endpoint gluing). The resulting
   explicit zero-datum budget is
   `ofReal (32*L*forcePrimitive f L^2 + 32*(ν⁻¹)^2*∫₀ᴸ l2Sq(slice f t))`.
   The existing natural-square/rpow pin gives A04's finite integral.
7. Use unconditional `exists_maximal'`. If the lifespan is at most S, put
   L equal to its real value, assemble `SolvesBelow` at L, and apply
   `extendsBeyond_of_memForceR'`. Its strict inequality contradicts equality
   with the maximal lifespan. This proves `ofReal S < lifespan`, not infinity.

`rcritical2_endpoint` is an instantiation skeleton with an explicit universal
S1 provider as its first argument. No unconditional theorem or complete
`RCritical2API` instance has been manufactured.

## Failed elaboration attempts and fixes

- Opening both A02 and D01 wholesale made `MemForceR`, `IsSobolevPath`, and
  `forceTimeMeasure` ambiguous. Selective A02 opening and qualified
  `A02.MemForceR` fix this without changing any definitions.
- Using the order-zero path directly exposed the dependent coercion
  `RealVectorSobolev (↑0)` versus `RealVectorSobolev 0`. Simplifying the
  dependent local G separately introduced a new variable and disconnected its
  hypotheses. The existing R43 pattern uses order two; using that pattern
  avoids the elaboration issue and still lowers to the correct negative order.
- A bare `have hi := ... .mono Icc_subset_Ici_self` left the right endpoint
  unspecified. An explicit `ContinuousOn ... (Icc 0 S)` type fixes inference.
- Rewriting a datum-norm identity through the opaque-looking `C01.slice`
  spelling failed to find the physical lambda. `change`/`unfold C01.slice`,
  or `erw` at the zero spatial field, pins the intended expression.
- `simp [← ENNReal.rpow_natCast]` recursed while normalizing exponents.
  Use the existing `R43.enorm_npow_two_eq_rpow_two` directly instead.
- The gate's implicit radius parameter is named `c`, not `theta`.
  Supplying `(c := theta)` before the arithmetic prevents an unresolved
  metavariable from reaching `linarith`.
- `intervalIntegrable_const` is in the root namespace, not
  `intervalIntegral`; the zero derivative uses that theorem.
- The datum-norm identity imported by the conformance file belongs to R44,
  not D01. Qualifying it as D01 initially produced an unknown-identifier error;
  the final conformance file uses the actual R44 declaration.

No heartbeat or recursion-depth override was needed.

## Non-vacuity and conformance

`zeroSol_differential` explicitly uses `E' = 0`. The conformance file also
proves the actual zero-force strict smallness premise, and uses velocity
uniqueness to prove `RCritical2Differential` for **every** zero-force classical
solution. Its zero-force endpoint example therefore invokes the new conditional
endpoint theorem with a proved provider, not with an assumed premise.

`EndpointConformance.main` copies the Spec's final binders and Data vocabulary;
`EndpointConformance.nonDensityBallZero` uses exactly the same radius and the
specified breakdown-set contradiction. The radius formula is checked by rfl.
All 27 authored module declarations and all four conformance theorems are
individually audited: 31 reports, each exactly
`[propext, Classical.choice, Quot.sound]`.

## Validation

See `REPORT_227.md` for the final gate results. Local command outputs are in
`tmp/lane227/` (untracked). The module's direct Lean check has zero output.
Lake's aggregate build replays existing dependency warnings, while the new
module itself has no warnings. No proof-admission token or option override is
present in the authored Lean source.
