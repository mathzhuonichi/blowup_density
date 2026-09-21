# Lane 164: ordinary H2 comparison and terminal time integral

## Target and current result

The compiled proofs close the three original C01 fields `sobolevTwoFourier`,
`h2TimeIntegral`, and `h2TimeIntegralZeroDatum`, with explicit constants
`CH2=16` and `Cassembly=32`. The time-integral hypothesis remains `0<S≤T`,
including S=T. The authoritative statements remain the original Section 4
paper and `research/C01/Spec.lean`; no revision draft is a proof dependency.
Compilation and all three exact-field consumers passed; the explicit terminal
finite-bound consumer also passed, with only the three standard axioms.

## Actual proof route

The old carrier-crossing blocker in `ENERGY_SPLIT.md` is superseded by the
already proved quantitative weak-derivative constructor in
`D01.FiniteOrderNorm`. Its genuine L2 Plancherel/isometry construction bounds
the angular datum; no pointwise Fourier transform of a non-L1 field is used.

`SobolevTwo.lean` constructs `HasWeakDerivsL2Bound z M 2` with
`M=l2Sq z+laplacianSq z`. Order zero is immediate. Each first derivative is
bounded using the physical Laplacian integration-by-parts identity,
Cauchy-Schwarz, and quadratic Young inequality. Each second derivative is
bounded by the existing `A05.integral_hessian_le`, a consequence of the actual
Hessian/Laplacian equality. The weak witnesses are the smooth directional
derivatives and their proved Schwartz pairing equations. The sharp order-two
datum construction gives `4^2*M=16*M`; its datum witnesses the norm infimum.

`H2TimeIntegral.lean` combines the preceding pointwise inequality with the
previous lanes' `l2Bound` and `enstrophyIntegralBound`. For each `t<S`, the
velocity energy integral is bounded by `S*K(S)^2`, and the Laplacian integral
by `ν⁻¹*gradientSq a+2*ν⁻²*forceSqIntegral(S)`. Nonnegativity allows the common
constant 32. Every real-to-lower-integral conversion has an explicit
integrability proof. The force is controlled on the full finite interval
through its established `MemForceR` regularity.

The open interval `(0,S)` is exhausted by the countable directed family
`(0,q]` for rational `0<q<S`. `setLIntegral_iUnion_of_directed` turns the uniform
earlier-time bound into the terminal lower-integral bound. This works without
a value, continuity, or integrability assumption on the terminal velocity,
and without an assumed measurable Sobolev norm path. The zero-datum instance
uses the same constant 32 and the actual vanishing initial energy terms.

## Original vocabulary and remaining scope

`axioms_h2_164.lean` contains all three complete original Spec consumers,
using the registered C1 and the existing non-definitional Frobenius gradient
bridge. A separate `terminal_finite` consumer instantiates S=T and produces
a strict finite lower-integral bound. These are proof consumers, not a newly
registered contract. Contract/API registration and the global Section 4
constructor/continuation assembly are not claimed by this batch.

## Verification

Only `/root/wave3_compile` (Luna high) runs Lean. Requested compilation of
`NSFormalization.Section4.C01.H2TimeIntegral` and then
`research/C01/axioms_h2_164.lean`. The first build reached two SobolevTwo
elaboration/tactic errors: inferring the summand in `single_le_sum` exhausted
the default heartbeat budget, and `simp` did not normalize `4^2` to `16`.
The summand is now explicit and the numeral normalization uses `norm_num`;
no mathematical assumption changed and no global heartbeat limit was raised.
The r2 log records a successful `SobolevTwo` build. The time-integral module
then had two API-name/argument-order errors (`add_le_add_left` and
`setLIntegral_mono_fun`); these were corrected using `add_le_add` and the
actual `setLIntegral_mono'` theorem. Final assigned-compiler evidence:

- `tmp/build_164_H2TimeIntegral_r3.log`: H2TimeIntegral built successfully;
  the lead also inspected `LAKE_BUILD_EXITCODE 0`. SobolevTwo had already
  built successfully in r2. Neither new module has a local warning.
- `tmp/probe_164_axioms_h2.log`: all three complete original fields,
  `terminal_finite`, `weakDerivsL2Bound_two`, and
  `lintegral_Ioo_le_of_Ioc` report only `propext`, `Classical.choice`, and
  `Quot.sound`; there are no probe errors.

The independent source review is in `REVIEW_H2_164.md`; its compilation and
axiom conditions are satisfied by this evidence. The lead manages the broader
regression checks and PR. No proof hypothesis was added to bypass the analytic
targets, and the proof author ran no Lean command.
