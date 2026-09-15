# Lane 164 independent source review

## Verdict and scope

Source verdict: ACCEPT for `SobolevTwo.lean` and `H2TimeIntegral.lean`, subject
to actual kernel compilation, exact original-Spec consumers, and transitive axiom
audit by the assigned Luna compiler. This reviewer ran no Lean commands and
edited no C01 source.

Read both modules, the three original fields in `research/C01/Spec.lean`,
D01 datum/jet equivalence and datum norm definition, A05 Hessian comparison,
and Mathlib's directed-union lower-integral theorem.

## Genuine datum norm and CH2

The source does not replace the order-two Sobolev norm with a spatial norm or
pointwise Fourier transform. `MemHInfty` supplies real angular data and smoothness;
the existing D01 equivalence reconstructs all square-integrable spatial jets.
For the resulting actual smooth L2 field Z, the order-zero derivative is bounded
by `l2Sq + laplacianSq`; first derivatives follow from integration by parts,
Cauchy–Schwarz and quadratic Young; each second directional derivative follows
from A05's proved Hessian/Laplacian identity. The recursive weak-derivative
witnesses are actual directional fields, paired by the genuine Schwartz weak
identity. No derivative membership is postulated.

`exists_isSobolevDatum_norm_le_sharp` at m=2 constructs an actual angular datum A
with squared norm at most `4^2*(l2Sq+laplacianSq)`. The actual `sobolevENorm` is
the infimum over these data; `sobolevENorm_le_of_isSobolevDatum hA` bounds it by
this inhabited datum norm. Raising the extended-real inequality to power 2 and
converting the finite norm gives exactly `CH2=16`. There is no empty-infimum or
`.toReal` infinity shortcut.

## Uniform time estimate and Cassembly

On every strictly earlier interval `(0,t]`, the true spatial comparison is
integrated. Velocity L2 energy is bounded by the actual energy budget at S using
its monotonicity; this gives `S*K(S)^2`. The integrated enstrophy estimate gives
`integral laplacianSq ≤ ν⁻¹*gradientSq(a) + 2*ν⁻²*integral forceSq`.
Multiplication by CH2=16 yields coefficients 16,16,32. Increasing the first two
to 32 is valid because S, K(S)^2, ν⁻¹, and gradientSq(a) are nonnegative.
Thus the single `Cassembly=32` is universal and correctly covers all three terms.

All conversions between real and lower integrals use explicit interval
integrability of velocity and Laplacian energy on the earlier slab. Forcing
squared L2 norm is continuous and integrable on the full finite `[0,S]` by the
actual `MemForceR` time regularity, and is nonnegative. The proof does not rely
on a junk real integral on an unproved domain.

## Terminal endpoint S=T

The final theorem retains the original `0<S≤T` hypothesis. It never applies
velocity regularity or an enstrophy estimate at S when S=T. Every auxiliary t
satisfies `t<S≤T`, hence `t<T`; all velocity slice uses, including the right
endpoint of `(0,t]`, stay strictly inside the solution domain.

The open terminal interval `(0,S)` is the countable directed union of `(0,q]`
for rational `0<q<S`. Density gives coverage, and max of two rational endpoints
gives directedness. Mathlib `setLIntegral_iUnion_of_directed` in
`MeasureTheory/Integral/Lebesgue/Basic.lean:646` indeed requires only a countable
index and directed sets; it does not require an unprovided measurability
hypothesis on the integrand. Taking the supremum of the uniform bound therefore
proves the exact lower-integral estimate through S=T. No terminal velocity value,
continuation, or smooth extension is assumed.

The zero-datum corollary uses the same constant 32; the true initial L2 norm and
gradient vanish, leaving forcePrimitive in K. This matches the original field.

## Consumer and validation requirements

The local raw-integral `gradientSq` requires the existing Frobenius gradient
bridge for literal Spec consumers; the author is adding those probes. The
remaining vocabulary is the established datum/energy vocabulary. All omitted
initial-class hypotheses are present in the Spec and unused by these stronger
source results, so they may be retained by consumers without a new assumption.

No compilation, axiom clearance, or full C01 registration is claimed by this
source-only review. Append actual assigned-compiler evidence before final handoff.

## Exact consumer source check

Read `axioms_h2_164.lean`: all three original fields retain their original
quantifiers, actual registered C1, and S≤T. The non-definitional gradient bridge
is applied explicitly in the general assembly. `terminal_finite` instantiates
S=T using `le_rfl` and deduces a strict finite bound via `ENNReal.ofReal_lt_top`;
it does not strengthen the hypothesis to S<T. Source conformance is ACCEPT.
The six requested axiom checks remain subject to the assigned compiler's output.

## Assigned-compiler evidence appended by lead

The lead inspected build r2 (SobolevTwo succeeds), build r3 (H2TimeIntegral
succeeds, LAKE_BUILD_EXITCODE 0), and probe_164_axioms_h2.log. All six requested
declarations report only propext, Classical.choice and Quot.sound, with no
probe errors. These satisfy the independent source review's build and axiom
conditions. The reviewer did not run Lean. Full contract registration remains
outside this proof lane.
