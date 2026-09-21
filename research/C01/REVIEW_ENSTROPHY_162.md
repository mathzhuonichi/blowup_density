# Lane 162 independent source review: EnstrophyIdentity

## Verdict

Source review: ACCEPT for the enstrophy identity and its mathematical hypotheses.
This verdict is conditional on the assigned compiler passing the module, the
literal Spec-field consumer, and transitive axiom audit. I did not run Lean.
The author is adding the exact Spec consumer using the existing gradientSq bridge.
No C01 source was edited by this reviewer.

## Statement, signs, and coefficients

Compared `research/C01/Spec.lean` field `enstrophyIdentity` (line 487) against
`Section4/C01/EnstrophyIdentity.lean` theorem `enstrophyIdentity`.
Both differentiate the squared gradient norm and have derivative
`2*advectionWork - 2*ν*laplacianSq - 2*pairing(force,laplacian velocity)`.
The factors and signs follow directly from `-2*inner(laplacian u, ∂t u)` and
`momentum_split_toLp`: `∂t u = ν*laplacian u - advection - pressureGradient + force`.
In particular the forcing term is negative and the nonlinear term positive;
neither was replaced by an inequality or absolute value.
The helper pairing identity has its minus sign on the Laplacian side, matching
ordinary integration by parts. The factor 2 arises from differentiating squared
L2 norms of the three first derivative fields.

The theorem assumes a classical solution, `MemForceR f`, and interior time.
It drops the Spec's unused viscosity positivity and initial-class hypotheses,
which strengthens the result and permits the original field to consume it.
It does not add a `HasSmoothSobolevPath`, datum-path, pressure orthogonality,
time-derivative continuity, compact-support, or other smoothness rider.

## Pressure and time regularity

Pressure cancellation is not asserted from the word "pressure":
`gradient_mem` is supplied with the actual potential `w.pressure (t,·)`, its
proved slice smoothness, and `pressureGradientField_eq_gradient`.
Velocity solenoidality is supplied by `smooth_mem_solenoidal` using the actual
classical divergence equation (`velocitySliceField_divergence`).
`word_pressure_pairing_zero` preserves both closed Helmholtz subspaces under
spatial words; at one derivative, summing and integration by parts yields
`inner(laplacian u,pressureGradient)=0`.

The all-order jet-continuity assumptions of the generic time-differentiation
helper are discharged in `enstrophyDerivative_shift` by existing classical
velocity and temporal-slice path theorems. The temporal derivative path is used
only on `[c,S]` inside `(0,T)`. The chosen window `c=t/2`, `S=(t+T)/2` is valid
for every `0<t<T`. The clamp is removed by local eventual equality and the
translation is undone by the chain rule. There is no claim of endpoint
`HasDerivAt`, nor dependence on an extension of the solution past T.

## Vocabulary and exact consumer

The local `EnergyBounds.gradientSq` is the raw integral of the sum of three
squared directional derivatives. The literal Spec uses the squared norm of its
PiLp gradient tensor. These are equal by the existing PiLp norm-square bridge,
but are NOT definitionally equal. The exact Spec consumer must invoke that bridge.
This is a binding/consumer obligation, not a mathematical gap in the source theorem.
The author confirmed it is included in the planned consumer probe.
`laplacianField_eq_lap` identifies the genuine carrier Laplacian with A05's
coordinate Laplacian. Local `laplacianSq`, `advectionWork`, and `pairing` then
match the respective Spec definitions via the established vocabulary.

## Verification status and limitations

Read the complete new identity module, exact original field, and relevant
`EnergyBounds`, `Trilinear`, `MomentumCarrierB`, `Vocabulary`,
`Euler.OrdinaryWordConstraints`, and `Euler.OrdinaryWordTime` declarations.
The new module contains no proof placeholders. Transitive axiom clearance cannot
be established by source scanning; the assigned Luna compiler must provide
`#print axioms` output restricted to `propext`, `Classical.choice`, `Quot.sound`.
No compiled or rendered verification is claimed here. Later additions concerning
enstrophy inequalities or integrated bounds are outside this identity review.

## Addendum: EnstrophyBounds source review

Reviewed the full `EnstrophyBounds.lean` module against the original differential
field and the integrability clause of the integral field. Source verdict: ACCEPT,
with the same outstanding compiler/axiom/exact-consumer qualification above.

The smallness condition is unchanged: `ofReal gradientL6Const * criticalL3 ≤
ofReal (ν/4)`. `advectionWork_abs_le` combines the registered extended-real
trilinear estimate with the proved Laplacian norm identity. Conversion through
`ofReal_le_ofReal_iff` uses nonnegativity of the right side, so no invalid
conversion from extended-real infinity to a real number is made.

The forcing estimate is the real L2 Cauchy–Schwarz inequality followed by
`F*L ≤ (ν/4)*L² + ν⁻¹*F²`. Its proof multiplies by strictly positive ν and uses
`(ν*L-2*F)² ≥ 0`; this verifies the coefficient exactly. The negative force
pairing is bounded above by its absolute value. Combining the identity with
`work ≤ |work| ≤ (ν/4)*laplacianSq` spends ν/2 on each of the two doubled terms,
leaving `E' + ν*laplacianSq ≤ 2*ν⁻¹*l2Sq(force)`. Thus `CRH1=2` is correct,
independent of t, ν, the solution, and the data. `HasDerivAt.unique` aligns the
arbitrary derivative E' with the identity's actual derivative.

Both continuity lemmas use existing classical-solution data at the initial
endpoint. Laplacian energy is the squared norm of the genuine continuous L2
Laplacian path, identified with its physical integral. Gradient energy is the
finite sum of squared norms of three genuine first-derivative paths. The local
raw-integral gradient vocabulary still needs the existing PiLp bridge when
consuming the literal Spec field. Neither continuity theorem assumes the desired
real energy continuity or imposes an additional smooth-path rider.

`intervalIntegrable_laplacianSq` obtains continuity on the compact unordered
interval from `0≤t<T` and invokes `ContinuousOn.intervalIntegrable`. This is a
real interval-integrability proof, not a `.toReal` finiteness shortcut or an
identity involving Mathlib's default integral value. It also covers t=0.
The spatial energy identities rely on actual L2 fields and their inner products;
so the real pairings used by the enstrophy identity are honest integrals as well.

This module does not yet prove the integrated inequality itself or identify the
initial gradient term with the datum. Those obligations remain for a following
module; only the exact differential bound and the two continuity results plus
Laplacian interval integrability are covered by this addendum.

## Final addendum: integrated enstrophy bound

The author subsequently added `enstrophyIntegralBound`; the earlier scope note
about the integrated inequality is superseded by this addendum. Source review:
ACCEPT, still subject to actual kernel compilation and axiom audit.

Compared the new conclusion with Spec's complete integrated field: the actual
`IntervalIntegrable` conjunct, the coefficient ν on dissipation, initial
`gradientSq a`, constant `2*ν⁻¹` on forcing, and the `Ico 0 t` smallness domain
all agree (with the fixed choice `CRH1=2`).

The proof uses Mathlib `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`
(`FundThmCalculus.lean:1068`), whose derivative hypothesis is only on `Ioo 0 t`.
At each such s, the classical identity applies since `0<s<t<T`, and the required
smallness follows from `Ioo 0 t ⊆ Ico 0 t`. Hence no unprovided smallness at t,
derivative at 0, or differentiability beyond T is required. The theorem accepts
`0≤t`, and its equal-endpoint branch handles t=0 directly, with vacuous derivative
conditions and zero interval integrals.

The upper bound integrand is genuinely integrable: continuity of force L2 norm,
then squaring, yields continuity and integrability of force `l2Sq` on `[0,t]`;
the already proved Laplacian continuity supplies its counterpart. Linear
combination gives the integrable majorant demanded by Mathlib. Integral
subtraction and constant extraction use those two explicit interval-integrability
proofs. There is no need to assume the nonlinear derivative expression itself
integrable, because the exact Mathlib comparison theorem permits an integrable
majorant. The initial substitution is the function equality
`slice w.velocity 0 = a`, proved directly by `funext w.initial`, so replacing its
gradient energy is justified without a separate derivative-at-initial-time claim.

Also read `research/C01/axioms_enstrophy162.lean` identity/differential consumers:
they retain all original quantifiers, use `uniqueness_toA02` for the same actual
solution, and explicitly apply the existing Frobenius-to-raw gradient bridge.
Their declared `#print axioms` checks still require the compiler output; the
integrated consumer was being added at review time.

## Lead validation update

The lead inspected Luna's r4 module and exact-consumer logs: BUILD_EXIT_CODE=0
and PROBE_EXIT_CODE=0. All three original-field consumers and the five auxiliary
exports report only propext, Classical.choice, and Quot.sound. This satisfies
the compilation and axiom conditions of the independent source review above.
The historical failed attempts remain recorded in ATTEMPTS_ENSTROPHY_162.md.
