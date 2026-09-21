# Lane 199 — signed regularized energy and scalar envelope

## Outcome

Partial result, not A3-M2 closure. Neither `forcingFamilyBound_of_cylinder`
nor an unconditional `envelopeConversion_of_cylinder` has been proved.
No general-data choice of A is supplied. The new module proves the two ends
of the proposed route: the actual signed regularized identity, and the scalar
ODE/envelope construction. The signed limit and nonlinear estimates between
these ends remain unfinished.

## Positive results

`identity_jetLaplacian_pairing` sums the vendor's
`metric_second_derivative_identity` at the identity metric. The directional
coefficient operator is zero, proved by its norm bound, and the conclusion is
exactly the negative sum of all four first-derivative squares. No half-viscosity
estimate or Young absorption occurs here.

`full_word_energy_hasDerivAt` applies `family_energy_hasDerivAt` with identity
metric, zero transport/pressure, and the unaltered source, retaining its signed
pairing. `regularized_full_energy_hasDerivAt` supplies every derivative from
`regularized_word_hasDerivAt_clamped` on the actual quadratic mild path, at
all words through q+1. Its source is `sourcePath (D.comp (timeInclusion hTS)) u`.
These are finite-order statements on the given window, not statements about
an all-order constructor or a classical solution.

`energyComparison α b c t` is the explicit function

    exp(∫₀ᵗ α) * (c + b * ∫₀ᵗ exp(-∫₀ˢ α)).

For continuous α, it solves y′=αy+b at every real t, and y(0)=c.
It is the unique global pointwise differentiable solution with that initial
value: multiplying the difference of two solutions by `exp(-∫₀ᵗ α)` gives
a function with zero derivative and hence a constant zero function. It is
nonnegative for t≥0 when b,c≥0. The scalar envelope uses x=y²,
d=2y(k²y/(4ν)+b), g=ky/(2ν), with k=A*(16*low). Its dissipative inequality
is equality. The cylinder driver is continuous, and the closed-interval clamp
agrees locally with the global comparison at every interior point.

`finiteMildEnergy_of_rootComparison` uses exactly ONE analytic predicate,
`CylinderRootComparison`, whose full statement is in the module and report.
It directly asks for domination of the actual full-word root by the explicit
y above. It does not assume an energy envelope, an unspecified scalar ODE
solution, differentiability of the original root, or an extension of the mild
solution. This remains a substantial unproved analytic statement.
The conditional EnvelopeConversion, MildGronwall, and base-family assembly
are supplied with unchanged downstream conclusions.

`ForcingFamilyBound` is not a second premise of this conditional chain:
`CylinderRootComparison` implies `FiniteMildEnergy` directly. Its
source/pressure identification and quantitative commutator estimate are,
however, what a general-data proof of `CylinderRootComparison` needs
internally before passing the signed regularized identity to the scalar root
comparison. Lanes 200/201 split those two general-data targets.

## Satisfiability

The conformance file proves CylinderRootComparison on zero data for every
competitor by mild uniqueness, every q≥6, every E≥0, and every A.
It then applies the new finite-energy and conversion theorems at
E=mildNormConstant q and A=1. Neither the residual nor the desired energy
predicate is an assumption of these examples.

Nonstationary scalar checks give y=1+t and y=t when α=0 and b=1.
The scalar construction consequently permits vanishing initial energy and
nonconstant forcing responses. These are scalar witnesses; they are not a
nonzero Navier–Stokes proof of the residual.

## Negative routes

1. A signed forcing pairing cannot bound its family norm. The conformance
   check uses e=1 and forcing=-2: the signed pairing is ≤0, while
   root*norm(forcing)>0. Thus the A03 tensor pairing route alone cannot prove
   lane 198's ForcingFamilyBound. It still needs its own commutator family
   norm estimate and the identification of source+transport+pressure.
2. The nonnegative root estimate with viscosity already dropped cannot
   restore a *prescribed* positive gradient: root=1, Z=0, d=0, ν=g=1 fails
   the dissipation inequality. This does NOT refute EnvelopeConversion,
   whose g is existential. The new scalar construction supplies that g.
3. Setting x=root² is not justified: TimeLp regularity does not supply its
   everywhere-interior derivative. The construction instead differentiates
   the explicit scalar ODE solution.
4. The regularized signed identity alone does not identify its limiting
   physical/cylinder tensor pairing. The finite real tame bound also needs
   its finiteness hypotheses. These bridges and the signed-limit comparison
   were not proved, and no classical-solution energy lemma is used to bypass
   them.

The vendor forcing definitions, signed derivative identities, the reviewer
198 route, A03.outerProductTame, A04.outerSobolevNormAt_le and
A04.inner_energy_Rhigh were inspected. Searches across
Section4/{D01,A03,A04,A01,C01} and vendor transport/commutator modules did not
supply a directly applicable proof. This is a report of unfinished work,
not a claim that no useful commutator machinery exists.

## Compiler diagnostics (resolved)

```
Invalid field `exp`: The environment does not contain `Continuous.exp`
```
Use `Real.continuous_exp.comp`.

```
Type mismatch: After simplification, term HasDerivAt.pow (hyd t ht) 2 ...
Real.normedCommRing.toCommRing.toAddCommGroup ... Real.instAddCommGroup
```
The real module presentations and derivative expression were handled with
`convert ... using 1`, reflexivity for the instance equalities, then scalar
normalization. No instance declaration was changed.

```
Application type mismatch: The argument J has type
SpatialJet 1 standardDirection 2 f
but is expected to have type
SpatialJet 1 EulerCylinderSobolev.standardDirection 2 ...
```
An unopened namespace caused autoImplicit to bind a new direction parameter.
Opening EulerCylinderSobolev fixes the actual direction. The final statements
are about the genuine standard cylinder directions.

```
linarith failed to find a contradiction
```
For the variation-of-constants derivative, multiply exp(P)*exp(-P)=1 by b
explicitly via `linear_combination`; the unmultiplied identity does not give
the needed polynomial relation to nlinarith.

There are no unresolved compiler errors. The analytic gaps are the explicit
comparison predicate and the original independent forcing-family target.

The module is silent under direct `lake env lean` checking. `lake build`
replays warnings from dependencies, not from this module. Change attribution
uses the three-dot lane diff against `origin/erenup/integration`; it consists
of one formalization module plus lane and review records.
