# Constructor force-scope review (lane 163, read-only Lean review)

## Finding: the old research target is too strong

Confirmed from the exact source types. `research/A01/probes/ctor158_full.lean`
`CarrierConstructorFull` accepts only
`F : Icc 0 S → SmoothL2Field Space` and continuity of every spatial `jetLp` path.
It retains the actual local-theory cylinder/ordinary carrier outputs, including
the Duhamel equation, but asks for a `ClassicalSolutionR` with `S<T` whose velocity
agrees a.e. with U at every time in `[0,S]`.

`A02/SolutionClass.lean:122` requires that velocity to be jointly
`ContDiffOn ℝ ∞` on `[0,T) × R³`; each interior time slice at a fixed spatial point
is therefore smooth in time. Continuity of the forcing's spatial jets does not
supply its time derivatives. This is a mismatch in the research target itself,
not merely a missing proof lemma. The target is a Prop definition and
`rows_from_constructor_full` assumes it; neither declaration is a proved
constructor, and no claim of kernel inconsistency follows from this finding.

## Mathematical counterexample route (NOT formalized in Lean)

Choose an interior time `t* ∈ (0,S)`, viscosity ν>0, and a nonzero compactly
supported smooth divergence-free vector field W on R³, for example the curl of
a suitable compactly supported smooth vector potential. Let
`α(t)=|t-t*|^(3/2)`, a C1 function that is not C2 at t*, and put
`v(t,x)=α(t) W(x)`.

Define the ordinary forcing at each time by the exact zero-pressure NS residual:
`F(t)=α'(t) W - ν α(t) ΔW + α(t)^2 (W·∇)W`.
Each spatial field is smooth and compactly supported. Every spatial L2 jet path
is continuous in time because α and α' are continuous. The initial datum
`a=α(0)W` is smooth and solenoidal. For each fixed finite q the corresponding
ordinary Sobolev path and its constant-angle lift are continuous and bounded
on the compact interval, so R can be chosen to bound the supplied cylinder path.
The lift is angle invariant and divergence free. The forced evolution is a
strong C1 evolution in every finite Sobolev space; its variation-of-constants
identity gives the projected mild/Duhamel equation. One could instead take the
Leray projection of F if desired; projection does not restore time C2 of v.

This paragraph describes how to instantiate the concrete Duhamel operators; it
has not been encoded or kernel-checked as a counterexample to the Lean Prop.
The mathematical obstruction does not depend on an endpoint extension argument:
it occurs at the interior time t*.

If the old constructor produced w, then at each time its spatially continuous
velocity and `α(t)W` would agree a.e., hence everywhere. Pick a component and point
with `W_i(x0)≠0`. The equality
`w.velocity_i(t,x0)=α(t)W_i(x0)` forces α to be C∞ near t*, since w is jointly C∞,
contradicting the choice of α. The existential freedom to choose new a' or f'
(and pressure) cannot repair this obstruction: it is already in the required
velocity matching. Even reducing the required output horizon to S would not
remove this interior-time defect.

## Correct scope for the original A01 parent proposition

`research/A01/Spec.lean` `LocalTheoryAPI.solution` takes actual
`a ∈ initialClassR` and `MemForceR f`, and returns a solution with those very
inputs a and f. `A02/SolutionClass.lean:100` defines `MemForceR f` with both:

- joint `ContDiffOn ℝ ∞ f futureDomain`;
- for every Sobolev order a realizing datum path G that is itself
  `ContDiffOn ℝ ∞` on nonnegative times, with the prescribed L1/L2 time integrability.

Thus the original Section 4 parent has materially stronger force regularity than
the old carrier-only research target. The parent is not refuted by the route above.
Its `ManuscriptLocalRegularity` additionally asks for all-order smooth datum
paths, so merely recovering continuous velocity datum paths does not fulfill it.

For a replacement research target, supply actual `f : SpaceTimeField` with
`hf : MemForceR f` and identify the finite-window carrier force with its true
slices, preferably `∀ t, (F t).field = fun x => f (↑t,x)` (or a.e. equality plus
the already available spatial continuity if a carrier-level version is needed).
Likewise retain the actual initial datum link, e.g. the smooth carrier's field
is the specified initial a. The conclusion must solve the equation with that
same a and f, rather than existential unrelated a' and f'.

Existing supply for this identification is `C01/JetPaths.lean`:
`forcePath hf`, `forcePath_field`, `forcePath_jetLp_continuous`, built from the
actual force-class hypotheses without assuming a classical solution. These
show how to feed local theory, but their continuous output alone must not erase
the stronger `hf` during the later time-derivative bootstrap. Reusing the
underlying force-class data or an appropriate lower-level force module avoids
making time smoothness a new target-shaped hypothesis.

This correction is necessary, not a completed constructor proof. Common
all-order regularity, the time bootstrap, actual pressure and momentum recovery,
and any extension past S still need proofs. For the basic LocalTheoryAPI one
may choose a smaller positive local horizon; the carrier campaign's separate
`S<T` requirement requires a real extension theorem and must not be obtained by
choosing the number S+1. No target, contract, or existing Lean declaration was
changed by this review.

## Impact on lane 163

None. The c6 carrier descent uses only lift compatibility and the genuine
cylinder divergence constraint; it does not consume CarrierConstructorFull,
force continuity, or force time smoothness. Its pointwise corollary explicitly
requires an actual smooth representative, and does not claim to construct one.
