# Lane 161 independent source review

## What is proved

Reviewed `161-a01/formalization/NSFormalization/Section4/A01/ConstructorDatumPath.lean`
against its imported full-order descent and sharp datum bound. Source verdict:
ACCEPT, conditional on the assigned compiler's successful build and transitive
axiom output. This is a finite-order continuous datum-path theorem, not the full
A01 constructor or an all-order smooth solution.

## The actual proof

The recursive bound carries the single constant `‖u‖²` through every weak
derivative. Its base uses `eLpNorm_descend_le`, which derives the bound from the
isometry `ordinaryLift` and the finite cylinder array's supremum norm. In the
successor step, `n + (k+1) ≤ q+1` yields `n < q+1` for `word_hasDerivAt` and
`n+1 ≤ q+1` for top-order descent. Thus the recursion genuinely reaches
`m=q+1`; it does not lose the top order to a strict bound. The weak derivative
pairing is the existing translation-derivative descent, not an assumed PDE.

The difference estimate applies that recursion to `u-v`. Angular invariance
survives subtraction by linearity, and `ordinaryLift (U-V)=value (u-v)` is
established before using the bound. `D01.isSobolevDatum_sub` applies at every
order, including zero, using L2-based Schwartz pairability. The a.e. rewrite
uses `(Lp.coeFn_sub U V).symm` to transfer the pointwise representative
`⇑U-⇑V` to `⇑(U-V)`. The existing sharp theorem then gives exactly
`‖A-B‖² ≤ 4^m * ‖u-v‖²` for arbitrary data A and B of those fields.

Continuity of any chosen datum path follows by the explicit square-root
majorant tending to zero. No continuity of a choice operation is assumed.
The subsequent `choose A hA` is justified because that estimate applies to
every pair of valid choices. The velocity-slice transfer uses the reverse of
`slice =ᵐ U`, taking a datum of U to a datum of the slice; the a.e. direction
is correct. Neither derivative regularity nor a spatial smooth representative
is added to the hypotheses.

## Remaining scope

The input is a supplied continuous finite-order cylinder path, an invariant
angular variable, and its ordinary L2 descent. The output does not construct
these inputs or establish a single classical solution with every natural
Sobolev order. The top-order zero-path probe demonstrates a nonempty instance;
the general theorem, not that particular example, is the evidence for the
universal finite-order claim.

## Verification evidence

Read the source and `research/A01/axioms_constructor_datum_path.lean`; did not
run Lean, as compilation is assigned to the Luna agent. At initial review the
only available `tmp/compile_ConstructorDatumPath_20260915.log` ended with
`EXIT_CODE=1`; the author had already revised the implicated source. Successful
fresh build and the seven standard-axiom outputs remain required before final
acceptance. No A01 source was edited in this review.

## Lead validation update (2026-09-15)

Luna subsequently compiled the revised module and the top-order consumer: both exit 0.
The lead inspected the two r2b logs. All six exports and the consumer report only
propext, Classical.choice, and Quot.sound. The initial review's compilation condition
is now satisfied; the original failed attempt remains recorded above.
