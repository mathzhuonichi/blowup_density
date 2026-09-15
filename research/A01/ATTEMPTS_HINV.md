# Lane 173 — residual row (iv), HANDOFF P9a

## Route β: closed

`AprioriInvariance.lean` defines `HasAprioriBoundInv` with exactly the old
window/data/Duhamel quantifiers, followed by angle invariance as an additional premise.
`HasAprioriBound.toInv` is the forward implication. The reverse implication is neither
assumed nor claimed.

The new core helper `forced_global_mild_core_of_boundInv` adapts the existing
`forced_global_mild_of_bound_invariant` induction. Its invariant is the full mild
equation **and** angle invariance. At the successor step, `hbound ... hsolu hinvu`
bounds the endpoint datum; after reaching S, `hbound ... hsol hinvu` bounds the final
path. This avoids any circular attempt to extract invariance from the bound.
`forced_global_of_boundInv` then restores all seven output clauses using
`forced_mild_divergenceFree` and `forced_ordinary_descent`; its conclusion is copied
token-for-token from `forced_global_of_bound_unconditional`. The theorem
`localTheory_on_prescribed_horizon_of_boundInv` is a thin alias whose conclusion is
copied token-for-token from `localTheory_on_prescribed_horizon`.

Exact reused declarations:
- A01 `exists_uniform_restart_time_invariant`, `gluePath_invariant`.
- `EulerQuadraticMildPasting.quadratic_mild_window_iff`, `glue_quadratic_mild`.
- `EulerTimePathGluing.gluePath` and `EulerBoundedMildContinuation.advance_grid`.
- `ordinarySobolev_angle` (the existing ordinary-cylinder datum invariance lemma).
- A01 `forced_mild_divergenceFree`, `forced_ordinary_descent`.

Failed direct reuse: merely passing the restricted bound where the old bound is
required leaves the invariance premise. The temporary Lean probe used
`intro T hT hTS u hsol; exact hb T hT hTS u hsol` to try to prove the old predicate
from the new one. Actual diagnostic (probe removed after preserving this record):

```text
../research/A01/hinv_direct_probe.lean:22:2: error: Type mismatch
  hb T hT hTS u hsol
has type
  (∀ (θ : AddCircle 1) (t : ↑(Icc 0 T)), (sobolevTranslation 1 (q + 1) (0, θ)) (u t) = u t) → ‖u‖ ≤ R
but is expected to have type
  ‖u‖ ≤ R

```

The new continuation induction resolves this exact problem by passing `hinvu` at
both bound applications. No failed declaration remains in the delivered module.

## Route α: inspected, not closed or needed for β

Search used `rg` by file name and declarations, followed by the required
`grep -rn --include='*.lean' --exclude-dir=.lake` over **all** of
`Section4/{D01,A03,A04,A01,C01}`, `NSFormalization/Source`, `FormalPatched`, and both
vendors. Search terms included `mild_solution_unique`, `quadratic.*unique`,
`unique.*quadratic`, `source_translation`, `heatKernel_translation`; candidate
files with `Mild`, `Uniqu`, and `Translation` in their names were also examined.

The covariance API is present:
- `ForcedCylinderLocal.source_translation` (`Source/ForcedCylinderInvariant.lean:19`)
  commutes the actual forced projected nonlinear source with translation, provided
  the force is fixed.
- `ForcedCylinderLocal.heatKernel_translation`
  (`Source/ForcedCylinderTranslation.lean:64`) and `heatOperator_translation`
  commute heat evolution with translation.
- `ordinarySobolev_angle` makes both initial data and every force slice invariant.
- `EulerVolterraConvolution.mild_solution_unique`
  (`vendor/NavierStokesAndEuler/Euler/VolterraUniqueness.lean:22`) is uniqueness
  in a ball **with** `kernelMass T k * L < 1`. Inspection of its full type shows
  why this is not a direct whole-horizon proof for arbitrary T.
- `MNS2.EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.unique`
  (`FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:119`) is unrestricted, but
  consumes its own contract's mild equation. The concrete specialization
  `MNS2.r3EndpointSafeProjectedMildSolution_unique` at line 231 uses
  `R3HsVelocity 3` and the unforced projected equation, not this forced cylinder
  `quadraticDuhamel` equation. No conversion was constructed in this lane.
- `A01.restart_window_invariance` already provides the local covariance/uniqueness
  argument, and `exists_uniform_restart_time_invariant` packages its safe window.

Thus α would still require extending the cylinder uniqueness argument over all
windows of an arbitrary given solution (or a contract conversion). This is an
unperformed proof extension, **not** a claim that global uniqueness is impossible
or absent throughout the tree. There is no α compiler error to quote: this route
was rejected at signature inspection, before attempting that extension. The actual
failed β shortcut diagnostic is recorded above. `Propagation.lean` is the scalar
Grönwall skeleton and does not itself establish angle invariance.

## Verification and scope

All five declarations print exactly `[propext, Classical.choice, Quot.sound]`.
The conformance `example` uses concrete zero datum/force, ν = 1, q = 6, S = 1 and
calls `forced_global_of_boundInv`, checking both paths and all seven clauses. Its
`HasAprioriBoundInv` premise remains the explicitly unsupplied uniform a-priori bound.
The separate `fix173_consumer_match.lean` probe is a verbatim full-conclusion
restatement closed by `exact forced_global_of_boundInv ...`.
No new heartbeat option, admission, or change to existing Lean modules.
The imported pre-existing invariance machinery has larger heartbeat settings;
this lane adds none. Remaining A3 energy, carrier, endpoint and uniform-bound
supply obligations are unchanged. Future supply work can target the new predicate
and apply the new full consumer directly.
