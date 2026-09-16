# Lane 210 — horizon uniformity: positive results and failed routes

## Scope and checkout

Read CLAUDE.md, NEXT_SESSION.md, HANDOFF §0 / §2 P7, Spec.lean:300–345,
appendix-a-local-theory.tex:140–157, REPORT_193.md, REVIEW_207 and the top
40 LESSONS lines. The requested REVIEW_207 §5 does not exist in this checkout;
the relevant remaining-API discussion is §3 (especially its H¹ bullet).
LocalSolution.lean / localHorizon are absent. `constructor_of_base` is a theorem
in `research/A01/probes/a01_constructor_unconditional.lean`, not an export of
TameAssembly.lean. No sibling worktree was read or changed.

## Successful formalization

`HorizonUniform.lean` has eight named declarations, all audited with exactly
`[propext, Classical.choice, Quot.sound]`:

- `HorizonLowerBoundH1 horizon`: obligation only, with the field body copied
  token-for-token from Spec.lean. The audit proves definitional equality to
  the same formula using the canonical contract vocabulary.
- `HorizonLowerBoundH7L1 horizon`: separate unresolved obligation; not a theorem.
- `picard_ballBound_mono`: `0 ≤ r → r ≤ R → C.ballBound r ≤ C.ballBound R`.
- `picard_ballLipschitz_mono`: `r ≤ R → C.ballLipschitz r ≤ C.ballLipschitz R`.
- `picard_budget_mono`: for `T ≥ 0`, both strict budget inequalities transfer
  along `M ≤ M'` and `L ≤ L'`.
- `exists_uniform_H7_coefficient_horizon`: for fixed `ν>0`, `S>0`, `R≥0`,
  `M,L : ℝ`, one `0<δ≤S` works for every coefficient bundle with
  `C.ballBound (R+1) ≤ M`, `C.ballLipschitz (R+1) ≤ L`, and every cylinder
  datum `a : SobolevSpace 1 7` with `‖a‖≤R`. The result is an actual mild
  solution on `[0,δ]`, norm at most `R+1`, with the specified initial value
  and the exact vendor quadratic Duhamel equation.
- `exists_uniform_H7_sup_force_horizon`: specializes to the actual forced
  Navier–Stokes coefficient bundle, choosing δ before **both** the datum and
  a force path `F : C(Icc 0 S, SobolevSpace 1 6)` satisfying `‖F‖≤B`.
- `uniform_H7_zero`: invokes that uniform theorem with `R=B=0`, `S=1`, zero
  datum and zero force. The nonlinear convection operator is retained.
  The audit also checks physical zero datum / force class membership.

Both budgets use `massν(T) = T + 2*parabolicConstant ν*sqrt T`, whose
nonnegativity follows from `parabolicConstant_nonneg` and `Real.sqrt_nonneg`.
Scalar monotonicity uses `mul_le_mul_of_nonneg_left`, `add_le_add`, and
`pow_le_pow_left₀`. The vendor's time monotonicity is
`EulerUniformHeatLocal.parabolic_mass_mono`, proved using
`Real.sqrt_le_sqrt`; our common-interval proof does not need to shrink δ.
The kernel identity is `parabolicKernelBound_integral`, used with
`kernelMass` in `SobolevHeatVolterra.lean` and MildUniqueness.lean:181–182.
We call `exists_positive_time_budget ν M L 1 S` **once before** C and a,
then `exists_viscous_mild_solution`, rather than choosing a new existential
horizon for each datum.

The force specialization uses C₀ = coefficients of the zero path,
`M = ‖C₀.projection‖ * (B + ‖C₀.quadratic‖*(R+1)^2)` and
`L = C₀.ballLipschitz (R+1)`. Projection and quadratic operators are
independent of the force, the linear term is zero, and `‖-F‖ = ‖F‖`.

## Failed route 1: even H⁷/L¹ does not match the vendor budget

`QuadraticCoefficients.lean` defines

```
C.ballBound R = ‖C.projection‖ *
  (‖C.forcing‖ + ‖C.linear‖*R + ‖C.quadratic‖*R^2)
C.ballLipschitz R = ‖C.projection‖ *
  (‖C.linear‖ + 2*‖C.quadratic‖*R)
```

These are continuous-map **sup norms on the whole prescribed interval**.
`ForcedCylinderLocal.coefficients` has forcing `-F`, zero linear term,
and fixed Leray/advection maps. `QuadraticHeatLocal.exists_local_quadratic_mild`
uses BOTH `massν(T)*ballBound R < 1` and `massν(T)*ballLipschitz R < 1`,
with radius `‖u₀‖+1`. The uniqueness call with `M=0` in lane 188 does not
supply the ball-invariance inequality needed for existence.

A global `forceSobolevENormL1 7 f ≤ K` does not bound the sup norm of the
order-6 force path. Spatial lowering cannot repair this temporal mismatch.
For a fixed smooth spatial field g and a smooth bump φ supported in (1,2),
`f_n(t,x)=n*φ(n*t)*g(x)` has a fixed time L¹ H⁷ norm and unbounded time
sup H⁶ norm on [0,1]. Each individual force is smooth and has finite
all-order L¹ and L² norms, as required by MemForceR. This is an explanatory
analytic example, not a Lean counterexample to local existence.

Thus the requested theorem `horizon_lower_bound_H7` was **not proved**.
It is not renamed to a theorem with a stronger time-norm hypothesis.
A forced Picard argument estimating the H⁷ force by its L¹ H⁷ norm,
with a larger radius depending on the integrated force, could address this;
that is new analysis, not the stated ballLipschitz monotonicity argument.
Physical Sobolev norm comparison and constructor/horizon integration also
remain outside the proved cylinder result.

## Failed route 2: a chosen witness need not be uniformly large

`exists_positive_time_budget` chooses ε from a neighborhood of zero and
returns ε/2. The theorem guarantees the two inequalities, not monotonicity
of that choice in its parameters. Existence of a common suitable δ proves
that a uniform horizon can be selected; it does not prove `δ ≤ S` for an
arbitrarily selected witness S. A future localHorizon must be selected with
the uniform guarantee in its specification (or be suitably maximal).
No claim of a lower bound on lane 208's absent function is made.

## Failed route 3: H¹ and circular persistence

Searched Section4/{D01,A03,A04,A01,C01} for uniform/restart/horizon/lifespan
and H¹ local suppliers; opened Continuation.lean, ContinuationInvariant.lean,
Horizon.lean, ForceCap.lean and the vendor uniform restart theorem.
The existing restart statements fix the force path and require q≥6,
with order-(q+1) data. `hb_of_base''` requires an actual base mild solution
on the given S. Grönwall on that S bounds high norms in terms of their
initial high norms and force high norms. It neither controls high initial
norms from an H¹ ball nor provides a common existence interval. Using it
as H¹ local existence would be circular.

`vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean` explicitly takes
`u0 : R3HsVelocity 3`; its nonlinear operator is
`r3ProjectedConvectionH3ToH2`. The lifespan depends on the **H³** norm,
not H² or H¹, and the displayed theorem is unforced. H² is the source space.
A search finding this lifespan is not a proof of the forced H¹ contract.

Two owner options, neither implemented as a contract change:

1. Commission genuine forced quantitative H¹ local theory plus same-interval
   smooth persistence and horizon selection. H³ local theory is a possible
   lower-cost restart supplier, but still does not prove the unchanged H¹
   field; HeliCorgi additionally needs forced/carrier/persistence adapters.
2. Owner-authorized V2: state uniformity at an order and temporal force norm
   actually supported. Merely changing `1` to `7` while retaining L¹ does
   not fix the gap found here. A04's only recorded consumer (REVIEW.md M5)
   can use any fixed sufficiently regular order: the appendix:146–150
   bounds every H^m norm up to S and the fixed smooth force has a finite
   sup H^m bound on [0,S+1]. Thus fixed-force/sup-force high-order restart
   suffices in principle. The physical carrier and restart adapters still
   have to be supplied; this lane does not claim an A04 theorem.

## Compiler attempts

The first direct check exposed `Unknown constant ...D01.initialClassR`
(the class is opened from A02), missing ENNReal scope, and dependent
positivity proofs outside the scope of conjunction witnesses. Fixed by
explicit existential proof binders, preserving positive nonempty intervals.
Nested continuous-linear-map norms needed local `SeminormedAddCommGroup`
instances, as in the vendor. One diagnostic was
`failed to synthesize ... SeminormedAddGroup C(T, X →L[ℝ] X →L[ℝ] Y)`.
Local proof instances use `let` to avoid the letI linter. No linter is disabled,
no heartbeat override is used, and final direct module checking is silent.
