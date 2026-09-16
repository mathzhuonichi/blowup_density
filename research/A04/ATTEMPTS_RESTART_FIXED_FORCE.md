# Lane 215 — fixed-force windows and the exact higher-order bound

## Results and quantifiers

`RestartFixedForce ν f S` chooses δ after ν, f, S and a finite H⁷ bound K,
but before **both** `t₀ ∈ Icc 0 S` and the admissible restart datum. The theorem
`restartFixedForce_of_memForceR` proves precisely this statement against lane
211's selected `localHorizon'`, not just existence at an unrelated horizon.

Set `F := sobolevPath (C01.forcePath hf) … 6` on `[0,S+1]` and `B := ‖F‖`.
The shifted path at `r ∈ [0,1]` equals the original path at `r+t₀`: the
`SmoothL2Field` fields are definitionally equal and field extensionality makes
their Sobolev lifts equal. `ContinuousMap.norm_le` then bounds every shifted
reference-path norm by B. Choose

```
δ = A01.uniformHorizon ν (A01.datumRadiusConstant * K.toReal) B.
```

Its positivity and antitonicity, together with the physical H⁷-to-cylinder
radius bound, give the desired horizon lower bound. Negative S is vacuous;
the exported theorem retains the requested `0 ≤ S` assumption.

The vendor route was inspected: `Euler/UniformHeatLocal.lean` contains
`exists_uniform_restart_time`; `forced_uniform_restart_time` is its local
specialization in `Section4/A01/Continuation.lean`, not a vendor declaration
of that exact name. It produces a mild solution on a uniform window, but does
not compare its chosen δ with `localHorizon'`. The antitone route does.

## Removing the smooth-path obstacle, without endpoint assumptions

1. `shiftedSolution` translates an actual classical solution at an interior
   nonnegative time, including the momentum equation (vector-valued chain
   rule `HasDerivAt.scomp`) and continuous Sobolev datum paths.
2. `compact_hSeven_bound` bounds a classical solution on `[0,t]`, with t
   strictly before its horizon. This uses only its existing continuous datum.
3. `exists_carrier_window` applies fixed-force uniformity to that compact
   bound and chooses `b = max 0 (t - δ/2)`. The selected carrier starting at b
   reaches strictly past t. At t=0 it starts at zero.
4. `classical_hasSmoothSobolevPath` compares the translated classical solution
   to this carrier by `velocity_unique_core`. Uniqueness of Sobolev data
   identifies the original continuous datum with the translated smooth one
   on an actual neighborhood within `[0,T)`. Locality of `ContDiffWithinAt`
   proves the full smooth-path property for **every** classical solution.

This argument is not circular: it uses compact continuity strictly inside
an already existing solution, and no integral-continuation or gluing result.
It does not assume a closed carrier at a possibly singular terminal time.

`localCarrier_gronwall_bound` also supplies the literal lane-179 bridge:
`LocalCarrier.hpairs 6` gives the continuous cylinder path v, the same c.U,
angle invariance and lift equality. `c.velocity_eq` transfers `c.hslice` to
c.w. Taking R=‖v‖ and `c.regularity.sobolev_smooth` gives exactly
`highOrder_bddAbove_of_kbnd_Ico_full`, with exponent
`Cgron m ν * (256 * R^2 * S)`. This bridge applies at the carrier's own
horizon, not at an arbitrary terminal S of a `SolvesBelow` family.

## Exact HigherOrderBound, now unconditional

`higherOrderBound_of_gronwall : HigherOrderBound` proves the **unchanged**
A04 definition. The audit includes a definitional-equality check spelling out
all its quantifiers, including `MemL1Hm`, every natural order, and `Ico 0 S`.

For the integral criterion use lane 179's underlying engine
`A01.highOrder_bddAbove_of_kbnd`, rather than first constructing a cylinder
sup bound. `running_hTwo_integral_le` converts the real running integral into
an ENNReal integral on `(0,t)` and bounds it by `squaredHTwoIntegral S u`.
The explicit finiteness hypothesis justifies the final `.toReal` comparison.
Endpoint singletons are removed by `integral_Ioc_eq_integral_Ioo`.

At each t<S, take the shorter classical solution with horizon `(t+S)/2`.
All use the same cap `(squaredHTwoIntegral S u).toReal` and the same initial
and forcing norms, so the resulting bound is independent of the shorter
horizon. For n=max(m,3), let

```
B = (sobolevNormAt n u 0 + (forceSobolevENormL1 n f).toReal)
      * exp (Cgron n ν * (squaredHTwoIntegral S u).toReal).
M = ENNReal.ofReal (‖D01.lowerVectorL n m …‖ * B).
```

Datum lowering supplies every order, including 0, 1 and 2. No endpoint value
of u at S, no H⁷ bound derived before existence, and no `⊤.toReal` collapse
enters the argument.

## One remaining named fact: shifted classical gluing

The consumers `restartBeyond_fixed`, `extendsBeyond_fixed`, and
`lifespanInfiniteOfLocallyFinite_fixed` typecheck. Instantiating the proved
restart and higher-order inputs gives `extendsBeyond_of_memForceR` and
`lifespanInfiniteOfLocallyFinite_of_memForceR`. These **still require exactly
one named input**, `extension : ShiftedLocalExtension`, whose full statement is:

```lean
∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
  (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
  ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
    ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f
```

This is a concrete existence/patching fact, with two actual classical
solutions as inputs and no uniformity assumption. It is not proved in this
lane. The existing A02 `patch` only chooses the longer of two solutions with
the **same zero-time initial datum and force**. Applying it to `w` and the
shifted carrier fails on both indices. `shiftedSolution` now makes the
overlap comparison available, but a solution on the union, with compatible
pressure gauge, still needs construction. The only use of this hypothesis
is the last line of `restartBeyond_fixed`, after local existence, data
qualification, shifted-force membership and the horizon bound are discharged.

Whole-source searches covered A02, A01, D01, A03, A04, C01, Source lifespan
modules, and vendor continuation modules. The vendor mild continuation
result constructs cylinder mild paths; it is not the physical classical
union theorem with this conclusion. We do not package regularity, integral
bounds and gluing into a conjunction to pretend there is only one gap.

Satisfiability: the gluing statement requires only an interior restart
`b<T`, not regularity at an unattained terminal time. It is the standard
nonzero-solution overlap construction, with pressure normalization allowed
by A02. The audit supplies an actual zero-solution extension and uses
`zeroSol` both in the uniform-window and exact higher-order examples.

## Consumer fidelity and the V2 question

No consumer needs cross-force uniformity. R1 fixes f and S before δ, uses
only times in `[0,S) ⊆ [0,S]`, and consumes H⁷-bounded data. C1 asks the exact
higher-order theorem for order 7, then applies R1. The final finite-supremum
contradiction is unchanged. The old `restartBeyond` statement is **not** a
literal rename: its δ precedes all f and S, and it only assumes an H¹ bound.
Those quantifiers cannot be kept when substituting `RestartFixedForce`.
The new declarations expose the necessary fixed-force/H⁷ change explicitly.
No original Lean module, contract, `Restart`, or `HigherOrderBound` was edited.
Owner approval for V2 wording remains a separate matter.

## Proof attempts and checks

Useful elaboration fixes: `ContinuousMap.norm_le` takes the map before its
nonnegativity proof; `field_ext` is in `EulerOrdinarySobolev`; integer-order
casts sometimes need an explicitly typed datum equality; vector-valued
composition is `.scomp`, not scalar `.comp`; unfold `sobolevNormAt` before
rewriting `ENNReal.ofReal_pow`; specify `(S := S)` before proving the shorter
horizon inequality so the metavariable is not handed to `linarith`.

All production declarations are audited; no global or local heartbeat
increase is used. Gate results and the exact delivery limitation are in
`REPORT_215.md`. Logs are kept under worktree-local `tmp/`, not in the report.
