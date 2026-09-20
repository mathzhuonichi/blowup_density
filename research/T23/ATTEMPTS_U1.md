# T23 U1 attempts

## A1 — unnecessary distance symmetry in the interior-margin proof

The first proof of `domainPlacementMargin_pos` rewrote `dist_comm` after
unfolding ball membership.  This reversed the already-correct orientation of
`Metric.mem_ball`.

Command:

```text
cd verification && lake env lean ../formalization/NSFormalization/Section3/T23/Placement.lean
```

Exact error:

```text
../formalization/NSFormalization/Section3/T23/Placement.lean:114:27: error: Application type mismatch: The argument
  hx₀
has type
  x₀ ∈ Metric.ball chartCenter chartRadius
but is expected to have type
  chartCenter ∈ Metric.ball x₀ chartRadius
in the application
  Metric.mem_ball.mp hx₀
```

Resolution: retain the `dist x₀ chartCenter` orientation produced directly by
`Metric.mem_ball`; no symmetry rewrite is needed.

## A2 — asking `nlinarith` to synthesize the strict radius comparison

The first affine-containment proof gave `nlinarith` the non-strict carrier
bound and denominator bound, expecting it to infer that the positive scale
turns `R < 2(R+1)` into a strict product inequality.

Exact error:

```text
../formalization/NSFormalization/Section3/T23/Placement.lean:183:4: error: linarith failed to find a contradiction
K : Set Space
f : VelocityField
hK : IsCompact K
hf : HasCompactSupport f
T chartRadius : ℝ
chartCenter x₀ : Space
hx₀ : x₀ ∈ Metric.ball chartCenter chartRadius
ε : ℝ
hε : ε ∈ Ioc 0 (domainPlacementThreshold hK hf T chartCenter x₀ chartRadius)
y : Space
hy : y ∈ domainPlacementCarrier K f
hR : 0 < domainPlacementRadius hK hf
hden : 0 < 2 * (domainPlacementRadius hK hf + 1)
he : ε * (2 * (domainPlacementRadius hK hf + 1)) ≤ domainPlacementMargin chartCenter x₀ chartRadius
hn : ε * ‖y‖ ≤ ε * domainPlacementRadius hK hf
a✝ : domainPlacementMargin chartCenter x₀ chartRadius ≤ ε * ‖y‖
⊢ False
failed
```

Resolution: prove `R < 2(R+1)` explicitly, multiply it strictly by `ε>0`,
and compose the three inequalities with `trans_lt`/`trans_le`.

## A3 — wrong ordered-multiplication lemma for this Mathlib pin

Using `(mul_lt_mul_left hε.1).2 hfactor` selected the unbundled theorem whose
typeclass orientation does not match ordered real multiplication in this pin.

Exact error:

```text
../formalization/NSFormalization/Section3/T23/Placement.lean:187:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  MulRightStrictMono ℝ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Resolution: use the explicit ordered-ring lemma
`mul_lt_mul_of_pos_left hfactor hε.1`.

## A4 — compiling the consumer before building its new import

The first direct probe run occurred after checking `Placement.lean` with Lean,
but before Lake had produced the new module's object file.

Exact error:

```text
../research/T23/probes/placement_closes.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/476-T23-U1-domain-placement/formalization/.lake/build/lib/lean/NSFormalization/Section3/T23/Placement.olean' of module NSFormalization.Section3.T23.Placement does not exist
```

Resolution: build `NSFormalization.Section3.T23.Placement` from
`verification/` before checking importing research files.

## A5 — two probe names were not in the imported namespace

After the production module built, the first translated probe used
`Metric.isCompact_closedBall` (the theorem is unnamespaced) and used T13's
coordinate-norm helper without importing/opening its defining module.

Exact errors:

```text
../research/T23/probes/placement_closes.lean:34:8: error(lean.unknownIdentifier): Unknown identifier `Metric.isCompact_closedBall`
../research/T23/probes/placement_closes.lean:58:17: error(lean.unknownIdentifier): Unknown identifier `abs_spaceCoord_le_norm`
../research/T23/probes/placement_closes.lean:53:38: error: unsolved goals
hzero : 0 ∈ translatedDomain
hnorm : ‖translatedCenter‖ < 2
⊢ False
```

Resolution: use `isCompact_closedBall`, and import/open the safe
`Section3.T13.ConstantEndpoints` module that defines
`abs_spaceCoord_le_norm`.
