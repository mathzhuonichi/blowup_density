# Lane 313: construction attempts and residual

## Route and scope

Read `LEAD_AMENDMENTS.md`, `EXISTENCE_ROUTE.md`, the ground rules/U9 in
`T11_SPLIT.md`, the first 40 lines of `logs/LESSONS.md`, and the concrete
`LocalExistenceProbe.lean` contracts. Inspected the T10 canonical carrier,
`FourierCalculus.lean` decay results, T12 `SpectralGap.lean` reweighting,
`PeriodicHeatMultiplier.lean`, and the endpoint-safe Duhamel/Picard library.
No subagents, existing-module edits, new project axioms, global heartbeat
changes, or whole-space representatives are used. All instances have names.

1. **Carrier:** conjugate reflection is an intersection of closed equalizers of
   coefficient evaluation maps. The real submodule is therefore complete.
2. **Heat:** lift the existing even multiplier to CLMs. Prove scalar strong
   continuity via a continuous `tsum` of squared coefficient differences,
   dominated by `4*‖A(k)‖²`; use the uniform contraction for joint continuity.
3. **Kernel:** bound `sqrt(1+1/(νt))` by
   `1+(sqrt ν)⁻¹*t^(-1/2)` for `t>0`. The power is interval-integrable.
   Positive-endpoint measurability and the null endpoint suffice for the exact
   kernel. Integration gives `T+2*(sqrt ν)⁻¹*sqrt T`.
4. **Convolution:** all summands are absolutely summable by weight removal
   bounded by one, square-summability, and the bijection `l ↦ k-l`.
   T12 diagonal reweighting alone does not supply a norm estimate for the
   convolution at the output H² weight. T10 rapid decay concerns smooth
   representatives, and cannot be imposed on arbitrary complete-carrier inputs.
   The missing weighted Young/product estimate is isolated below.
5. **Forced iteration:** add a continuous forced linear path to the existing
   zero-datum Picard map. Reuse the endpoint-safe Duhamel estimates, prove ball
   invariance with the actual linear bound, and apply Banach on the complete
   closed ball. Prove the genuine force integral continuous using a continuous
   extension of the force from `[0,T]`. Recover both Bochner integrability
   clauses, initial value, uniqueness on the ball, and restriction.
6. **Quantitative time:** `torusKernelTime` controls the exact kernel mass;
   `torusPicardThreshold` supplies the invariant and contractive ball. The
   forced coefficient result depends on `‖A‖+B`, where B is the force supremum
   on `[0,1]`. It does not discharge the H¹/order-wise-L¹ target.

## Exact residual named input

```lean
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```

U9c is the named discharge unit. This is bounded real bilinearity with fixed
coefficients, not `Nonempty (TorusTwoSpaceContract ν)` restated. Every other
contract field is proved. The amended `PeriodicQuantitativeLocalInput'` is
also defined because it is the required eventual target; it is not used as
an assumption in the contract or forced-solver chain. Its H¹ lifespan
consequence is conditional, as in lane 311.

Absolute convergence, exact vanishing of the symbol on arbitrary constant
modes, and the nonzero physical forced witness are unconditional. The solver
probe with constant datum `e₁` and constant force `e₁` is conditional on an exact
contract. These checks do not pretend to discharge the universally quantified
convolution input or prove that input's existence by finite-mode testing.

## Actual errors encountered and resolved

The analytic residual above is an unproved estimate, not a remaining compiler
error. No error message is invented for it. Representative actual diagnostics:

```text
error: object file '.../NSFormalization/Section3/T11/LocalExistenceProbe.olean'
of module NSFormalization.Section3.T11.LocalExistenceProbe does not exist
```

Built the dependency through `verification/`, then checked the new source.

```text
error: Application type mismatch: The argument
  PiLp.continuous_apply ↑↑i
has type
  ∀ (β : ?m.73 → Type ?u.40) [inst : (i : ?m.73) → TopologicalSpace (β i)] ...
but is expected to have type
  Continuous[...] ...
```

Supply the exponent and family explicitly: `PiLp.continuous_apply 2
(fun _ : Fin 3 ↦ PeriodicScalarData) i`.

```text
⊢ L t + -C.analytic.duhamelIntegral (IccExtend hT ⇑f) ↑t =
    L t - C.analytic.duhamelIntegral (IccExtend hT ⇑f) ↑t
```

Normalize using `sub_eq_add_neg`.

```text
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
```

This occurred while matching the heat CLM estimate to the old multiplier
estimate through unrestricted `simpa`. Replaced it by a targeted `change`,
`rw [one_mul]`, and `exact`. No heartbeat increase was needed anywhere.

```text
error: Type mismatch
  torusHeat_zero 3 (LT.lt.le hν) A
has type
  torusHeat 3 ⋯ ⋯ A = A
but is expected to have type
  ↑((↑((torusHeatCLM ⋯ 0) A)).ofLp i✝) x✝ = ...
```

`ext A` recursed all the way to coefficients. Use `ContinuousLinearMap.ext`
explicitly, then apply the existing vector equality.

```text
error: Type mismatch
  lt_min zero_lt_one (sq_pos_of_pos (div_pos hη hη))
...
but is expected to have type
  0 < min 1 (η / (1 + 2 * (√ν)⁻¹)) ^ 2
```

Parenthesize the squared second argument of `min`; the intended formula is
`min 1 ((η / (1 + 2 * (Real.sqrt ν)⁻¹)) ^ 2)`.

```text
error: Unknown option `pp.width`
error: ❌️ Docstring on `#guard_msgs` does not match generated message:
```

Use `#guard_msgs (whitespace := lax)` to check the exact three-axiom list
independently of pretty-print line wrapping.

The zero-data probe initially failed to elaborate the tuple before simplifying
`‖0‖+0`; simplifying its hypotheses first fixes it. The nonzero single-mode and
nonzero-force probes did not require any weakened premise.
