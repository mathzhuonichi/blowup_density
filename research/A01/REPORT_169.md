# Lane 169-A01-b1-ladder-r2 report

## 1. Theorems proved

### Flagship R2 theorem

`NSFormalization.Section4.A01.exists_differentiable_datumPath` proves R2 for every
`q m : ℕ` with `6 ≤ q` and `m ≤ q - 1`.  Under `0 < ν`, `0 < S`, the Horizon force
regularity, angle invariance, ordinary descent, and the exact Horizon Duhamel identity,
its conclusion is exactly

```lean
∃ A R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)),
  (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧
  (∀ t, IsSobolevDatum (m : ℝ)
    (⇑(projectedResidualOrdinaryPath hq hm ν F hF u t)) (R t)) ∧
  ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
    HasDerivAt (extendPath S hS.le A)
      (R ⟨t, ht.1.le, ht.2.le⟩) t
```

Thus both `A` and its derivative path `R` are continuous on the closed interval, and
the clamped real extension of `A` is differentiable at every interior time.  No endpoint
derivative is asserted.

`NSFormalization.Section4.A01.projectedResidualPath_eq` states the residual exactly:

```lean
projectedResidualPath hq hm ν F hF u t =
  ν • laplacianOperator 1 m (restrictOperator 1 (by omega) (u t)) +
    restrictOperator 1 (by omega : m ≤ q)
      (leray 1 q (sobolevPath F hF q t - advection 1 hq (u t) (u t)))
```

In PDE notation this is `νΔu + P(F-(u·∇)u)`.  The spatial range is `m ≤ q-1`,
reflecting the two derivatives used by `Δu` from the order-`q+1` velocity path.

### Reusable derivative and identification theorems

`datumPath_hasDerivAt` is the selection-independent form.  For `m+2 ≤ q+1`, any
continuous datum maps `A,R` satisfying

```lean
∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)
∀ t, IsSobolevDatum (m : ℝ)
  (⇑(ordinaryResidualPath hq hm ν f u t)) (R t)
```

obey

```lean
∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
  HasDerivAt (extendPath S hS.le A)
    (R ⟨t, ht.1.le, ht.2.le⟩) t.
```

`ordinaryLift_projectedResidualOrdinaryPath` proves, for every time including the
endpoints,

```lean
ordinaryLift (projectedResidualOrdinaryPath hq hm ν F hF u t) =
  value 1 (projectedResidualPath hq hm ν F hF u t).
```

`residualDatum_is_timeDerivative` is the conditional R3 handoff.  Given a representative
`v` satisfying pointwise

```lean
∀ x, HasDerivAt (fun r => v (r, x))
  ((ordinaryResidualPath hq hm ν f u ⟨t, ht⟩) x) t,
```

it concludes exactly

```lean
IsSobolevDatum (m : ℝ)
  (fun x => deriv (fun r => v (r, x)) t) (R ⟨t, ht⟩).
```

Supporting results establish injectivity of datum order lowering, the continuous
cylinder residual, its angle invariance and ordinary descent, and a generalized R1
continuous-datum constructor at every available finite order.

## 2. What is in Lean now

The new module
`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean` contains the complete
vendor-Duhamel proof.  It differentiates the exact mild equation in ordinary L² via
`Source.OrdinaryForcedTime.realization_hasDerivAt`, maps the equation to the canonical
order-zero datum, then lifts the derivative through the injective continuous map
`lowerVectorL m 0` using `EulerInjectivePathDerivative.hasDerivAt_of_injective_map`.

The residual construction is not merely nominal: the module proves its displayed
Leray formula, angle invariance, existence of its ordinary L² descent, and exact
recovery after applying `ordinaryLift`.

`research/A01/axioms_b1_r2.lean` audits all 23 declarations in the module.  Every one
prints exactly `[propext, Classical.choice, Quot.sound]`.  The same file contains a
non-vacuity example with `q=6`, `m=0`, `S=1`, `ν=1`, zero initial datum, zero force,
`u := 0`, and `U := 0`.

`research/A01/B1_LADDER.md` marks R2 DONE at all `m ≤ q-1`, and
`research/A01/ATTEMPTS_B1_R2.md` records the successful route and alternatives.

## 3. Gaps

R2 itself has no residual Lean gap in the stated range.  The proved derivative is the
projected residual `νΔu + P(F-(u·∇)u)`, not yet the pointwise physical expression
`F-(u·∇)u+νΔu-∇p`.

The remaining R3 bridge is to construct a sufficiently smooth representative `v`,
recover pressure, and prove that the representative's pointwise time derivative equals
the descended projected residual.  `residualDatum_is_timeDerivative` will identify the
R2 derivative datum once that equality is available.

The physical-side A04/C01 route was not used because its relevant theorems assume an
already constructed `ClassicalSolutionR`; using them to establish B1's first time
derivative would be circular.  A direct word-path derivative route was also unnecessary:
ordinary L² differentiation plus injective order lowering yields the full order-`m`
datum result at once.

There is no theorem error left.  During the non-vacuity audit, a fully expanded result
type initially produced an application type mismatch because two proofs of force
jet-continuity occurred as non-definitionally-equal dependent arguments to
`projectedResidualOrdinaryPath`.  The final example consumes the flagship theorem and
projects out the non-vacuity consequence, leaving those proof arguments out of its
result type.

## 4. Commands and results

All Lean commands were run from `verification/` after sourcing `scripts/lean-env.sh`.

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathDeriv` — exit 0.
  Lake replayed pre-existing linter warnings from dependencies; the new module emitted
  no warning or error.
- `lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean` —
  exit 0, zero output.
- `lake env lean ../research/A01/axioms_b1_r2.lean` — exit 0; all 23 printed axiom sets
  were exactly `[propext, Classical.choice, Quot.sound]`, and the zero-path example
  elaborated.
- `make check` from the worktree root — exit 0.  Its architecture report retained the
  pre-existing copied-source admission/hash notices (`BoundaryCorollary.lean` and
  `source_hashes_match: false`); all invoked checks completed successfully.
- A forbidden-token scan of the new Lean module and conformance file found no `sorry`,
  `admit`, `axiom`, or `native_decide`.  The only module heartbeat override is the
  documented per-declaration value `400000` on `cylinderResidual_invariant`.
