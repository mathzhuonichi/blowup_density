# REPORT 210 — uniform horizon and the H¹ obligation

## 1. What was proved

**Partial delivery; the requested `horizon_lower_bound_H7` is not proved.**
The proposed proof has an additional temporal-norm gap: the vendor Picard
ball budget uses the force's time **supremum**, whereas the requested
statement bounds its time **L¹** norm. Radius/Lipschitz monotonicity alone
cannot bridge this. This is not a counterexample to H⁷/L¹ local existence.

Proved `exists_uniform_H7_sup_force_horizon`: for `ν>0`, `S>0`, `R≥0`
and `B : ℝ`, there is one `0<δ≤S`, chosen before both the force and datum,
such that every `F : C(Icc 0 S, SobolevSpace 1 6)` with `‖F‖≤B` and
`a : SobolevSpace 1 7` with `‖a‖≤R` has a genuine quadratic mild solution
on `[0,δ]`, norm at most `R+1`, with initial value a. Its coefficient bundle
is exactly `ForcedCylinderLocal.coefficients 1 (le_refl 6) F`.

The general `exists_uniform_H7_coefficient_horizon` chooses δ from
`exists_positive_time_budget ν M L 1 S` before the coefficient bundle,
under `ballBound (R+1)≤M` and `ballLipschitz (R+1)≤L`.
The force specialization sets
`M=‖C₀.projection‖*(B+‖C₀.quadratic‖*(R+1)^2)` and
`L=C₀.ballLipschitz (R+1)`, for the zero-force bundle C₀.
`uniform_H7_zero` instantiates this result on zero datum/force, for every
positive viscosity, retaining the actual convection operator.

## 2. What is now in Lean

New production module `formalization/NSFormalization/Section4/A01/HorizonUniform.lean`
contains eight named declarations: the two existence theorems and zero
instance above; `picard_ballBound_mono`, `picard_ballLipschitz_mono`,
`picard_budget_mono`; and the unasserted obligations `HorizonLowerBoundH1`
and `HorizonLowerBoundH7L1`, parameterized by the future horizon function.
The H¹ body is copied token-for-token from Spec.lean:338–343. The conformance
file checks its definitional equality using the canonical contract types.

Exact monotonicity inputs are `pow_le_pow_left₀`, `add_le_add`, and
`mul_le_mul_of_nonneg_left`, with `parabolicConstant_nonneg` and
`Real.sqrt_nonneg` for the nonnegative mass. The vendor's time monotonicity
lemma is `EulerUniformHeatLocal.parabolic_mass_mono` (using
`Real.sqrt_le_sqrt`); the proof here uses one common interval directly.
`parabolicKernelBound_integral` identifies the mass with `kernelMass`.

Records: `ATTEMPTS_HORIZON_UNIFORM.md`, row 210 in `A3_SPLIT.md`, this report,
and `axioms_horizon_uniform.lean`. No existing Lean module or contract changed.

## 3. What remains open

There is no `LocalSolution.lean` / `localHorizon` in this checkout.
`constructor_of_base` is in lane 207's research probe, not TameAssembly's
exports. This lane does not claim a classical-constructor horizon bound,
a physical H⁷-norm comparison, or integration with lane 208.

Two independent issues prevent claiming the requested H⁷ theorem:

- The H⁷/L¹ force bound does not control the time-sup H⁶ coefficient norm.
  Smooth time-concentrating forces have fixed L¹ norm and arbitrarily large
  sup norm. Existence needs both Picard budgets, not just the contraction
  budget used by uniqueness. A separate L¹-force Duhamel estimate with an
  appropriate ball radius is needed for that route.
- A common admissible interval does not lower-bound an arbitrary existential
  witness selected by `Classical.choose`. The exported horizon must be
  selected with the uniform guarantee, or have an appropriate maximality
  property. The vendor's ε/2 choice has no such monotonicity specification.

The H¹ field remains open as well. `hb_of_base''` starts from an existing
base solution and propagates high norms on its interval; it cannot provide
an H¹-uniform interval or bound arbitrary high initial norms by an H¹ ball.
Using persistence to obtain that initial interval would be circular.
HeliCorgi's `R3QuantitativeLifespan.lean` takes `R3HsVelocity 3`: its
lifespan is in terms of **H³** data, with convection H³→H², and is unforced.
It is not an H¹ local-existence supplier.

The lead/owner has two honest options, with no re-cut decided here:

1. Implement forced quantitative H¹ local theory, its smooth persistence,
   and the uniform horizon selection. An H³ theory could instead supply
   high-order restart, but would still not prove the unchanged H¹ field.
2. Authorize a V2 field at the supported spatial order and temporal force
   norm, or additionally prove the missing L¹-force estimate. Merely replacing
   H¹ by H⁷ while retaining L¹ is insufficient for this vendor-budget proof.
   A04's recorded consumer (REVIEW.md M5) can use any fixed sufficiently
   regular order: appendix-a:146–150 bounds every H^m norm up to S, and the
   fixed smooth force is bounded on [0,S+1]. This supports the restart
   strategy, not a completed A04 adapter in this lane.

## 4. Commands and results

All Lean shells sourced `. scripts/lean-env.sh`; all Lake commands ran
from `verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A01.HorizonUniform`: exit 0;
  9933 jobs, output redirected to `tmp/build210.log`. Inherited dependency
  warnings are replayed, so the aggregate build log is not empty.
- `lake env lean ../formalization/NSFormalization/Section4/A01/HorizonUniform.lean`:
  exit 0, **zero output**, `tmp/module210.log`.
- `lake env lean ../research/A01/axioms_horizon_uniform.lean`: exit 0,
  eight reports each exactly `[propext, Classical.choice, Quot.sound]`;
  contract conformance and non-vacuity examples pass, `tmp/axioms210.log`.
- `make check`: exit 0; 30 work items consistent, `tmp/check210.log`.
- `lake test`: exit 0, `tmp/test210.log`.
- `make test-mutations`: exit 0; refactor accepted, all three invalid
  mutations rejected, `tmp/mutations210.log`.
- `git diff --check`: exit 0.

No push, merge or rebase; only this worktree changed. The partial-delivery
commit contains the module, audit, attempts, split row and report.
