# T11 periodic local theory — blind draft A comparison

## 1. Paper clause to Lean field

| Paper clause | Draft A declaration / field | Section 4 shape mirrored | Fidelity note |
|---|---|---|---|
| One common local interval for every Sobolev order (`02-preliminaries.tex:116-120`; `appendix-a-local-theory.tex:62-76`) | `PeriodicLocalTheoryAPI.horizon`, `.solution`, `.regularity`; `PeriodicLocalRegularity.sobolev_smooth` | `A01.local_theory_v2`: `LocalTheoryAPI.horizon`, `.solution`, `.regularity`; `ManuscriptLocalRegularity.sobolev_smooth` | The same real `horizon ν a f` occurs in the solution and in the `∀m` regularity record. The interval-local path is expressed by `IsPeriodicSobolevPathOn`, an interval restriction of T10's global `IsPeriodicSobolevPath`. |
| Projected forced equation (`02-preliminaries.tex:80-83`; `appendix-a-local-theory.tex:76-77`) | `PeriodicLocalRegularity.projected` | `A01.regularity_partial.projected`; `A01.local_theory_v2` regularity `.projected` | Uses the literal physical expression `(f-div(u⊗u))-∇p`; no unspecified Leray operator is introduced. |
| Periodic pressure solves the Poisson equation and has zero mean (`02-preliminaries.tex:84-88`) | `PeriodicLocalRegularity.pressure_poisson`, `.periodic_and_pressure_gauge` | `A01.local_theory_v2`: `.pressure_recovery` + `.pressure_potential`; `A02.uniqueness.pressure_gauge` | On the torus the paper itself gives the Poisson equation and `∫p=0`, so Draft A uses those instead of the whole-space radial potential. |
| Velocity and pressure are periodic (`02-preliminaries.tex:28`) | `PeriodicLocalRegularity.periodic_and_pressure_gauge` | No whole-space counterpart | Deliberately repeated from `ClassicalSolutionT` so the complete manuscript regularity package is readable at the API boundary. |
| Local existence for `∀ν>0, ∀a∈X_T, ∀f∈F_T` (`02-preliminaries.tex:9-10,105-110`) | `PeriodicLocalTheoryAPI.solution` | `A01.local_theory_v2.solution` | Quantifier order is viscosity, datum, force, each followed immediately by its hypothesis. |
| Equal data give equal velocities on the common interval (`appendix-a-local-theory.tex:117-124`) | `PeriodicLocalTheoryAPI.velocity_unique` | `A02.uniqueness.velocity_unique` | Exact equality on `Ico 0 (min T₁ T₂)`. |
| Pressure is determined by the torus prescription (`02-preliminaries.tex:28,84-88,105-110`) | `PeriodicLocalTheoryAPI.pressure_unique` | `A02.uniqueness.pressure_gauge` | Stronger conclusion is appropriate on the torus: two already normalized pressures are exactly equal, not merely gauge-equivalent. |
| Local solutions patch to the unique maximal smooth solution (`02-preliminaries.tex:32-34,105-110`; `appendix-a-local-theory.tex:124-125`) | `PeriodicMaximalSolution`; `PeriodicLocalTheoryAPI.maximal_solution`, `.maximal_unique`, `.horizon_le_maximal` | `A02.maximal_partial`: `horizon_le_lifespan`, `patch`; `A02.maximal_partial_v2`: `exists_maximal`, `maximal_unique` | One pair of fields serves every real preterminal interval. The endpoint remains `maximalLifespanT : ℝ≥0∞`; it is not coerced into a fake real horizon. |
| `H¹` local bounds give a common restart duration (`appendix-a-local-theory.tex:147-152`) | `PeriodicContinuationAPI.restart` | `A04.continuation_v2.restart` | Draft A keeps the manuscript's `H¹` datum ball. Section 4 V2 was narrowed to fixed-force `H⁷` for implementation reasons. Both fix the original force before `∃δ` and retain uniformity in restart time. |
| Finite squared `H²` integral bounds all higher orders (`appendix-a-local-theory.tex:129-147`) | `PeriodicContinuationAPI.higherOrderBound` | `A04.continuation_v2.higherOrderBound` | Bounds the physical T10 `periodicSobolevENorm m` uniformly on `[0,S)`. |
| Bounded restart data extend through `S` (`appendix-a-local-theory.tex:147-154`) | `PeriodicContinuationAPI.restartBeyond` | `A04.continuation_v2.restartBeyond` | Returns an actual solution on `S+δ` and agreement, rather than only an inequality for the lifespan. |
| `∫₀^S ‖u(t)‖²_{H²(T³)}dt<∞` and `S<∞` imply extension (`02-preliminaries.tex:105-114`; `appendix-a-local-theory.tex:127-156`) | `squaredHTwoIntegralT`; `PeriodicContinuationAPI.extendsBeyond` | `A04.continuation_v2.extendsBeyond` | `S : ℝ` is automatically finite. The premise is `squaredHTwoIntegralT S u ≠ ⊤`; the conclusion is a `ClassicalSolutionT` on some `T>S` agreeing on all of `[0,S)`. |
| Local finiteness rules out finite maximal lifespan (same lines, packaged maximally) | `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite` | `A04.continuation_v2.lifespanInfiniteOfLocallyFinite` | A direct maximal-lifespan consequence of the displayed criterion; no extra analytic premise is introduced. |
| Mean formula and `m'=mean(f)` (`appendix-a-local-theory.tex:89-100,154`) | `solutionMeanT`, `prescribedMeanT`; `PeriodicMeanReductionAPI.mean_formula`, `.mean_derivative` | No Section 4 counterpart | The mean is the normalized Haar mean from T10 and is not assumed zero. |
| Galilean transform solves the mean-free equation (`appendix-a-local-theory.tex:95-106`) | `galileanShiftT`, `galileanVelocityT`, `galileanForceT`, `galileanPressureT`; `PeriodicMeanReductionAPI.transformed_solution` | No Section 4 counterpart | Uses exactly `m(t)=meanT(u(t,·))`, `X(t)=∫₀ᵗm`, `v=u(t,x+X)-m`, and `h=f(t,x+X)-m'`. |
| Transformed velocity and force are mean zero (`appendix-a-local-theory.tex:97-103`) | `PeriodicMeanReductionAPI.transformed_velocity_mean_zero`, `.transformed_force_mean_zero` | No Section 4 counterpart | Both conclusions are literal `IsMeanZeroT` Haar-integral equations. |
| Spatial translations preserve every Sobolev norm (`appendix-a-local-theory.tex:103`) | `PeriodicMeanReductionAPI.translation_preserves_sobolev` | No Section 4 counterpart | Stated directly for T10's extended norm at every real order. |
| Viscosity-one reduction and its inverse (`appendix-a-local-theory.tex:79-87`) | `viscosityRescaledInitialT`, `viscosityRescaledVelocityT`, `viscosityRescaledPressureT`, `viscosityRescaledForceT`, inverse field definitions; `PeriodicViscosityRescalingAPI.to_unit_viscosity`, `.from_unit_viscosity` | No registered A01/A02/A04 field; Section 4's local theory silently handles general `ν` | The rescaled horizon is `νT`; undoing a unit-viscosity horizon `T` gives `T/ν`. |

## 2. Representation choices

### Maximality

`PeriodicMaximalSolution` stores common physical velocity and pressure fields and requires `SolvesBelowT` at every positive real `S` with `ENNReal.ofReal S ≤ maximalLifespanT ν a f`. This is the torus analogue of A02's `IsMaximalSolution`, adjusted so a finite endpoint can be discussed without claiming a `ClassicalSolutionT` *at* the maximal horizon. `ClassicalSolutionT` accepts `T : ℝ`, while `maximalLifespanT` correctly lives in `ℝ≥0∞` and may be `⊤`.

### “Extends beyond”

The primary continuation conclusion is not merely
`ENNReal.ofReal S < maximalLifespanT ν a f`. It produces `T>S`, a
`ClassicalSolutionT ν a f T`, and pointwise agreement of velocity and normalized
pressure on `Ico 0 S`. This is the concrete content requested by
`02-preliminaries.tex:110-114` and by the lane brief. The lifespan inequality is
then an order-theoretic consequence.

### Continuation integral

Draft A uses

```lean
∫⁻ t in Ioo (0 : ℝ) S, periodicSobolevENorm 2 (fun x ↦ u (t,x)) ^ (2 : ℝ)
```

in `ℝ≥0∞`. This matches the existing T10 norm's codomain, represents the
nonnegative scalar integral directly, and lets finiteness be `≠ ⊤` without
`ENNReal.toReal` turning an infinite quantity into zero. A real Bochner integral
would first require a separately registered real-valued norm and an explicit
integrability hypothesis. Endpoints are null, so `Ioo`, `Ioc`, and the paper's
`0`-to-`S` notation agree once measurability is established.

### Mean reduction

The reduction is a separate `PeriodicMeanReductionAPI`, with named formula
definitions rather than a monolithic proposition. T20 can consume the mean ODE,
the transformed solution, mean-zero conclusions, and translation isometry
independently. The structure quantifies over an existing `ClassicalSolutionT`;
it does not assume a zero-mean datum and does not build local existence again.

### Pressure

The torus pressure is represented by the exact Poisson equation from
`02-preliminaries.tex:84-88`, spatial periodicity, and `PressureGaugeT`. The
coefficient-side `periodicLeray` is therefore not copied into this draft: its
physical pressure content is precisely the Poisson-plus-zero-mode prescription.
This also avoids inventing a coefficient datum for the nonlinear residual before
T10's reweighting and product lemmas are registered.

### Restart force class

`PeriodicContinuationAPI.restart` returns a shifted-force solution directly.
For `t₀>0`, `timeShiftT t₀ f` can be nonzero at its new time zero and hence does
not generally satisfy T10's `MemForceT`, whose support lies strictly inside
`(0,∞)`. Thus it would be ill-typed mathematically—not just inconvenient—to
route the restart through `PeriodicLocalTheoryAPI.solution`, which is deliberately
quantified only over `forceClassT`. Appendix A uses the larger classical local
theory class of forces smooth on compact nonnegative time intervals at this step.

## 3. Ambiguities and deliberate readings

1. **Pressure equation at `t=0`.** Draft A states `pressure_poisson` on `Ico 0 T`. The paper says pressure “is recovered from” the displayed equation and Appendix A restores the gradient part after solving the projected equation. If only the interior PDE is desired, this can be narrowed to `Ioo 0 T`; smooth one-sided data support the current endpoint reading.
2. **Restart-time range.** Appendix A literally discusses `t₀ ↑ S`; Draft A uses all `t₀∈[0,S]`, matching A04 V2. This follows from the same compact-window `H¹` bounds and is the useful uniform statement, but a reconciliation may choose an eventual-neighborhood formulation instead.
3. **Force-uniformity.** The manuscript fixes the original `f` and uses its bound on `[0,S+1]`. Draft A fixes `f` before `∃δ`; it does not claim one duration uniformly over all forces with a common norm bound.
4. **`H¹` versus `H⁷`.** Draft A records the manuscript's `H¹` restart claim. A04 V2's `H⁷` field is an implementation narrowing and must not silently replace the torus paper statement.
5. **Maximal fields outside the lifespan.** `SpaceTimeField` is total, so the stored fields have arbitrary values after a finite lifespan. Every equality and solution condition is restricted to a physical preterminal interval; no assertion depends on the arbitrary tail.
6. **Mean derivative at zero.** `mean_derivative` is on `Ioo 0 T`, where ordinary `HasDerivAt` is two-sided. The mean formula includes `t=0`; a one-sided derivative statement at zero would require `HasDerivWithinAt` and is not needed for T20.
7. **General local-theory force class.** Proposition `prop:local` is stated for forces smooth into every `H^m` on compact intervals, while the Section 3 consumers use `F_T`. The requested API is narrowed to `F_T`; restart explicitly exposes the only place where the larger class is essential.
8. **T10 path locality.** T10's `IsPeriodicSobolevPath` quantifies at every nonnegative time. `IsPeriodicSobolevPathOn` uses a global auxiliary extension agreeing on the solution interval, so local regularity does not constrain arbitrary values of a total velocity field after its lifespan.

## 4. Needs a lemma / implementation debt

- Register the T10 vocabulary, then delete all verbatim copies in `DraftA.lean`.
- Show interval-local physical Sobolev paths admit the auxiliary global extension used by `IsPeriodicSobolevPathOn`, and prove uniqueness of their T10 data.
- Prove `convectionDivergenceT = (u·∇)u` under solenoidality, the periodic analogue of Section 4 A01's `ConvectionDivergence.lean`.
- Recover the periodic pressure: Poisson solvability at every time, periodicity, zero mean, smoothness, and uniqueness; connect this to the coefficient-side periodic Leray projector.
- Construct a common local interval in the Fourier Sobolev carrier for all integer orders, including force smoothness at the initial endpoint and pressure recovery.
- Prove classical velocity uniqueness on a common interval and exact pressure equality after zero-mean normalization.
- Implement restriction, patching, the order theory of `maximalLifespanT`, maximal gluing, and uniqueness of the glued fields.
- Prove strong measurability of `t ↦ periodicSobolevENorm 2 (u(t))`, identify the `lintegral` with the manuscript's usual integral, and exclude `⊤` on compact subintervals.
- Establish the periodic high-order energy inequality, its regularized norm inequality, Grönwall bounds in every `H^m`, and the manuscript-strength `H¹` quantitative local existence duration.
- Extend the local solver to shifted forces smooth at time zero; T10's test-force class alone is not closed under positive time shifts.
- Patch shifted solutions with `SolvesBelowT`, including exact normalized pressure agreement, to prove `restartBeyond` and `extendsBeyond`.
- Derive the maximal-lifespan `= ⊤` packaging from the concrete extension theorem, including the `ENNReal.toReal` endpoint bookkeeping.
- Prove the mean identity by integrating the equation over the torus, including vanishing means of the Laplacian, pressure gradient, and nonlinear divergence.
- Prove the Bochner fundamental theorem for `prescribedMeanT`, yielding `m'=meanT(f)` on interior times and the bounded-mean consequence used in restart.
- Prove time-dependent periodic translation preserves smoothness, divergence, pressure gauge, and every T10 Sobolev norm; verify the cancellation between `X'=m` and the subtracted advecting velocity.
- Prove the transformed force and velocity have zero mean and that `galileanVelocityT`/`galileanPressureT` satisfy every `ClassicalSolutionT` field.
- Prove the viscosity time-chain rules, horizon scaling, class preservation, pressure gauge preservation, and the two rescaling directions.

## 5. Existing implementation candidates (not imported)

- `Paper1/PeriodicInitialData.lean`: `IsAdmissibleInitialData` and the extraction lemmas `Flow.initial_smooth`, `.initial_periodic`, `.initial_divergence_free`, `.initial_admissible` match `initialClassT` closely.
- `Paper1/PeriodicLifespan.lean`: `Flow`, `lifespan`, `horizon_le_lifespan`, `lifespan_le_iff`, and `lifespan_le_iff_no_extension` are direct candidates for the `ClassicalSolutionT`/`maximalLifespanT` order layer. Its `Flow` lacks T10's Sobolev path, pressure-gradient, and zero-mean-gauge fields, so it needs a fieldwise adapter rather than an `rfl` identification.
- `Paper1/PeriodicFlowRestriction.lean`: `Flow.restrict` and `Flow.nonempty_restrict` are the natural restriction implementation.
- `Paper1/PeriodicUniqueness.lean`: `classical_uniqueness_on_Icc` is the velocity-uniqueness core; `normalized_residual` and the normalization helpers support shifted/scaled intervals.
- `Paper1/PeriodicPressureNormalization.lean`: `pressureMean`, `normalizedPressure`, `normalizedPressure_gradient_eq`, `normalizedPressure_periodic`, `normalizedPressure_residual_eq`, `normalizedFlow`, and `normalizedFlow_mean_zero` are pressure-gauge candidates.
- `Paper1/PeriodicLocalLifespan.lean`: `IsSmoothPeriodicForce` is the larger force class needed for restarts; `h2SquaredProfile`/`FiniteH2Energy` are an existing real-valued criterion spelling; `ClassicalPeriodicLocalTheory` is an honest conditional two-field interface for local flow plus finite-`H²` extension; `MaximalSolution`, `exists_maximal_periodic_solution`, `maximal_solutions_agree`, `exists_periodic_extension_of_finite_h2`, and `maximal_endpoint_gt_of_finite_h2` implement much of the packaging once its analytic premise is discharged.
- `Paper1/PeriodicOrdinaryLocal.lean`: `exists_finiteOrder_local_of_representative` is only an interface conditional on an ordinary `L²(R³)` representative. Its own header correctly notes that a nonzero periodic field has no such representative, so it is not the periodic local-existence proof.
- No `PeriodicMeanReduction*` or `Galilean*` module is present. The entire mean/Galilean package is new implementation debt.
