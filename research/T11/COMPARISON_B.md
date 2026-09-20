# T11 draft B comparison — periodic local theory and continuation

This comparison is based only on the paper, the reconciled T10 vocabulary,
the registered Section 4 contracts, and the existing `Paper1/Periodic*`
implementation heads named in the lane brief. It does not use another T11
draft or brief.

## Paper clause → Lean field → Section 4 shape

| Paper clause | Draft B declaration/field | Section 4 counterpart | Fidelity note |
|---|---|---|---|
| `X_T=C∞_div(T³;R³)`, `F_T=C_c∞(T³×(0,∞);R³)` (`02-preliminaries.tex:7-26`) | `PeriodicLocalTheoryAPI.solution`, with `ν>0`, then `a∈initialClassT`, then `f∈forceClassT` | `A01.local_theory_v2`: `LocalTheoryAPI.solution` | The quantifier order requested by the lane is literal. No mean-zero hypothesis is added. |
| One common existence interval for every Sobolev order (`02-preliminaries.tex:116-119`; `appendix-a-local-theory.tex:65-76`) | `PeriodicLocalRegularity.sobolev_smooth`; `PeriodicLocalTheoryAPI.regularity` | `A01.local_theory_v2`: `ManuscriptLocalRegularity.sobolev_smooth`, `LocalTheoryAPI.regularity` | `∀m` occurs inside one record indexed by one real `T`; it does not select a different horizon for each `m`. |
| Smooth periodic velocity and pressure (`02-preliminaries.tex:28-36`) | `PeriodicLocalRegularity.velocity_periodic`, `pressure_periodic`; the copied `ClassicalSolutionT` carries slab smoothness | No direct torus clause; closest are `A01.local_theory_v2` regularity plus `ClassicalSolutionR` | Equality at unit shifts is stated for the actual fields on `Ico 0 T`. |
| Projected equation (`02-preliminaries.tex:75-83`; `appendix-a-local-theory.tex:76-77`) | `PeriodicLocalRegularity.projected` | `A01.regularity_partial.projected`; `A01.local_theory_v2` inherited/full `projected` | The right side is `(f-div(u⊗u))-grad p`, paired with the next Leray-complement clause. |
| Periodic Leray pressure recovery and `∫p=0` (`02-preliminaries.tex:76-88`) | `PeriodicLocalRegularity.pressure_recovery`, `pressure_gauge`, `pressure_normalized` | `A01.local_theory_v2`: `ManuscriptLocalRegularity.pressure_recovery`; whole-space `pressure_potential` has no torus analogue | `IsPeriodicLerayComplementT` uses T10 Fourier data and the actual periodic Leray graph. The gauge is a literal Haar integral. |
| Local existence (`02-preliminaries.tex:105-109`; `appendix-a-local-theory.tex:60-70`) | `PeriodicLocalTheoryAPI.horizon`, `solution`, `regularity` | `A01.local_theory_v2`: `horizon`, `solution`, `regularity` | Positivity is stored by `ClassicalSolutionT.horizon_pos`, as in A01 V2. |
| Unique velocity on the common interval (`02-preliminaries.tex:105-109`; `appendix-a-local-theory.tex:117-124`) | `PeriodicLocalTheoryAPI.velocity_unique` | `A02.uniqueness.velocity_unique` | The conclusion is pointwise equality on `Ico 0 (min T₁ T₂)`. |
| Pressure “determined as above” (`02-preliminaries.tex:84-109`) | `PeriodicLocalTheoryAPI.pressure_unique` | `A02.uniqueness.pressure_gauge` | On `R³` the contract states gauge equivalence. On `T³`, both pressures have zero mean, so Draft B states literal pointwise equality. |
| Maximal lifespan (`02-preliminaries.tex:32-34,105-109`; `appendix-a-local-theory.tex:123-125`) | copied `maximalLifespanT`; `horizon_le_lifespan`; `IsMaximalPeriodicSolution`; `exists_maximal` | `A02.maximal_partial.horizon_le_lifespan`; `A02.maximal_partial_v2.exists_maximal` | The lifespan is `ℝ≥0∞`; the maximal object is one common `(u,p)` restricted to every real horizon strictly below it. |
| Unique maximal smooth velocity (`02-preliminaries.tex:105-109`) | `PeriodicLocalTheoryAPI.maximal_unique` | `A02.maximal_partial_v2.maximal_unique` | Equality is only asserted on physical preterminal times; values of total Lean functions outside the lifespan are deliberately ignored. |
| High-order energy/Gronwall bound (`appendix-a-local-theory.tex:127-147`) | `PeriodicContinuationAPI.higherOrderBound` | `A04.continuation_v2.higherOrderBound`; analytic precursor `A04.energy_high_partial(_v2)` | A finite squared `H²` lintegral yields a finite uniform `H^m` bound for every integer `m`. |
| Common H¹ restart duration for `t₀↑S` (`appendix-a-local-theory.tex:147-152`) | `PeriodicRestartH1`; `PeriodicContinuationAPI.restart` | Closest shape: `A04.continuation_v2.restart` | Draft B states the manuscript H¹/fixed-force version. A04 V2 is the proved narrower H⁷ version. Neither statement is cross-force uniform. |
| One restart interval passes beyond `S` and uniqueness patches it (`appendix-a-local-theory.tex:149-155`) | `PeriodicContinuationAPI.restartBeyond`; concrete `ExtendsBeyondT` | `A04.continuation_v2.restartBeyond` | The torus conclusion returns an actual larger solution and overlap equality, rather than only a lifespan lower bound. |
| `∫₀^S ‖u(t)‖²_{H²(T³)}dt<∞` implies extension (`02-preliminaries.tex:110-114`; `appendix-a-local-theory.tex:127-156`) | `squaredHTwoIntegralT`; `PeriodicContinuationAPI.extendsBeyond` | `A04.continuation_v2.extendsBeyond` | `S : ℝ` makes `S<∞` automatic; `0<S` is explicit. Finiteness is `≠⊤`. |
| Mean formula and `m'=mean(f)` (`appendix-a-local-theory.tex:89-99`) | `velocityMeanT`, `forceMeanT`, `prescribedMeanT`; `PeriodicMeanReductionAPI.mean_formula`, `mean_derivative` | None: torus-only clause | The actual solution mean and the explicit initial-plus-force-integral trajectory are both exposed. |
| Galilean reduction to mean-zero data and force (`appendix-a-local-theory.tex:89-106`) | `galileanShiftT`, `galileanVelocityT`, `galileanForceT`, `galileanPressureT`; `transformed_solution`, `transformed_classes`, `transformed_mean_zero` | None: torus-only clause consumed by T20 | The force subtracts `meanT f`; `mean_derivative` separately proves this is `m'`. |
| Spatial translations preserve Sobolev norms (`appendix-a-local-theory.tex:101-104`) | `PeriodicMeanReductionAPI.translation_preserves_sobolev` | None | The right side is the centered untranslated slice, since removing the zero mode is not itself norm preserving. |
| Viscosity-one rescaling and inverse (`appendix-a-local-theory.tex:79-87`) | `unitViscosity*`, `restoreViscosity*`; `PeriodicViscosityRescalingAPI` | No A01/A02/A04 field | Horizon changes from `T` to `νT`; initial velocity scales by `ν⁻¹`, pressure and force by `ν⁻²`. |

Draft B intentionally has no analogue of
`A04.continuation_v2.lifespanInfiniteOfLocallyFinite`: Appendix A proves the
single-endpoint criterion and its restart, not that later convenience wrapper.

## Representation choices

### Maximality

`maximalLifespanT` remains the T10 `ℝ≥0∞` supremum. A solution is not placed on
`[0,maximalLifespanT)` by coercing that value to a real: the lifespan may be
`⊤`, and a finite supremum is not an attained horizon. Instead,
`IsMaximalPeriodicSolution` chooses one velocity and one normalized pressure
whose restrictions are `ClassicalSolutionT`s, with `PeriodicLocalRegularity`,
for every positive real `S` satisfying
`ENNReal.ofReal S < maximalLifespanT ν a f`. This is the same union-of-shorter-
intervals idea as A02 V2 and the existing `PeriodicLocalLifespan.MaximalSolution`.

### “Extends beyond”

`ExtendsBeyondT ν a f S w` includes both `RegularThroughT ν a f S` and a
specific `δ>0` plus a `ClassicalSolutionT ... (S+δ)` agreeing with `w` in
velocity and normalized pressure at every point of `[0,S)`. The redundant
`RegularThroughT` conjunct makes the T10 consumer vocabulary available, while
the explicit witness prevents “extension” from degenerating into only a
lifespan inequality.

### Continuation integral

The criterion uses

`∫⁻ t in Ioo 0 S, periodicSobolevENorm 2 (u(t,·)) ^ 2`

in `ℝ≥0∞`. A real Bochner/Lebesgue integral in Lean is totalized to zero for a
non-integrable integrand, so a bare real inequality would require a separate
integrability conjunct. The lintegral instead records divergence as `⊤` and
renders the paper's finiteness hypothesis as `squaredHTwoIntegralT S u ≠ ⊤`.
Using `Ioo` rather than `(0,S)` notation is literal; endpoint values have zero
measure.

### Mean reduction

The package follows the formula requested by the lane:

* `m(t) = meanT (u(t,·))`;
* `X(t) = ∫₀ᵗ m(r)dr`;
* `v(t,x) = u(t,x+X(t))-m(t)`;
* `h(t,x) = f(t,x+X(t))-meanT(f(t,·))`;
* `q(t,x) = p(t,x+X(t))`.

The derivative statement `m'=meanT f` makes `h` definitionally equivalent to
the appendix's `f(t,x+X(t))-m'(t)` without putting a noncomputable derivative
operator into the force definition. The output is a full classical solution,
not merely a residual equality, because T20 needs its divergence, pressure
gauge, periodicity, and Sobolev information together.

### Local Sobolev paths

T10's `IsPeriodicSobolevPath` is quantified over every nonnegative time and is
suited to globally defined forces. Requiring it directly of a solution on
`[0,T)` would demand an artificial Sobolev extension beyond a possibly
singular `T`. Draft B therefore adds the explicitly flagged
`IsPeriodicSobolevPathOn`; registration should either add this definition to
T11 or generalize the T10 path predicate to accept a time set.

## Ambiguities and rulings

1. **Force class in `prop:local`.** The proposition text allows any force
   smooth into every `H^m` on compact intervals, while Section 3 downstream
   quantifies over `F_T`. Per the lane instruction, the public existence,
   uniqueness, maximality, and continuation fields use `f∈forceClassT`.
   Restart solutions use `timeShiftT t₀ f` without falsely claiming that this
   shift is again in `forceClassT`: it may be nonzero at its new time zero.
2. **H¹ restart uniformity.** Lines 147-150 fix the original force and use its
   boundedness on `[0,S+1]`; Draft B quantifies that force before `∃δ`. It does
   not choose one duration uniformly over all forces. It does quantify over
   the H¹ datum ball and restart times, which is the quantitative local-theory
   content invoked by “common positive existence duration.”
3. **Pressure recovery.** The paper displays a Poisson equation, while the
   plan and T10 vocabulary privilege the periodic Leray graph. Draft B uses
   `P(w)=w-grad p` at order zero plus the literal zero-mean gauge. An
   implementation lemma must prove this equivalent to the displayed Poisson
   formula for smooth periodic fields.
4. **Endpoint derivatives.** `mean_derivative` is stated on `Ioo 0 T`; the
   appendix uses the equation at positive times. A one-sided derivative at
   zero could be added, but is not needed by the Galilean cancellation and is
   not separately asserted in the paper.
5. **Regularity redundancy.** `ClassicalSolutionT` already carries continuous
   Sobolev datum paths. `PeriodicLocalRegularity.sobolev_smooth` deliberately
   strengthens this to `ContDiffOn`, exactly as A01 V2 does.
6. **Pressure overlap.** Since `ClassicalSolutionT` already requires
   `PressureGaugeT`, extensions agree in pressure literally. Without that
   gauge, only equality up to a function of time would be valid.
7. **Finite terminal time.** There is no separate Lean premise `S<∞` because
   `S` is real, not extended real. This is stronger typing, not an omitted
   hypothesis.

## Needs a lemma / implementation debt

1. Register the used T10 definitions and replace the verbatim copies.
2. Prove that smooth periodic slices admit unique weighted Fourier data at
   every integer order, and upgrade their paths from `ContinuousOn` to
   `ContDiffOn` (`PeriodicLocalRegularity.sobolev_smooth`).
3. Connect `IsPeriodicLerayComplementT` to the periodic Poisson equation and
   show the recovered zero-mean pressure is unique.
4. Convert between T10 `ClassicalSolutionT` and the existing
   `PeriodicLifespan.Flow` field by field. They are distinct structures, so the
   `CLAUDE.md` structure exception forbids an `rfl` bridge; two conversions and
   round-trip lemmas are needed.
5. Prove restriction and normalized overlap agreement in the T10 carrier,
   then glue a common maximal `(u,p)` realizing every preterminal horizon.
6. Relate `squaredHTwoIntegralT≠⊤` to the existing real
   `FiniteH2Energy`/`periodicVectorSobolevNorm` spelling, including
   measurability and Parseval.
7. Establish the periodic high-order energy inequality, its integrated
   Grönwall consequence, and the finite uniform `H^m` bounds.
8. Prove the fixed-force H¹ restart theorem for shifted periodic forces and
   stitch a restart past `S` using normalized uniqueness.
9. Differentiate the spatial mean under the torus integral and derive
   `m'=meanT f` from the equation; prove the initial-plus-force integral
   formula.
10. Prove translation invariance of the weighted Fourier norm, the Galilean
    chain-rule cancellation, preservation of divergence/periodicity/pressure
    gauge, and membership of the transformed datum and force classes.
11. Prove the viscosity rescaling identities, class preservation, horizon
    scaling, and both directions of the solution conversion.

## Existing implementation candidates (not imported by the draft)

* `Paper1/PeriodicLocalLifespan.lean`
  * `ClassicalPeriodicLocalTheory.local_flow` and `finite_h2_extension` are the
    closest conditional analytic interface.
  * `normalized_flows_agree` already proves literal velocity and pressure
    agreement after normalization.
  * `MaximalSolution`, `exists_maximal_periodic_solution`, and
    `maximal_solutions_agree` closely match Draft B's maximal-object choice.
  * `exists_periodic_extension_of_finite_h2`,
    `extension_agrees_on_common_interval`, and
    `maximal_endpoint_gt_of_finite_h2` are direct continuation candidates,
    conditional on `ClassicalPeriodicLocalTheory`.
* `Paper1/PeriodicLifespan.lean`: `Flow`, `lifespan`,
  `horizon_le_lifespan`, `lifespan_le_iff`, and
  `lifespan_le_iff_no_extension` provide the order-theoretic base. `Flow` lacks
  T10's Sobolev and pressure-gradient fields, hence the conversion debt above.
* `Paper1/PeriodicFlowRestriction.lean`: `Flow.restrict` and
  `Flow.nonempty_restrict` implement shorter-horizon transport.
* `Paper1/PeriodicPressureNormalization.lean`: `normalizedPressure`,
  `normalizedFlow`, gradient/residual preservation, idempotence, and mean-zero
  theorems are strong candidates for the gauge fields.
* `Paper1/PeriodicUniqueness.lean`: `classical_uniqueness_on_Icc` is the
  velocity-uniqueness engine used by the normalized overlap theorem.
* `Paper1/PeriodicInitialData.lean`: `IsAdmissibleInitialData` is the existing
  spelling of `initialClassT`; `Flow.initial_admissible` extracts it from a
  flow.
* `Paper1/PeriodicOrdinaryLocal.lean` is **not** a direct periodic existence
  implementation: its `OrdinaryRepresentative` requires genuine ordinary
  `L²(R³)` data, impossible for a nonzero periodic field. Its finite-order
  solver is useful only after replacing that bridge with a coefficient-side
  periodic solver.
* No `Paper1/PeriodicMeanReduction*` or `Paper1/Galilean*` file was present.
  The mean/Galilean package is therefore new work, not a renaming of an
  existing declaration.
