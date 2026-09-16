# R41 reconciled paper-to-Lean comparison

The binding authority for this file is `research/R41/RECONCILIATION.md` on
`erenup/integration`.  The independent inputs are preserved byte-for-byte as
`DraftA.lean` / `COMPARISON_A.md` / `REPORT_236.md` and
`DraftB.lean` / `COMPARISON_B.md` / `REPORT_237.md`.  The reconciled statement is
`research/R41/Spec.lean`, in namespace `BlowupDensity.R41.Draft`.

## Paper-clause map and provenance

| Paper clause | Reconciled Lean field / clause | Draft A provenance | Draft B provenance | Reconciliation ruling |
|---|---|---|---|---|
| Fix `ν,T>0`, `q∈{1,2}`, and `s_q=2/q-3/2` (`04-whole-space.tex:8`) | Every analytic field quantifies `ν`, positivity, `T`, positivity, then `q : ℝ≥0∞` with `q = 1 ∨ q = 2`; the threshold is `criticalOrder q.toReal` | Used `q : ℕ`, casts to `ℝ`/`ℝ≥0∞`, and jointly bound `ν T` before their positivity proofs | Used `q : ℝ`, `ENNReal.ofReal q`, and sequential `ν`, `T` binders | Use the cross-R45/R46/R47 convention `q : ℝ≥0∞`; keep `ν,T` universally quantified rather than record parameters |
| Fixed-initial-velocity density below threshold (`:8-10`) | `fixedInitialDensity`: after `s` and `a ∈ initialClassR`, `s < criticalOrder q.toReal → BreakdownDenseR ν a T q s` | `fixed_initial_velocity_density`, the same registered density predicate, with the subcritical proof before `a` | `fixedInitialDensity`, with `a` before the subcritical proof | Keep B's field name and quantifier order, A's registered `criticalOrder` spelling, and the ENNReal `q` convention |
| Zero-initial-velocity density iff subcritical (`:8,11`) | `zeroInitialDensityIff`: `RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔ s < criticalOrder q.toReal` | One biconditional field `zero_initial_velocity_density_iff` | One biconditional field `zeroInitialDensityIff` | Keep one `↔`, not the skeleton's separate `densityZero` / `nonDensityZero` fields |
| Threshold values (`:13`) | `thresholdValues`: `criticalOrder 1 = 1/2 ∧ criticalOrder 2 = -1/2` | Same pair as `threshold_values` | Literal arithmetic pair | Keep A's registered-function formulation under B's field name |
| Every reference regular through `T` (`:13`; made explicit at `:32`) | In `regularReferenceApproximation`, quantify `g`, `δ>0`, and a named `v : ClassicalSolutionR ν a g (T+δ)` | Bundled `RegularReferenceR` containing `RegularThrough`, a margin, and a solution | Explicit `δ`, positivity, and `v` | Use B's explicit quantifiers; do not add a second structure |
| One approximating force/velocity family (`:13,32,42`) | `∃ ε₀>0, ∃ f u : ℝ → SpaceTimeField`, with all pointwise and limit conclusions conjoined | Returned a Type-valued `RegularReferenceApproximation` record | One inline `Prop` with shared existential witnesses | Use B's inline proposition so every structure field is a proposition and simultaneity is retained |
| Sufficiently small positive `ε` (`:32`) | Pointwise conclusions hold for every `ε ∈ Ioo 0 ε₀` | Indexed a subtype over `Ioc 0 ε₀` | Used `Ioo 0 ε₀` and additionally required `2*ε₀^2<T` | Keep B's open interval; drop `2*ε₀^2<T`, which the paper does not state and which is unnecessary when the history interval is empty |
| `g_ε ∈ F_R` and a solution with the same initial velocity (`:13,32`) | `MemForceR (f ε)` and `∃ U : ClassicalSolutionR ν a (f ε) T, U.velocity = u ε` | Separate family fields `force_mem`, `solution`, and an explicit redundant same-initial equality | The solution type carries datum `a`; its velocity is identified with the shared `u ε` | Use B's formulation: the two solution records already carry the same datum `a` |
| Singularity exactly at `T` (`:13,34`) | `maximalLifespanR ν a (f ε) = ENNReal.ofReal T` | Exact lifespan, without speed blow-up | Exact lifespan, without speed blow-up | Keep exact lifespan only; the separate `limsup` display at `:35` is an R42 clause and the skeleton's extra conjunct is dropped |
| Same earlier history (`:13,36`) | For `t ∈ Icc 0 (T-2*ε^2)` and all `x`, `u ε (t,x)=v.velocity (t,x)` | Equivalent split inequalities `0≤t` and `t≤T-2ε²` | `Icc` pointwise equality | Keep B's interval spelling and the cutoff supplied by Theorem 4.2 |
| Force approximation (`:13,42`) | `Tendsto (fun ε => forceSobolevENorm q s (f ε-g)) (𝓝[>] 0) (𝓝 0)` | Explicit positive-radius epsilon definition | The registered one-sided filter limit | Use B's `Tendsto`; retain the subcritical `s < criticalOrder q.toReal` hypothesis |
| Velocity approximation in `E_T` (`:13,39-40`) | `Tendsto (fun ε => energyENorm T (u ε-v.velocity)) (𝓝[>] 0) (𝓝 0)` | Explicit positive-radius epsilon definition | The registered one-sided filter limit | Use B's qualitative limit; do not expose R42's quantitative rate |

The rider deliberately does not add R42's spatial support, compact force
correction, pressure, quantitative constants, or unbounded-speed conclusion.
Those are true of the supplying insertion family but are not separate clauses
of Theorem 4.1's final sentence.

## Earlier skeleton comparison

`research/section4/STATEMENTS.md` §1(iv) fixed `ν,T,q` as record fields, used a
real `q`, split clause (ii) into `densityZero` and `nonDensityZero`, and phrased
the rider as a single-radius witness with `IsMaximalSolution` and a blow-up
`limsup`.  The reconciliation instead universally quantifies the common
parameters in each field, makes clause (ii) one literal biconditional, and uses
one whole `ε`-family with two limits.  Exact lifespan represents the rider's
“singularity exactly at `T`”; the skeleton's `limsup` conjunct belongs to the
separate `04-whole-space.tex:35` R42 display and is not repeated.

## Registered-vocabulary checks

The spec uses `BreakdownDenseR`, `RelativelyDense`, `breakdownSetRZero`,
`criticalOrder`, `maximalLifespanR`, `energyENorm`, `MemForceR`, and
`ClassicalSolutionR` directly from `Contracts.V1.Data`.

The two completed-density abbreviations are not used by R41: Theorem 4.1 is
relative density inside `forceClassR`, while `CompletedDenseVia` belongs to
Proposition 4.6's completed-space topology.  Nevertheless, the requested drift
checks are present in `Spec.lean` and elaborate by `rfl`:

```lean
CompletedDense q s S = CompletedDenseVia q s (IsSobolevPath s) S
CompletedDenseHomogeneous q s S =
  CompletedDenseVia q s (IsHomogeneousPath s) S
```

## Proof dependencies

- `fixedInitialDensity`: lane 235 `Bindings.breakdownDenseR_of_subcritical` (exact shape modulo the `q` convention).
- `zeroInitialDensityIff`: `←` lane 235 `breakdownDenseR_zero_of_subcritical`; `→` lane 232 `not_breakdownDenseR_zero_of_q` (contrapositive at `s ≥ s_q`).
- `thresholdValues`: arithmetic.
- `regularReferenceApproximation`: lane 233 `insertionLifespanV2_of_data` + R42 record fields (`history`, `forceConvergence`, `energyRate`/`E_T` convergence — check the registered `energyRate`
  gives `energyENorm T (u_ε − v) → 0`; if only the rate estimate is registered, derive the limit), `memForceR_force`, `lifespan`, `solution`.
So the registration lane can bind all four fields; no new analysis is expected.

## Binding plan

| Spec field | Landed supplier(s) | Exact adaptation needed |
|---|---|---|
| `fixedInitialDensity` | Lane 235, `BlowupDensity.Bindings.breakdownDenseR_of_subcritical` | Unfold `criticalOrder`; its conclusion uses the same `q : ℝ≥0∞`, the same hypothesis `q = 1 ∨ q = 2`, and threshold `2 / q.toReal - 3 / 2`.  Apply it after the spec's `a` binder, reordering only the `a ∈ initialClassR` and subcritical proof arguments. |
| `zeroInitialDensityIff`, reverse implication | Lane 235, `BlowupDensity.Bindings.breakdownDenseR_zero_of_subcritical` | Unfold `criticalOrder`, then unfold/simplify `BreakdownDenseR` and `breakdownSetRZero` to the spec's explicit `RelativelyDense` left side.  This supplier already uses the spec's `q : ℝ≥0∞` convention. |
| `zeroInitialDensityIff`, forward implication | Lane 232, `NSFormalization.Section4.R41.not_breakdownDenseR_zero_of_q NSFormalization.Section4.R41.rMainThresholds` | Argue by contradiction from `criticalOrder q.toReal ≤ s`.  Lane 232 binds `q : ℝ` and concludes at exponent `ENNReal.ofReal q`; split the spec proof `q = 1 ∨ q = 2`, instantiate lane 232 with real `1` or `2`, and simplify `ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞)`, `ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞)`, and the corresponding `.toReal` values.  Rewrite `rMainThresholds.exponent q 0` by its formula to `criticalOrder q`, and simplify `BreakdownDenseR`/`breakdownSetRZero`.  This is the required bridge from lane 232's real-`q` convention to the reconciled ENNReal convention. |
| `thresholdValues` | Registered definition `criticalOrder` | `norm_num [criticalOrder]`; no analytic supplier is needed. |
| `regularReferenceApproximation` | Lane 233, `BlowupDensity.Bindings.insertionLifespanV2_of_data`; R42 V2 record fields and `BlowupDensity.Bindings.InsertionLifespan.memForceR_force` | The named reference `v` and `δ>0` first give `ENNReal.ofReal T < maximalLifespanR ν a g`; apply lane 233 and align `L.family.a`, `.g`, and `.T` with `a,g,T`.  Take `ε₀ := L.family.ε₀`, `f := L.family.force`, and `u := L.family.velocity`; turn `ε ∈ Ioo 0 ε₀` into `ε ∈ Ioc 0 ε₀`.  Use `memForceR_force`, `L.lifespan`, and `L.solution`; use registered velocity uniqueness to identify the R42 reference velocity with the explicitly quantified `v` on the common interval, which transports `L.family.history` and the energy difference.  `L.family.forceConvergence` supplies the force limit after rewriting its registered threshold formula to `criticalOrder q.toReal`.  Derive the qualitative `E_T` limit by squeezing `L.family.energyRate` against its explicit right-hand side, which tends to zero as `ε ↓ 0`. |

The rider adaptation preserves one R42 family throughout.  In particular, no
separate calls may be made for lifespan, history, force convergence, and energy
convergence, because that would lose the paper's same-family assertion.

## Open questions for the owner

None at the statement level.  The lead reconciliation resolves the exponent
type, biconditional packaging, rider hypothesis, history window, exact-lifespan
interpretation, and every kept/dropped conjunct.  Lane 249 still has routine
binding work—most visibly the real-`q` case split for lane 232 and deriving the
qualitative energy limit from R42's rate—but those require no new mathematical
or specification decision from the owner.

## Registration (lane 249, 2026-09-17)

Registered as the 32nd contract `R41.main_thresholds` V1: `verification/Contracts/V1/MainThresholds.lean` (`MainThresholdsAPI` = this `RMainAPI`, byte-identical body), `Bindings/MainThresholds.lean` (witness `mainThresholds` following the binding plan above: lane 235 density, lane 232 non-density by cases on `q`, lane 233 record called once for the rider with the energy limit squeezed from R42's registered rate), `Tests/MainThresholds.lean` (`checkedMainThresholds`). See `REPORT_249.md`.
