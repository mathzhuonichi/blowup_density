# R45 draft A: manuscript-to-Lean comparison

This is an independent transcription of `cor:Rclasses`. It uses only the
paper, the R45 one-line blueprint contract, and registered V1 vocabulary.

## Paper clause to Lean field

| Paper clause | Lean rendering in `DraftA.lean` | Notes |
|---|---|---|
| `04-whole-space.tex:8`: fix `ν,T>0`, `q∈{1,2}`, `s_q=2/q-3/2` | Every field begins `∀ ν T : ℝ, 0 < ν → 0 < T → ∀ q : ℕ, (q = 1 ∨ q = 2) → ...`; `rClassesThreshold q` is exactly `2 / (q : ℝ) - 3 / 2` | `q : ℕ` gives canonical casts to the real threshold formula and the `ℝ≥0∞` norm exponent. |
| `:10`, transported by `:195`: density for each fixed `a∈X_R` below threshold | `compactDenseBelow`, `rapidDenseBelow` | The target set is `breakdownSetIn Y ν a T`, not the whole-space `breakdownSetR`, so membership of every approximant in the selected subclass is part of the proposition. |
| `:11`, transported by `:195`: zero-datum density iff below threshold | `compactZeroIff`, `rapidZeroIff` | Both directions are retained. The threshold is not assumed outside the equivalence. This also encodes the “complete if-and-only-if classification at `a=0`” emphasized on line 195. |
| `:13`, transported by `:195`: same datum, same earlier history, exact singular time, and `E_T` convergence around every regular reference | `compactReferenceApproximation`, `rapidReferenceApproximation`, using `HasReferenceApproximationRider` | The chosen reference is a `ClassicalSolutionR ν a g (T+δ)` with `δ>0`. Given independent positive force and energy radii and any `0≤S<T`, the field produces an approximating force and solution agreeing on `[0,S]`, force-close in `L^q_tH^s_x`, energy-close in `E_T`, and with maximal lifespan exactly `T`. |
| `:13`: “same initial velocity” | The reference and approximant solution types have the same index `a`: `ClassicalSolutionR ν a g (T+δ)` and `ClassicalSolutionR ν a f T` | This uses the registered solution structure's `initial` field rather than repeating a pointwise equality. |
| `:13`: thresholds are `1/2` for `q=1` and `-1/2` for `q=2` | The shared formula in `rClassesThreshold`; all density and iff fields restrict `q` to `1` or `2` | The displayed values are arithmetic reductions of the formula, so no redundant proposition fields are added. |
| `:183-192`: definitions of `F_c`, `F_rd`, and `S_σ` | Registered `forceClassCompact`, `forceClassRapid`, and `initialClassSchwartz` | No class definition is copied locally. In particular, the registered rapid class retains every mixed-derivative decay seminorm with a separate bound, not one common bound. |
| `:195`: “In particular” for every fixed `a∈S_σ` in the rapid class | `rapidSchwartzDenseBelow`, `rapidSchwartzReferenceApproximation` | These are direct `S_σ` statements. A consumer need not first establish `initialClassSchwartz ⊆ initialClassR`. The zero-data iff remains the standalone, stronger `rapidZeroIff` field. |
| `:198`: compact corrections keep the proof within `F_c` and `F_rd` | In every density field, `RelativelyDense ... Y (breakdownSetIn Y ...)`; in every rider, the witness satisfies `f ∈ Y` | Compactness of the correction is proof mechanism, not an additional conclusion of the corollary, so no field asserts existence of a decomposition `f=g+h`. |
| `:198`: critical regular balls stay nonempty relative balls | Reverse directions of `compactZeroIff` and `rapidZeroIff` | This is proof support for non-density at and above threshold, not a separately stated corollary conclusion. |
| `:198`: no compactness is required of the nonzero reference velocity or pressure | The rider universally quantifies an arbitrary registered `ClassicalSolutionR`; it imposes no support or decay condition on its velocity or pressure | Only the reference force belongs to the selected ambient class. |

## Encoding choices

### Two ambient-class copies

The API uses separate compact and rapid fields. A parameterized theorem over
an unconstrained `Y` would overstate the paper unless it also carried a finite
enumeration hypothesis `Y = forceClassCompact ∨ Y = forceClassRapid`. Separate
fields make omissions visible and allow the rapid/Schwartz specialization to
remain explicit. `breakdownSetIn` and `RelativelyDense` are still parametric
internally, so both the target and the closure ambient are exactly the selected
class.

### Relative topology

The phrase “relative `L^q(0,∞;H^s)` topology” is rendered with registered

```lean
RelativelyDense (q : ℝ≥0∞) s Y (breakdownSetIn Y ν a T)
```

Thus a target `g` is quantified only in `Y`, every witness lies in the
breakdown subset of `Y`, and distance is the registered
`forceSobolevENorm q s (f-g)`. It is not density in the completed Bochner
space and it is not the test-function topology.

### The inherited approximation rider

The manuscript says “tending to zero” and “same earlier history” but does not
bind a sequence in Theorem 4.1. `HasReferenceApproximationRider` uses the
equivalent neighborhood formulation supported by the insertion theorem:
arbitrary positive force and `E_T` tolerances, and arbitrary earlier cutoff
`S<T`. The two tolerances are independent, so the statement really gives
simultaneous convergence. Agreement through every prescribed `S<T` expresses
the expanding common history without choosing an artificial sequence or rate.

The exact-singularity conclusion is equality
`maximalLifespanR ν a f = ENNReal.ofReal T`, stronger than mere membership in
the by-time-`T` breakdown set. The reference is supplied as a chosen solution
through `T+δ` rather than merely by `RegularThrough`; its velocity is needed
on the right side of both history equality and the energy norm.

`HasReferenceApproximationRider` is a concrete local definition, not a
placeholder proposition. **Needs registration:** V1 Data has the constituent
`ClassicalSolutionR`, `energyENorm`, norm, and lifespan notions, but no
registered predicate combining the full Theorem 4.1 rider.

### Initial classes

Literal replacement of `F_R` on line 195 changes the force class, not
`X_R`; consequently both ambient classes retain the theorem for every
`a∈initialClassR`. The extra rapid fields record the explicitly highlighted
`a∈initialClassSchwartz` formulation. No compactness or rapid-decay condition
is imposed on initial data beyond those registered classes.

## Manuscript ambiguities and resolutions

1. **Scope of “Theorem remains valid”.** It could be read as only items (i)
   and (ii), but the theorem's line 13 is an asserted rider and its proof on
   line 179 calls out energy/history. Draft A therefore includes it for both
   force classes.
2. **Which class gets the highlighted zero iff.** Grammatically, “in the
   rapid-decay class” most closely modifies the Schwartz sentence, while the
   opening sentence transports all of Theorem 4.1 to both classes. Draft A
   therefore gives the complete zero iff for both `F_c` and `F_rd`.
3. **Does `F_rd` replace `X_R` by `S_σ`?** The corollary says only that `F_R`
   is replaced, then says “in particular” for Schwartz data. Draft A retains
   `X_R` for the general rapid clause and separately exposes its `S_σ`
   specialization.
4. **Meaning of “same earlier history”.** No cutoff or convergence mode is
   bound on line 13. The insertion theorem has equality through
   `T-2ε²`; Draft A states equality through every requested fixed `S<T`.
   The restriction `0≤S` reflects that solutions and history begin at time
   zero.
5. **Meaning of “velocity difference tending to zero”.** No family index is
   present in the theorem statement. Draft A uses an arbitrary positive
   `E_T` radius rather than introducing a sequence; it also requires force
   and energy accuracy simultaneously.
6. **“Regular through `T`”.** The preliminary definition means existence
   through `T+δ` for some `δ>0`. Draft A quantifies `δ`, its positivity, and a
   chosen reference solution explicitly because the rider compares velocity
   fields.
7. **“Singularity exactly at `T`”.** Draft A interprets this as exact maximal
   lifespan equality, not only unbounded speed and not only lifespan `≤T`.
   The corollary inherits the exact-lifespan wording from line 13; unbounded
   speed is stated in the insertion theorem but not repeated in Theorem 4.1's
   rider, so it is not added here.
8. **Rapid seminorm formulation.** The paper uses all mixed derivatives
   `∂_x^α∂_t^j`, while the registered predicate packages them by joint
   Fréchet-derivative order with separate existential constants. Draft A uses
   that registered choice unchanged and does not introduce a common bound.
9. **Threshold display sentence.** The explicit values `1/2` and `-1/2` are
   consequences of `2/q-3/2` at the only permitted `q`; adding fields for
   those identities would duplicate arithmetic rather than add a corollary
   obligation.
10. **Proof mechanism versus conclusion.** “The force correction is
    spacetime compact” is why class membership is preserved. The corollary
    does not state a correction/decomposition result, so Draft A records the
    membership consequence but not the internal construction.
