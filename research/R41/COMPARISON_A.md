# Theorem 4.1 draft A: paper-to-Lean comparison

This draft was written from the permitted manuscript excerpts and the
`Contracts.V1.Data` / `Contracts.V1.Thresholds` vocabulary only.  It does not
use another R41 statement or implementation.

## Clause map

| Paper clause | Source | Lean field | Encoding |
|---|---|---|---|
| Fix `ν,T > 0`, choose `q ∈ {1,2}`, and set `s_q = 2/q - 3/2` | `04-whole-space.tex:8` | hypotheses of every `RMainAPI` theorem field | `ν T : ℝ`, positivity hypotheses, `q : ℕ` with `q = 1 ∨ q = 2`, and `criticalOrder (q : ℝ)` |
| (i) fixed-initial-velocity density below threshold | `04-whole-space.tex:10` | `RMainAPI.fixed_initial_velocity_density` | `BreakdownDenseR ν a T (q : ℝ≥0∞) s`, after `a ∈ initialClassR` and `s < criticalOrder (q : ℝ)` |
| (ii) zero-initial-velocity density exactly below threshold | `04-whole-space.tex:11` | `RMainAPI.zero_initial_velocity_density_iff` | one biconditional using the registered `breakdownSetRZero` |
| threshold values `1/2` and `-1/2` | `04-whole-space.tex:13` | `RMainAPI.threshold_values` | the two real equalities for `criticalOrder 1` and `criticalOrder 2` |
| every reference regular through `T` | `04-whole-space.tex:13`; expanded at `:32` | `RMainAPI.regular_reference_approximation`, with `RegularReferenceR` | universal quantification over the explicit positive margin and `ClassicalSolutionR` witness that bundle `RegularThrough` |
| approximating forces and solutions | `04-whole-space.tex:13`; Theorem 4.2 at `:32,42` | `RegularReferenceApproximation.force`, `.solution`, `.force_mem`, `.force_tends_to_reference` | one positive-`ε` family; force convergence is in the same registered norm as relative density |
| same initial velocity | `04-whole-space.tex:13`; implicit in Theorem 4.2 at `:32` | `RegularReferenceApproximation.same_initial_velocity` | stated explicitly, although both solution records already have initial datum `a` |
| singularity exactly at `T` | `04-whole-space.tex:13`; Theorem 4.2 at `:34` | `RegularReferenceApproximation.lifespan_exact` | `maximalLifespanR ν a (force ε) = ENNReal.ofReal T` |
| same earlier history | `04-whole-space.tex:13`; Theorem 4.2 at `:36` | `RegularReferenceApproximation.same_earlier_history` | pointwise equality for `0 ≤ t ≤ T - 2 ε^2` |
| velocity difference tends to zero in `E_T` | `04-whole-space.tex:13`; quantitative source at `:39-40` | `RegularReferenceApproximation.velocity_tends_in_energy` | an explicit positive-`ε`, positive-radius formulation using `energyENorm T` |

## Representation choices

- The zero-velocity clause is one `↔` field.  That preserves the manuscript's
  single “if and only if” under one set of hypotheses; two implication fields
  would be logically equivalent but make accidental hypothesis drift easier.

- `q` is a natural number with the explicit proof `q = 1 ∨ q = 2`.  It is cast
  to `ℝ` only in `criticalOrder` and to `ℝ≥0∞` only in
  `forceSobolevENorm` / `BreakdownDenseR`.  This avoids both
  `ENNReal.ofReal` and `.toReal` in the theorem statement.  The Sobolev order
  `s` is real, as in `Data.forceSobolevENorm`.

- Relative `L^q(0,∞;H^s(ℝ^3))` density is exactly the registered
  `BreakdownDenseR`.  Through `RelativelyDense`, this means: for every
  `g ∈ forceClassR` and every positive `ℝ≥0∞` radius, an
  `f ∈ breakdownSetR ν a T` has `forceSobolevENorm q s (f-g)` below that
  radius.  No ambient completed-space density was substituted.

- Exact terminal time is an equality in the codomain of the registered
  lifespan: `maximalLifespanR ... = ENNReal.ofReal T`.  The density set itself
  still uses `≤ ENNReal.ofReal T`, exactly as `breakdownSetR` does.

- The registered `ThresholdAPI` was not stored wholesale in `RMainAPI`.
  Its `negativeIndex` and `energy` fields are auxiliary assertions not made by
  Theorem 4.1.  The theorem's own arithmetic rider is instead the exact pair of
  `criticalOrder` equalities; the registered `R41.threshold_arithmetic` can
  discharge them when this draft is bound without enlarging the theorem
  contract.

- `RegularReferenceR` and `RegularReferenceApproximation` are local explicit
  structures marked **needs registration**.  `Data.lean` has all their atomic
  notions but no bundle that can keep one reference velocity and one inserted
  family shared across every rider.  A `RegularReferenceR` retains the
  registered `RegularThrough ν a g T` proposition and explicitly unpacks its
  positive-margin solution witness.

- Both convergence statements use the elementary epsilon/radius definition of
  a right-hand limit.  The family is indexed by
  `{ε : ℝ // ε ∈ Set.Ioc 0 epsilon0}`.  This avoids introducing an unregistered
  topology on families while preserving “for all sufficiently small `ε > 0`.”

## Theorem 4.2 re-exports

The final sentence of Theorem 4.1 is kept on one family.  Its components are
re-exports of these Theorem 4.2 assertions:

| Theorem 4.1 rider | Theorem 4.2 source |
|---|---|
| approximating `g_ε ∈ 𝓕_R` and `u_ε` with datum `a` | `04-whole-space.tex:32` |
| force convergence in every subcritical indicated topology | `04-whole-space.tex:42` |
| exact lifespan | `04-whole-space.tex:34` |
| unchanged earlier history | `04-whole-space.tex:36` |
| `E_T` convergence | qualitative consequence of `04-whole-space.tex:39-40` |

Theorem 4.2's unbounded-speed conclusion, spatial support assertion, compact
support of `g_ε-g`, and numerical energy bound are not separate Theorem 4.1
clauses, so this draft does not add them to `RMainAPI`.

## Manuscript ambiguities and resolutions

1. The topology sentence contains `s` without saying “fix `s`.”  The draft
   quantifies `s : ℝ` after `q` and before the item-specific datum, matching the
   displayed order of the theorem.

2. “Around every reference regular through `T`” can mean every regular force or
   every chosen regular solution triple.  The draft takes the stronger,
   object-level reading: every explicit `RegularReferenceR` bundle.  Local
   uniqueness should identify the two readings, but that is not assumed by the
   statement.

3. The final sentence does not repeat `s < s_q`.  The draft keeps it under the
   subcritical hypotheses of the density assertion, because otherwise
   “approximating” in the indicated force topology contradicts clause (ii) at
   zero datum.

4. “Same earlier history” does not itself name an interval.  The draft uses the
   exact interval supplied by Theorem 4.2, `0 ≤ t ≤ T - 2 ε^2`, rather than an
   weaker eventual-agreement-on-each-compact reformulation.

5. “Singularity exactly at `T`” could be read as requiring the unbounded-speed
   limit in addition to nonextendibility.  The sentence contrasts with the
   breakdown-by-`T` set, and Theorem 4.2 states exact maximal lifespan and
   unbounded speed separately.  The draft therefore encodes this rider as
   `T_max = T`; it does not silently add the unmentioned speed assertion.

6. The energy rider says only “tending to zero,” although Theorem 4.2 gives a
   rate.  The draft states the qualitative limit and records the displayed
   estimate only as its source.
