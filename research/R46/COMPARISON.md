# Proposition 4.6 — reconciled comparison

This comparison merges blind Draft A (lane 242) and blind Draft B (lane 243)
under the binding decisions in `RECONCILIATION.md`.  The authoritative statement
is `paper/sections/04-whole-space.tex:218-229`; Theorem 4.2, referenced by the
proposition, is at `:31-43`.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled Lean field | Draft A | Draft B | Reconciliation ruling |
|---|---|---|---|---|
| `04-whole-space.tex:218-219`: for fixed `a ∈ X_R` and `ν,T>0`, density in every full `L^q(0,∞;H^s)` with `q∈{1,2}` and `s<s_q` | `REnergyAPI.completedSobolevDensity` | Same field name and quantifier order; `CompletedDense q s`; threshold `criticalOrder q.toReal` | Named `sobolevDensity`; expanded `CompletedDenseVia q s (IsSobolevPath s)`; threshold written `2 / q.toReal - 3 / 2` | Keep A's field name and abbreviation. Keep `q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, and registered `criticalOrder q.toReal`; do not insert `ENNReal.ofReal` casts. The predicates are definitionally equal, checked by `example ... := rfl` in `Spec.lean`. |
| `04-whole-space.tex:219`: density in full `L²(0,∞;Ḣ⁻¹)` | `REnergyAPI.completedHomogeneousDensity` | Same field name; `CompletedDenseHomogeneous 2 (-1)` | Named `homogeneousDensity`; expanded `CompletedDenseVia 2 (-1) (IsHomogeneousPath (-1))` | Keep A's field name and abbreviation. The predicates are definitionally equal, checked by a second `example ... := rfl`. The dense set in both clauses is exactly `breakdownSetIn forceClassCompact ν a T`. |
| `04-whole-space.tex:221`: “For every reference in Theorem 4.2” | Outer binders of `REnergyAPI.strongTrajectoryClosure` | Takes packet/scaling records first and a reference compatible with the correction | Takes raw `a,ν,T,g,δ,R`, plus redundant `RegularThrough`, then insertion-ball data | Adopt B's raw-data order: `a`, membership, `ν`, positivity, `T`, positivity, `g`, membership, `δ`, positivity, explicit `R : ClassicalSolutionR ν a g (T+δ)`, then `∃ P, A`. Drop `RegularThrough` because explicit `R` supplies the reference. Drop `x₀,r` because Proposition 4.6 does not mention the insertion ball. |
| Theorem 4.2 `:32,34` and its proof `:53`, imported by “inserted solutions” at `:221` | Per-`ε` conjunct inside `strongTrajectoryClosure` | Relies only on `InsertionFamilyAPI`; omits registered force membership, exact lifespan, and full classical-solution witness | Explicitly requires `MemForceR (A.force ε)`, exact lifespan `ENNReal.ofReal T`, and a `ClassicalSolutionR` whose velocity and pressure are the family fields | Keep B's three clauses for every `ε ∈ (0,A.ε₀]`. Lifespan and solution are the conclusions re-exported by `R42.insertion_lifespan_v2`; retaining them prevents “trajectory” from meaning an arbitrary field. |
| `04-whole-space.tex:221-223`: `‖u_ε-v‖_{E_T} → 0` | First `Tendsto` conjunct of `strongTrajectoryClosure` | Inside local `StrongTrajectoryClosure`, using `A.T` and `A.velocityDifference` | Inline, using raw `T` and `R.velocity` | Inline the literal B form after pinning `A.scaling.correction.T = T` and `A.scaling.correction.v = R.velocity`: `energyENorm T (fun z => A.velocity ε z - R.velocity z)`, along `𝓝[>] 0`. No local wrapper is needed. |
| `04-whole-space.tex:224-226`: the sum of `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x` distances tends to zero | Second `Tendsto` conjunct of `strongTrajectoryClosure` | Literal three-norm sum on `A.forceDifference ε` | Literal three-norm sum on `A.force ε - g` | Keep the single summed limit exactly: `forceSobolevENorm 1 0 + forceSobolevENorm 2 (-1) + forceHomogeneousENorm 2 (-1)` on the same difference and the same existential family. Do not split it into separately witnessed limits. |
| `04-whole-space.tex:228`: the homogeneous norm applies only to the compact difference | Homogeneous summand of `strongTrajectoryClosure` | Applies it to `A.forceDifference ε` | Applies it to `A.force ε - g` | Apply `forceHomogeneousENorm` only to `fun z => A.force ε z - g z`; impose no homogeneous-space membership on the background `g`. |

## Final quantifier shapes

The completed Sobolev field has the exact order

```text
∀ a, a ∈ initialClassR → ∀ ν, 0 < ν → ∀ T, 0 < T →
  ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
    ∀ s, s < criticalOrder q.toReal → CompletedDense ...
```

The completed homogeneous field stops after `a, ν, T` and fixes `q = 2`,
`s = -1`.  The strong-closure field has the exact order

```text
∀ a, a ∈ initialClassR → ∀ ν, 0 < ν → ∀ T, 0 < T →
  ∀ g, MemForceR g → ∀ δ, 0 < δ →
    ∀ R : ClassicalSolutionR ν a g (T + δ), ∃ P, ∃ A, ...
```

The packet and family are conclusion witnesses, not caller-supplied hypotheses.
The family correction is pinned to `a,T,g,R.velocity,R.pressure`; its internal
ball and margin remain implementation data.

## Registered-vocabulary checks

`CompletedDense` is an abbreviation for
`CompletedDenseVia q s (IsSobolevPath s)`, and
`CompletedDenseHomogeneous` is an abbreviation for
`CompletedDenseVia q s (IsHomogeneousPath s)`
(`Contracts/V1/Data.lean:741-753`).  `Spec.lean` contains both generic equality
checks as literal `example ... := rfl` declarations; Lean accepts them.

The known mismatch between pointwise-in-time realization predicates
(`IsSobolevPath` / `IsHomogeneousPath` quantify every `t ≥ 0`) and the a.e.
equivalence of Bochner space is inherited from registered vocabulary.  Both
drafts identified it, and the reconciliation rules that it is not an R46
statement change.

## Proof dependencies

- Completed Sobolev density: **proved in lane 256** as
  `Bindings.completedSobolevDensity`.  The proof composes B01's
  `bochnerPartial.approxCompact` with lane 252's `density_compact`, extracts the
  perturbation path from the `forceSobolevENorm` infimum, and closes under path
  addition and the Bochner triangle inequality.  No additional hypothesis is
  used.
- Completed homogeneous density: B02's completed homogeneous approximation
  is now registered in `HomogeneousPartialV2`; its composition with compact
  relative density remains a separate R46 binding clause.
- Strong closure: lane 233's record + `R42.insertion_family` fields `energyRate`, `forceConvergence` at `(1,0)`, `(2,−1)` + a homogeneous convergence at `(2,−1)` (the `L²Ḣ⁻¹` clause — `Scaling` omits the homogeneous scaled estimate; open, I03).

## Binding status (lane 256)

| Reconciled field | Status | Binding |
|---|---|---|
| `completedSobolevDensity` | **proved** | `verification/Bindings/CompletedSobolevDensity.lean` |
| `completedHomogeneousDensity` | not part of lane 256 | pending R46 assembly |
| `strongTrajectoryClosure` | not part of lane 256 | pending R46 assembly |

## Open questions for the owner

1. **Resolved before lane 256:** the full homogeneous completed-space assembly
   is registered by `HomogeneousPartialV2`; only the R46 composition remains.
2. Should the missing same-family `L²_tḢ⁻¹_x` scaling convergence be added as an
   I03 V2 field, or proved privately in the eventual R46 binding?
3. The registered realization predicates require values at every nonnegative
   time while the completed Bochner carrier is a.e.-quotiented.  The present
   statement deliberately inherits this convention; does the owner want a
   later vocabulary revision, independently of R46 registration?
