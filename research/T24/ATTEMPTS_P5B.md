# Lane 500: P5.3 and P5.4

## Scope and interface

Only `MultipleOmegaRegions.lean` is introduced. P5.1/P5.2 constructors remain
with lane 497. Theorems take component velocity functions and the exact global
support/pin facts; the assembly supplies `fun j => (component j).velocity`.
The sum is definitionally `finiteVelocitySum`.

## P5.3

Agreement uses `Finset.sum_eq_single` and pairwise disjoint balls. Raw
`speed_unbounded_at_target` applied to `zeroPastField_speed` gives witnesses.
A witness has positive speed; the threaded global component support puts it
inside its ball directly. No periodization or spatial chart is used.
Initial compile exposed Lean section-variable omission (`Unknown identifier
component_support`); explicitly including the proof variables fixes it.

## Authorized existing-file edits

- `formalization/blueprint/entrypoints.json`: register the new proof module.
- `research/T24/T24_SPLIT.md`: unit status entries (at completion).

## P5.4

Closed via the compact-support route. `component_tsupport` uses the raw scaled
support and cube-free placement to put the closed support inside the open ball.
`fderiv_of_notMem_tsupport` then gives global gradient vanishing outside it.
`eLpNorm_restrict_eq_of_support_subset` preserves both component norms on Ω;
no measurability or boundary-null-set assumption on Ω is needed for these bridges.
A generic at-most-one-nonzero-summand lemma yields squared-norm additivity,
then `lintegral_finsetSum'` gives slice additivity. The energy bound uses
`I03.eLpNorm_scaled_slice` and `l2Norm_zeroPastField_le` directly, a slice-level
version of `energyEssSup_scaled_le`. Dissipation uses
`energyGradient_scaled_eq` (which proves the `scaled_total_dissipation` identity)
and `scaled_dissipation_integrableOn` for time measurability. Constants remain
exactly M and D. Gradient is I02's full Euclidean matrix, not the operator norm.

One elaboration correction: rewriting under the set-integral congruence initially
reported `Tactic rewrite failed: Did not find an occurrence of the pattern
eLpNorm ...`. `dsimp only` reduces the applied integrand lambdas before rewriting.
No analytic residual or extra hypothesis was introduced.

## Validation and metadata

- Dependency closure and the new module build successfully.
- Direct module and four-field probe Lean runs exit 0 with zero output.
- All 17 module theorems print exactly the standard three axioms.
- First `make check` stopped with `Source changed: rerun the article axiom audit`.
  The common closing procedure explicitly requires a fresh audit after source
  edits; rerun it and refresh `AXIOM_AUDIT.json`, with no coverage changes.
- Additional authorized metadata edit: `formalization/blueprint/AXIOM_AUDIT.json`
  (fresh audit required by `make check`). The graph is regenerated only if its
  rendered audit summary changes. P5.5/full article closure is not claimed here.

Final gates passed: full article audit (56 declarations, no forbidden axioms),
`make check` (29 contracts, 11 policy tests), and probe axiom audit (all four
exactly standard-three). Audit metadata changed only the source fingerprint and
source count; generated graph and article coverage were unchanged.
