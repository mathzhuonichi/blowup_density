# T18 U12 — assembly attempts (lane 455)

## Accepted route

The canonical `PeriodicInsertionAPI (data : InsertionData)` has all 45 fields,
in reconciled order. `RawPremises data` bundles only the three explicit raw
clauses required by U7/U9: slice support in `data.carrier`, nonnegative
`energyBound`, and nonnegative `dissipationBound`. `assemble` supplies each
field from its same-named U1–U11 theorem. The canonical existence statement
quantifies viscosity, the six raw packet fields, placement, scaling, initial
datum, force, radius, margin, cutoff, reference, correction, paper hypotheses,
and those raw clauses. No analytic lemma was reproved.

The binding reuses the U1 placement and reference conversion pattern and the
U9/U10 probe's exact sign arguments. It discharges support with
`P.velocity_support`; `energy_isLUB` applied to the time-zero square root gives
`hM`, and `dissipation_eq` plus `Real.sqrt_nonneg` gives `hD`. Both directions
of the placement, scaling, correction, and insertion API conversions are
fieldwise, with `rfl` round trips. T11 solution witnesses are converted by
`TorusLocalTheory.ofContract`/`toContract`. The maximal and lifespan fields
use the U8 probe's explicit predicate rewrites. Every copied definition has
a named `rfl` bridge; the existence statement has a fieldwise iff bridge.

The contract's T18 structure and existence definition are byte-identical to
`research/T18/Spec.lean`. Only unregistered T15 scaling vocabulary is copied.
Compatibility `export`s retain the historical namespaces while using the
registered packet, localization, cutoff, placement, and correction objects.

## Base mismatch and additive prerequisite recovery

The worktree began with 46 contracts. The requested remote base
`origin/erenup/integration-section3` at
`33515e1fea080d094f2b97863a843317e259480e` has 48. The first compatibility check
failed with:

```text
AssertionError: Removed stable specification: verification/Contracts/V1/Correction3.lean
```

Recovered exactly eight **new** files byte-for-byte from that base: canonical
T17/T20 `Assembly.lean` and the `Correction3`/`CriticalRegularityT` contract,
binding, and test trios. Restored their two registry entries and work-item
contract references. No existing Lean module was changed, and no merge,
rebase, or push was performed. The T18 contract then switched from a local
T17 restatement to the registered `Correction3.Packet` vocabulary. The final
count is 49 = current base 48 + this lane's one new registration.

The requested ID is `T03.periodic_insertion`; `parent_task` is `T02`, following
the literal T18 work-item deliverable. This pre-existing bucket discrepancy
is recorded in the registry scope rather than silently changing the task.

## Resolved elaboration failures

- Compatibility `abbrev`s opened beside the registered namespace caused
  `Ambiguous term CutoffData` and `Ambiguous term PacketImportAPI`. `export`
  aliases retain the registered declaration identity and avoid that clash.
- Without `open scoped ContDiff`, `∞` in `ContDiffOn` was read as `ℝ≥0∞`
  instead of `WithTop ℕ∞`. Opened the intended scope.
- `intro` on the canonical statement also introduces its `let data`; the
  first attempt named that local `h` and left `RawPremises h → Nonempty …`.
  Introduced both `data` and the raw-premise proof explicitly.
- `simpa only [isMaximalPeriodicSolution_eq] using h.maximal` did not unfold
  the local `data` projections. Reused the U8 probe verbatim: introduce the
  scale, rewrite the registered predicate, then `exact h.maximal ε hε`.
- The reverse localization conversion initially used `cFrac_pos`; the actual
  six-field API calls that field `constant_pos_finite`.
- A local notation `A` needs `(A).field`; `A.field` parsed as a qualified
  identifier and produced `Unknown identifier «A».ε₀`.
- A doc comment cannot annotate `export` (`unexpected token 'export'; expected
  'lemma'`); changed that comment to an ordinary provenance comment.
- The audit formatting experiment `set_option pp.width 240` produced
  `Unknown option pp.width`. Removed it and reran the full axiom file.

## Non-vacuity staging

T13 and T11 are already inhabited. The recovered T17 registration includes a
concrete nonzero constant-reference correction example and an amended
existence theorem with positive viscosity/radius/margin, `r < 1/2`, global
smoothness and periodicity, local divergence, packet support and ball-in-chart
hypotheses. It does not by itself supply a correction at a future full T15
scaling witness for the registered blow-up packet. The remaining concrete
end-to-end input is a full T15 U15 scaling/placement witness and compatible
reference/cutoff/correction data satisfying those hypotheses. Both canonical
and binding `nonvacuity_of_witnesses` theorems are proved; the test repeats the
explicit existential witness hypothesis. No unconditional non-vacuity is
claimed and no field is deferred.
