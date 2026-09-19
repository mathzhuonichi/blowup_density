# Lane 481 — T23 U2b matching supplier and correction estimates

Branch: `erenup/481-T23-U2b-matching-supplier`. No push, merge, or rebase.
Skeleton checkpoint: `b856dbb0`; completed proof/audit checkpoint: `90c98776`.

## 1. Statements

**The R1 registered matching conjunction and its correction norm estimates
are closed in the contract-facing probe.** `T23U2b.exists_matching_supplier`
constructs the spatial solenoidal extension from the locally smooth,
locally divergence-free reference, then calls the registered implementation
`Bindings.correctionV2` and `Bindings.scaling`. Neither correction nor scaling
record is an input. It returns the actual pair `C, A` and one
`D = localCorrectionData v x₀ T C.θ C.η C.plateau C.θRadius A.ε₀`, retaining:

- `A.correction = C`, `C.T = T`, `C.δ = δ`, `C.x₀ = x₀`, and
  `A.thresholds = th`;
- `0 < D.ε₀`, `D.ε₀ = C.ε₀`, and `D.ε₀ = A.ε₀` (the last follows from
  the displayed literal definition of D), hence the exact R1 inequality;
- equality of the actual local correction and the supplied correction,
  and equality of the actual local force and the supplied force, on that range;
- a nonnegative energy constant with rate `ε^(3/2)`;
- positive mixed-Lebesgue constants, for every p with `Fact (1 ≤ p)` and
  every q, including infinity, with rate `ε^(alpha p q + 1)`;
- positive Sobolev-force constants for `1 ≤ q`, `0 ≤ s ≤ 1`, with exactly
  `ε^(2/q.toReal-1/2) + ε^(2/q.toReal-1/2-s)`;
- both exact U2 cross-transport conclusions on `Ico 0 T`, including t = 0.

The key threshold fact is constructive: the I02 V2 constructor already chooses
`ε₀ ≤ sqrt ((min T δ / 4) / 2)`. I03 takes its minimum with that same number.
Thus it does not shrink this particular C. No change to I03's same-C wording
is needed, and no independently chosen correction is identified with C.

`exists_matching_registered_cutoff` chooses the literal seven-field supplier
cutoff instead: D copies C's theta, eta, plateau, radius, threshold, potential,
and correction family. It proves the force identity against the **original
local** reference and carries all three norm estimates and both cross terms
at this same D. This is the cutoff spelling required by the G0 repair.
The original-reference and extension-reference potentials are never asserted
to agree globally.

`exists_matching_supplier_on_domain` derives the local hypotheses from the
actual `ClassicalSolutionOmega`, with an interior-ball inclusion. Exterior
values of the original total reference require no regularity.

Production results supply the necessary mathematics without contract imports:
`local_match`, `local_crossTransport`, `supplierCutoff_force`, and
`ClassicalSolutionOmega.local_velocity`; energy restriction and local
energy/mixed transport; the angular-path infimum bound; and
`exists_local_sobolev_bounds`, which constructs a fixed global extension and
one threshold before quantifying q and s. The latter is an independent
canonical analytic proof, not an assumed Sobolev bound.

## 2. Files

- `formalization/NSFormalization/Section3/T23/MatchingSupplier.lean`:
  supplier correction formula, local matching, both U2 cross transports,
  literal seven-field supplier cutoff/force transport, domain locality.
- `formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean`:
  energy restriction, local energy and mixed bounds, angular realization
  of the path norm, and uniform-threshold local Sobolev-force bounds.
- `research/T23/probes/T23-U2b-matching-supplier_closes.lean`:
  original Spec embedded byte-for-byte; all original `local_correction_closes`
  checks retained in a scoped block; registered constructors, full matching
  and estimates for both cutoff spellings, actual domain instantiation, and
  four `exact` consumers for the two literal Spec/canonical U2 field forms.
- `research/T23/axioms_T23-U2b-matching-supplier.lean`:
  11 guarded production audits. Eight additional guarded audits in the probe
  cover its conversion, three supplier theorems, and four field consumers.
  All **19** print exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T23/ATTEMPTS_T23-U2b-matching-supplier.md`, this report,
  `T23_SPLIT.md` status, and the retained gate/audit logs.

No existing Lean module was edited. The new probe extends the old probe's
checks rather than modifying that existing module. No competing correction,
placement, domain-solution, or scaling record was introduced. The pre-existing
untracked collaboration brief was left untouched.

## 3. Gaps and error text

There is **no remaining failed Lean goal** in this delivery and no same-C
obstruction. The contract-facing constructor theorem lives in the research
probe because formalization cannot import `Contracts.*`/`Bindings.*`, while
the full registered record constructors live in Bindings. The implementation
modules expose canonical transport/analytic lemmas; U9 can move the checked
record bridge to its binding without assuming a supplier existential.
This report does not claim an implementation-layer inhabitant of the full
registered ScalingAPI.

The input radius r in the supplier theorem is the **local regularity radius**;
the constructed supplier has `C.r = r/2` and agrees with v on that smaller
ball throughout the open slab. This is explicit in both constructor statements.
It is not a proof of the entire canonical repaired boundary statement with its
independently prescribed radius. That statement's geometry/assembly remains
U9 work; the matching residual R1 fixes T, delta, and center and is proved as
stated. No origin-centered or torus restriction has been added.

U6 owns the path-infimum-to-slice-integral comparison, force-difference rates,
and convergence. Those are not identified definitionally with the correction
Sobolev path norm proved here. U3–U6/U8, complete BoundaryInsertionAPI assembly,
G0's owner-approved V1 wording, and smooth-domain G1 remain outside this lane.
No fresh V1 amendment is required for the registered matching itself.

All failed approaches and exact diagnostics are preserved in ATTEMPTS and were
repaired. Representative error:

```text
../formalization/NSFormalization/Section3/T23/CorrectionEstimates.lean:42:2: error: `dsimp` made no progress
```

Another revealed the genuine interval adapter requirement:

```text
P.velocity_support
has type
  ∀ t ∈ Ico 0 1, (tsupport fun x => P.velocity (t, x)) ⊆ P.carrier
but is expected to have type
  ∀ t ∈ Ioo 0 1, (tsupport fun x => P.velocity (t, x)) ⊆ P.carrier
```

The proof now restricts Ico support to Ioo explicitly. No error is hidden by an
admission, placeholder record, named conclusion input, or added axiom.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`. All Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- Initial closure build: `lake build NSFormalization.Section3.T23.Boundary
  NSFormalization.Section3.T23.LocalCorrectionBridge
  NSFormalization.Section3.T23.StatementRepair
  NSFormalization.Section3.T23.BoxIntegration` — exit 0, 10087 jobs.
  Boundary's closure includes the consumed placement, extension, domain,
  no-slip-energy, and difference-energy modules.
- Additional consumed closures: `Bindings.CorrectionV2`, `Bindings.Scaling`,
  `NSFormalization.Section4.D01.HalfOrder`, and
  `NSFormalization.Section4.I03.Angular` — exit 0.
- `lake build NSFormalization.Section3.T23.MatchingSupplier
  NSFormalization.Section3.T23.CorrectionEstimates` — exit 0, 10093 jobs;
  only replayed upstream diagnostics.
- `lake env lean` on each new production module — exit 0, **0 output bytes**.
- `lake env lean ../research/T23/probes/T23-U2b-matching-supplier_closes.lean`
  — exit 0, **0 output bytes**, including eight guarded audits. Rerun after
  adding all estimates to the literal supplier-cutoff variant: same result.
- `lake env lean ../research/T23/axioms_T23-U2b-matching-supplier.lean`
  — exit 0, **0 output bytes**, with eleven exact guarded audits.
- `make check` — exit 0: 13 policy tests, 45-item queue check.
  It still reports the pre-existing umbrella BoundaryCorollary admission and
  `source_hashes_match: false`; neither is introduced by this lane.
- `make test-mutations` — exit 0. Its initial `lake test` completed the 11015-job
  registered closure. Implementation refactor accepted; admission, extra-axiom,
  and weakened-hypothesis mutations rejected as required.
- Explicit production import traversal: **1330** project/vendor files, no
  `Paper1.BoundaryCorollary` import. No forbidden proof tokens outside comments
  in the four delivered Lean files. No heartbeat override was added.
- Original Spec byte containment and `git diff --check` — pass.

Commits were made for the skeleton and each closed lemma/checkpoint. No work
outside this worktree and no remote write was performed.
