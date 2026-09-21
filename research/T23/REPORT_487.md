# Lane 487 — U9 partial delivery; T23 remains unregistered

## 1. What is proved

The supplier preparation is now production code. The spatial solenoidal
extension preserves any prescribed positive inner radius strictly below the
outer regularity radius. The binding constructs I02/I03 at that inner radius,
retaining `A.correction = C`, exact center/time/margin, one positive common
threshold, all seven literal cutoff identities, energy/mixed/Sobolev estimates,
and both cross transports. No supplier record is assumed as an input.

This is **not** a 48-field BoundaryInsertionAPI construction. Neither
`boundaryInsertionStatement'_box_holds` nor
`boundaryInsertionStatement'_of_ibp` is proved or declared.

## 2. Lean contents

- `Section3/T23/Assembly.lean`: the arbitrary-inner-radius extension theorem
  and the precise global-potential consequence of supplying U3's core at the
  literal supplier cutoff. No replacement record or incomplete definition.
- `Bindings/BoundaryInsertion.lean`: four declarations migrated from 481's
  probe, generalized to separate inner/outer radii; uses registered I02/I03.
- `research/T23/probes/assembly_supplier_closes.lean`: a concrete supplier
  at viscosity=T=delta=1, inner radius 1/4, outer radius 1/3, zero reference
  velocity, using the existing nonzero packet constructor
  `Bindings.insertionFromData_packet` in registered PacketAPI vocabulary.
  It is not the requested unit-box full-API non-vacuity probe.
- `research/T23/axioms_u9.lean`: six exact guarded audits; the probe separately
  guards its theorem. All seven lists are exactly
  `[propext, Classical.choice, Quot.sound]`.
- `ATTEMPTS_U9.md`: exact residual, resolved compiler diagnostics, migration
  and import-collision workaround; U9 status and NEXT_SESSION updated.

No existing canonical module, Contracts/V1 file or Tests file was edited.
No deduplication was needed. The pre-existing modified lane brief is untouched.
First implementation checkpoint: `31b85fce`.

## 3. What remains open

U3 requires `LocalCorrectionCore reference.velocity ... D`. Its
`potential_formula` identifies the potential with the original reference's
radial integral at **all** times and spatial points. U2b's literal matching D
copies the whole-space extension's potential, while proving reference
agreement only on the interior cylinder. Therefore the available same-D
supplier does not discharge this core. The new checked implication isolates
exactly the unsupported global equality; it does not claim impossibility of
the intended insertion theorem.

The outstanding adapter must transfer U3 facts from a suitable local auxiliary
cutoff on the common scale interval, or prove U3 directly from the operational
supplier properties. It must retain the API's global triple formulas and may
not identify distinct potentials. U3 solution and force facts, then U4–U6 and
U8, still need instantiation for that single family. See ATTEMPTS for the
specific fields and hypotheses. The raw canonical repaired statement also
omits packet validity clauses; a raw theorem needs those clauses and the
packet-indexed binding must discharge them by projections.

Accordingly no contract trio or `T04.boundary_insertion` entry was created,
and T23's contracts list remains empty. Intended eventual scope is G0's
existential repair, unconditional boxes, and smooth domains conditional on
explicit `IBP Ω`, with owner-pending V1 wording. The requested +1 registration
and new checked line are **not achieved**.

## 4. Commands and results

All Lean invocations sourced `scripts/lean-env.sh`, ran Lake in verification,
and used `LEAN_NUM_THREADS=6`.

- Pre-edit build of all 26 T23 modules: passed, 10695 jobs.
- `lake build NSFormalization.Section3.T23.Assembly`: passed.
- `lake build Bindings.BoundaryInsertion`: passed, 10110 jobs; no new warning.
- Supplier probe and `axioms_u9.lean`: passed with zero output, including guards.
- `make check`: passed, 13 policy tests and 45 consistent work items. Existing
  broad-inventory `source_hashes_match: false` and historical umbrella admission
  diagnostics persist; neither was introduced here.
- `make test`: passed for the existing 54 registered contracts; no new T23 line.
- `make test-mutations`: passed; refactor accepted, all three invalid mutations
  rejected. These gates do not certify the unfinished T23 assembly.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`:
  passed, `registered_contracts: 54`, `base_compatibility_checked: true`.
- `python3 experiments/tasks.py render`: passed; no generated changes.
- Comment-aware import traversal of the new binding and concrete probe supplier:
  no `Paper1.BoundaryCorollary` import. `git diff --check`: passed.

Verbose build/gate outputs are retained locally under `tmp/u9/` rather than
committing the large repository-wide JSON closure inventories. No push, merge,
rebase, or work outside this worktree was performed.
