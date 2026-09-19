# Lane 480 — canonicalization attempts

## Inventory and closure

Read CLAUDE, split §§0/1/4, G0/G1 and the exact repaired statement,
Spec, reconciliation, reports 476/477/478, T18/T24 raw-field patterns, lessons.
The checkout already includes 478's continuation: domain vocabulary is in
DomainSolution, NoSlipUniqueness is its public analytic entry point.
`grep -rnE '^(structure|def) (CutoffData|ClassicalSolutionOmega|IsBoxDomain|IsRegularLevelDomain|IsBoundedBoxOrSmoothDomain|BoundaryInsertionAPI)' formalization/NSFormalization/Section3/T23`
found exactly one of each existing definition, and no BoundaryInsertionAPI.
No existing Lean module was edited; the deduplication edit ledger is empty.
The seven-module closure built successfully before implementation.

## Raw supplier adapter

The repaired existential explicitly quantifies the registered I02 CorrectionAPI.
A search for `structure CorrectionAPI` in formalization found only the distinct
T17 torus API. To preserve the full G0 statement without a contract import,
WholeSpaceCorrectionAPI copies the complete I02 record over raw velocity/carrier.
It is not an assumed supplier, a reduced local core, or a new analytic proof.
The probe checks all its fields against the registered record in both directions.
Existing cutoff, placement, solution, domain and T22 records are imported.

## Resolved development errors

- Initial build redirection: `no such file or directory: ../tmp/ucan_initial_build.log`.
  Created worktree-local tmp, then ran the required closure successfully.
- First raw supplier build: `Ambiguous term VelocityField` (also PressureField,
  Space), caused by opening both R3 and generic ProblemStatement namespaces.
  Open only R3's navierStokesResidual.
- Next build: `Unknown identifier NSFormalization.Section4.A02.spatialGradient`
  and `.energyENorm`, and `Section4.D01.mixedLebesgueENorm`.
  Search/read located existing canonical definitions at I02.Energy,
  T24.AffineEnergy and T15.Scaling; imported and used them without restatement.
- Boundary and Geometry then built successfully (10087 jobs).

Further probe/gate results are recorded below as checked.

## Probe and audit follow-up

- Full original Spec is embedded byte-for-byte (checked by Python substring
  equality). Bidirectional adapters check 16 placement, 7 cutoff, 10 solution,
  3 T22, 73 whole-space correction and 48 boundary fields. Solution witnesses
  require fieldwise conversion; lifespan uses an equivalence of Nonempty
  solution records under the supremum. Maximality transports the same witnesses.
- First probe: `Definition normsTo is a proposition; use theorem instead of def`;
  changed the proof-valued adapter to theorem. Reverse API round trip initially
  reported `don't know how to synthesize implicit argument norms`; supplied
  `(norms := norms)` explicitly because the proof-valued parameter is erased.
- Probe also checks literal/repaired raw binders by rfl, the exact repaired
  Spec conclusion in both directions (including all seven cutoff identities),
  and three one-line geometry consumers. Both arbitrary-record round trips are
  checked for the data adapters.
- Audit-only formatting attempt failed with `Unknown option pp.width`; removed
  that option. All 17 new production declarations then print exactly
  `[propext, Classical.choice, Quot.sound]` (line wrapping ignored).
- Import traversal initially matched prose inside comments; reran with nested
  block comments and line comments removed. The resolved project/vendor source
  closure contains 1324 files and no BoundaryCorollary import.

## Final gates

Boundary build: exit 0. Direct Lean checks: all 12 relevant implementation
modules and all seven non-mutation T23 probes exit 0, zero output. Axioms file:
exit 0, the 17 exact standard-three lists. No existing Lean module was changed.
`make check`: exit 0 (54 contracts, 13 policy tests, 45 queue entries);
`lake test`: exit 0 (11015 jobs); `make test-mutations`: exit 0, refactor accepted
and all three invalid mutations rejected. The check's historical umbrella
BoundaryCorollary admission and `source_hashes_match: false` remain disclosed.
