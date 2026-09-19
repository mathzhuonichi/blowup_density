# Lane 480 — T23 U-CAN

## 1. Statements

Canonicalization is complete. `Boundary.lean` exposes all 48 reconciled fields
on the raw packet velocity, pressure, force, carrier, energy and dissipation
bounds. It imports the existing 16-field placement, seven-field cutoff,
ten-field solution and domain vocabulary. Both `boundaryInsertionStatement`
(literal) and `boundaryInsertionStatement'` (G0 repair) are definitions of Prop.
The repair chooses the whole-space supplier and cutoff together, retaining all
seven cutoff identities, center/time/radius/margin identities, reference
agreement, positive radius and both ball inclusions. No existence theorem is
claimed. `boundaryInsertionAPI_zero_cutoff` proves the exact canonical false
instance. Geometry now includes closed-ball compactness, a positive smaller
closed ball at any allowed center, and frontier separation with explicit
`IsOpen Ω`.

## 2. Lean deliverables

- `formalization/NSFormalization/Section3/T23/Boundary.lean`: public canonical
  entry point, lifespan/norm/gauge definitions, API, statements, G0 obstruction.
- `Geometry.lean`: the three requested auxiliary lemmas.
- `WholeSpaceCorrection.lean`: full 73-field raw adapter for registered I02.
  There was no whole-space CorrectionAPI record in the implementation tree;
  the T17 record is a different torus interface. No contract import or weakened
  local-core substitute is used.
- `research/T23/probes/boundary_api_on_canonical.lean`: embeds the original Spec
  byte-for-byte; bidirectional field conversions and round trips for placement,
  cutoff, solution, full I02 supplier and boundary API; T22 adapter; literal and
  repaired binder checks; equivalence of the repaired existential conclusions;
  one-line geometry consumers. The 48 fields keep their names and order.
- `research/T23/axioms_ucan.lean`: all 17 new production declarations audit to
  exactly `[propext, Classical.choice, Quot.sound]`.
- `ATTEMPTS_UCAN.md`, §1 canonical consumer table/status in `T23_SPLIT.md`, G0
  location follow-up in `SPEC_ISSUES.md`, and `NEXT_SESSION.md` handoff.

The checkout already includes lane 478's continuation: domain vocabulary lives
in `DomainSolution.lean`, imported by `NoSlipUniqueness.lean`. There were no
remaining overlapping T23 definitions to remove. **No existing Lean module was
edited**, so the deduplication edit ledger is empty and prior statements remain
unchanged. The pre-existing modified lane brief was left untouched.

## 3. Remaining work and limitations

U-CAN has no remaining implementation gap. This delivery does not prove the
repaired corollary, construct the matching registered I02/I03 supplier, discharge
U3–U6/U8, or register T23. G0 owner approval and the smooth-domain G1 IBP theorem
remain pending. Box uniqueness remains available from lane 478. The canonical
raw interface acquires packet hypotheses only when instantiated with the
registered packet by a future binding; raw fields do not assert packet validity.

The new import closure excludes `Paper1.BoundaryCorollary` (1324 resolved
project/vendor source files traversed). `make check` still prints the historical
umbrella admission at that module and `source_hashes_match: false`, while exiting
0. These diagnostics are not additions to this lane's proof closure.

## 4. Validation

Every Lean shell sourced `. scripts/lean-env.sh`; Lake ran only from
`verification/`, with `LEAN_NUM_THREADS=6`.

- Built the seven requested prior T23 modules first: exit 0.
- `lake build NSFormalization.Section3.T23.Boundary`: exit 0, 10087 jobs.
- `lake env lean` on Boundary, Geometry, WholeSpaceCorrection and all nine
  previous/continuation implementation modules: exit 0, zero output each.
- All seven non-mutation T23 probes, including the new canonical probe:
  exit 0, zero output each.
- `lake env lean ../research/T23/axioms_ucan.lean`: exit 0; all 17 exact lists.
- `make check`: exit 0; 54 registered contracts, 13 policy tests, 45 consistent
  work items. Historical diagnostics disclosed above.
- `lake test`: exit 0, 11015 jobs.
- `make test-mutations`: exit 0; refactor accepted; admission, extra axiom and
  weakened hypothesis rejected.
- Original Spec byte comparison, forbidden proof-token/True-field scan of new
  production files, source-import traversal and `git diff --check`: passed.

Committed incrementally on the assigned branch. No push, merge or rebase.
