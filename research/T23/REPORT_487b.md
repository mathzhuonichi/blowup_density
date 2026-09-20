# Lane 487b — T23 U9 assembly and registration

## 1. What is proved

The U2b → U3 potential seam is closed. U3 does not use any potential identity:
its proofs require correction smoothness/divergence/support, scale bounds,
and the two cross transports. The weaker `WindowedCorrectionCore` is proved
for the literal matching supplier cutoff using agreement only on the open
interior cylinder. No global equality of different radial potentials is used.

`boundaryInsertionAPI` assembles all 48 fields. The production binding chooses
the registered I02/I03 pair, retains `A.correction = C`, and discharges every
internal supplier clause for that same family. Compact thickening of the
prescribed closed ball supplies an outer regularity ball, retaining the exact
prescribed `C.r = r` and all seven cutoff identities.

`T04.boundary_insertion` V1 registers the repaired existential on boxes
unconditionally and on bounded smooth-level domains conditional on explicit
`IBP Ω`. The registered count is **54 → 55**. The contract retains the solution,
exact lifespan and maximality, both blowup fields, support/no-slip clauses,
energy/Sobolev rates, comparison, convergence, and uniqueness. The four U9
hypothesis fields are supplied from the original domain/reference assumptions.

## 2. Lean contents

- `Section3/T23/LocalCorrection.lean`: weaker operational core, strong-to-weak
  projection, coercion, and support-in-cylinder theorem. Original U2 statements
  are unchanged.
- `Triple.lean` and `Solution.lean`: only U3 core hypothesis shapes and the
  support helper change. PressureNormalization needs no edit.
- `Assembly.lean`: literal-supplier core theorem, seven windowed U4 adapters,
  outer-ball geometry, and the complete `boundaryInsertionAPI`. U4's original
  production theorems remain unchanged.
- `Bindings/BoundaryInsertion.lean`: supplier constructors, closed existence
  theorem, registered box/IBP theorem proofs, fieldwise placement/cutoff/solution/
  API conversions and round trips, and definition bridges. The proof-side
  constructor takes raw supplier clauses internally; the registered statement
  exposes none of them as additional assumptions.
- `Contracts/V1/BoundaryInsertion.lean`: all 48 reconciled fields and G0's
  packet-indexed repaired existential over registered vocabulary, including
  registered T22 norms. Its V1 statement is the conjunction of box and explicit
  IBP branches. `Tests/BoundaryInsertion.lean` checks that complete statement.
- `probes/assembly_box_closes.lean`: actual full API on `(0,1)^3`, nonzero
  registered packet, zero reference, viscosity=T=δ=1, center `(1/2,1/2,1/2)`,
  chart radius 1/4, supplier radius 1/8. Packet nonzeroness is separately proved.
- `axioms_u9.lean`: **54 guarded declarations**, each exactly
  `[propext, Classical.choice, Quot.sound]`; the full probe adds two guards.
  The U3 probe uses explicit `C.toWindowed` at nine calls, keeping its theorem
  statements and embedded Spec unchanged. Its endpoint mutation uses the same
  projection and still fails for the intended endpoint mismatch.

Checkpoint `be6b7784` contains the seam and field assembly. Registry/work item,
generated task cards, attempts, U9 status and NEXT_SESSION are updated. The
pre-existing modified/untracked lane briefs are untouched by this work.

## 3. Remaining scope

No U9 proof or registration field remains open. G0/G1 V1 scope wording remains
owner-pending, as explicitly recorded in the registry. Unconditional scalar
IBP on arbitrary regular-level domains is outside this V1 claim. The literal
universally prescribed-cutoff statement is not registered.

The raw canonical `boundaryInsertionStatement'` has no packet validity clauses;
it is not asserted for arbitrary raw fields. The registered statement indexes
the valid packet and the binding supplies its clauses by projections. The
full raw field assembly stays in canonical code, while closed supplier choice
and the packet-indexed existence theorems live in Bindings, where I02/I03 are
available. No Contracts import was introduced into canonical code.

## 4. Commands and results

Every Lean shell sourced `scripts/lean-env.sh`; Lake ran only from
`verification/` with `LEAN_NUM_THREADS=6`.

- Pre-edit closure build of all T23 modules: passed, 10696 jobs.
- Final complete T23 closure and `lake build NSFormalization.Section3.T23.Assembly`:
  passed. `lake build Tests.BoundaryInsertion`: passed, with the new line
  `Contract BlowupDensity.Tests.checkedBoundaryInsertion: checked; standard logical axioms only`.
- Full unit-box probe and 54 guarded U9 audits: passed, zero output.
- U3 exact-field probe (explicit projection), unchanged U4 exact-field probe,
  and unchanged supplier probe: passed, zero output. U3's 42-declaration audit
  retains exactly the standard three axioms.
- U3 negative endpoint probe: rejected because `t ≤ T − ε²` does not supply
  `t ≤ T − 2ε²`, not because of a core type mismatch.
- `make check`: passed, 13 policy tests and 45 consistent work items.
- `make test`: passed for 55 registrations, including `checkedBoundaryInsertion`.
- `make test-mutations`: passed; refactor accepted and all three invalid
  mutations rejected.
- `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`:
  passed, `registered_contracts: 55`, `base_compatibility_checked: true`.
- `python3 experiments/tasks.py render` and `git diff --check`: passed.
- Comment-aware local import traversal: 1956 source files, no forbidden
  `Paper1.BoundaryCorollary` import. Changed Lean sources contain no admissions,
  added axioms, or `native_decide`; no heartbeat override remains.

The broad repository inventory still reports historical umbrella admission and
`source_hashes_match: false` diagnostics while passing; neither belongs to this
new import closure. Logs and gate exit codes are retained locally in `tmp/u9b/`.
No push, merge, rebase, or work outside this worktree was performed.
