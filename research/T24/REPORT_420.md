# Lane 420 — T24c Uc3 conservative forcing assembly and registration

## 1. What theorem was proved

Uc3 assembles the two proved torus clauses of `prop:conservative` into
`ConservativeForcingAPI` with the exact reconciled quantifier order:

1. `potential_pairing`: for every real viscosity, positive lifespan, smooth
   unit-periodic potential, and classical solution from rest forced by
   `-∇φ`, the Haar pairing of the force with the velocity is zero at every
   time in `[0,T)`;
2. `zero_from_rest`: at positive viscosity, every such solution has zero
   velocity throughout `[0,T)`.

The implementation has no named input.  `conservativeForcingStatement` is the
statement alias and is inhabited by the same two unconditional proofs.

## 2. What Lean now contains

`formalization/NSFormalization/Section3/T24/ConservativeAssembly.lean` contains
the canonical record, `conservativeForcing`, the alias, and the genuine
viscosity-generic
`restSolution ν T hT : ClassicalSolutionT ν 0 (conservativeForceT 0) T`.
The witness has zero velocity and zero pressure.  Its nontrivial Sobolev field
is reused from T11's `constantVelocitySolutionT 0`, found by the required
pre-write grep; its arbitrary-viscosity momentum equation is checked directly.

`verification/Contracts/V1/ConservativeForcing.lean` restates the two local
definitions, two-field API, and alias from `research/T24/Spec.lean:1360-1417`
over the registered T10/T11 vocabulary.  The contract imports only another
contract.  `verification/Bindings/ConservativeForcing.lean` has `rfl` drift
guards for `PeriodicPotentialT` and `conservativeForceT`, then uses the existing
`Bindings.TorusLocalTheory.ofContract` conversion for every quantified
solution and `toContract` for the rest witness.  It exports
`conservativeForcing` and `conservativeForcingStatement_holds`.

`verification/Tests/ConservativeForcing.lean` checks the public declaration,
independently restates both fields, proves `PeriodicPotentialT 0` and
`conservativeForceT 0 = 0`, and constructs an actual contract-side
`ClassicalSolutionT` with zero velocity and pressure.  The registry now has
`T04.conservative_forcing` V1; the work queue and Uc3 split status are updated.

The current integration base acquired `T01.mean_zero_calculus` after this lane
was cut.  To make the required current-base compatibility audit meaningful
without merging or rebasing, commit `a366b9bd` carries that registration's
stable specification, binding, test, small T12 deduplication, registry/queue
state, and overlapping T24 status text byte-for-byte from the base.  The Uc3
working diff remains separate; `verification/contracts.json` therefore shows
only the one requested eleven-line registration addition.

## 3. Gaps and scope

There is no Uc3 proof or registration gap.  The paper's bounded-domain branch
with homogeneous no-slip boundary data remains deliberately outside V1 because
the registered vocabulary has no bounded-domain/no-slip carrier.  The registry
scope states this explicitly rather than identifying no-slip data with torus
periodicity.  This component closes only T24c; it does not claim the remaining
T24 affine or multiple-region components.

## 4. Commands and results

All Lake commands were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6` for builds.

Final full gate:

```text
BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 \
  scripts/gates.sh \
  NSFormalization.Section3.T24.ConservativeAssembly \
  Contracts.V1.ConservativeForcing \
  Bindings.ConservativeForcing Tests.ConservativeForcing

== make check
  "registered_contracts": 44,
  "base_compatibility_checked": false,
45 work items: ownership, contract registration and task cards consistent.
== lake build NSFormalization.Section3.T24.ConservativeAssembly Contracts.V1.ConservativeForcing Bindings.ConservativeForcing Tests.ConservativeForcing
info: Tests/ConservativeForcing.lean:24:0: Contract BlowupDensity.Tests.checkedConservativeForcing: checked; standard logical axioms only
Build completed successfully (10604 jobs).
== make test
info: Tests/ConservativeForcing.lean:24:0: Contract BlowupDensity.Tests.checkedConservativeForcing: checked; standard logical axioms only
== make test-mutations
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
== gates OK
```

Explicit current-base contract audit (the base itself has 43 registrations):

```text
python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
registered_contracts: 44
base_compatibility_checked: true
scope: Architecture checks only; run lake test for Lean type and axiom checks.
base_registered_contracts: 43
```

The axiom file output is:

```text
lake env lean ../research/T24/axioms_uc3.lean
'NSFormalization.Section3.T24.conservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.conservativeForcing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.conservativeForcingStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.ConservativeForcing.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedConservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Registry stat:

```text
git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` passed.  The changed proof/contract modules contain no
`sorry`, `admit`, `axiom` declaration, `native_decide`, or
`set_option maxHeartbeats`; the only `axioms` tokens are the required audit
commands and their expected diagnostic text.


> Lead note after review 420 (REJECT, procedural): (1) the base-ref gate failed only because the worktree predates #392 (`AffineVariation.lean`); the lead merged the current integration base below, taking the integration versions of every file outside T24 (the worker's "[base-sync]" copies of lane 427's T12 files are thereby replaced by the merged originals) and appending the registry element JSON-aware; (2) the reviewer's substantive mutation (`Ico → Ioc` in the rest-solution clause) breaks the proof as required — recorded here since the worker cannot be re-run.
