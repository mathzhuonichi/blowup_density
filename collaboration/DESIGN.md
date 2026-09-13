# Design basis and limits

The design was checked against current primary Lean project sources on
13 September 2026. The source material informs the repository's engineering
conventions; its external contribution rules are not instructions to change
this repository's mathematical goal.

## Practices reused

- Mathlib separates its library from `MathlibTest` and sets a Lake `testDriver`.
  It also separates wanted statements from accepted mathematics. We use a
  separate verification package and keep unimplemented PDE specifications in
  the work queue instead of importing admitted placeholders. See
  [Mathlib's Lake configuration](https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean).
- Batteries also uses a separate test library and `testDriver`. This supplies
  a conventional `lake test` entry point instead of a project-specific list
  of shell commands. See
  [Batteries' Lake configuration](https://github.com/leanprover-community/batteries/blob/main/lakefile.toml).
- Mathlib's assertion tests check dependency boundaries. Our architecture
  checker enforces the direction from specifications to bindings to tests,
  and excludes the admitted legacy umbrella and schematic citation modules
  from accepted test closures. See
  [MathlibTest/AssertExists.lean](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/AssertExists.lean).
- Lean's own `collectAxioms` traverses declaration dependencies. Our small
  test helper uses that API directly, including transitively imported axioms,
  instead of grepping source or matching pretty-printer output. It is compiled
  and tested under the pinned Lean 4.34.0-rc2 toolchain.
- The official Lean Action supports separate build/test steps, Mathlib cache
  reuse and package-directory selection. Our PR workflow pins the action at
  revision `96e06131c0e9943c780388fd166f55d1e2fa0433`, runs the selected test
  package, and cancels superseded runs. See the
  [pinned action definition](https://github.com/leanprover/lean-action/blob/96e06131c0e9943c780388fd166f55d1e2fa0433/action.yml).

## Why contracts and bindings are separate

A specification states the exact expected mathematical type independently of
the current implementation's names. A binding supplies a term of that type
from the existing implementation. A test typechecks that term and audits its
transitive axioms. Moving a proof or changing a tactic only changes its binding
or implementation; the contract continues to express the same obligation.

Changing the contract to fit a broken implementation is a different change.
The PR-base compatibility check therefore preserves existing versioned specs,
registered acceptance tests and active registrations. New versions can be
added without dropping the old checks. The tests deliberately fail if a
binding only proves a weaker statement.

We tested four cases in actual Lean: a binding refactor passes; a `sorry`,
an extra assumed axiom and a weakened negative-index hypothesis each fail for
the intended reason. Five separate policy tests exercise version immutability,
test deletion, registry disabling and allowed binding/new-version changes.

## Honest coverage and maintenance

The first contract covers a reusable arithmetic component, not the full
Navier-Stokes theorem. Each of the 30 mathematical tasks has a work card, but
most need reviewed concrete interfaces before bulk proof filling is sound.
The ready queue initially contains compatibility work and two specification
tasks. It does not mislabel these as ready proofs of the main theorem.

The manuscript-fidelity review cannot be eliminated: a Lean theorem may prove
the wrong definition without violating its type. Changes to canonical
definitions, upstream pins, the axiom helper or CI require explicit human
review. Toolchain upgrades also require compatibility checks; no promise is
made that a test suite will remain executable on every future Lean release
without maintenance. The intended permanence is the mathematical contract,
not the absence of necessary regression failures.

The old snapshot checker was adjusted accordingly. Its optional `--snapshot`
mode still verifies historical byte identity, but normal PR checks allow
source evolution and ignored build caches. Keeping a copy manifest as a
universal correctness test would prevent the very proof development this
repository is meant to support.
