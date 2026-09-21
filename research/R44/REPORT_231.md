# Lane 231 — R44 critical finite-horizon V1 contract

## 1. The theorem registered

Registered Proposition 4.4 (`prop:Rcritical2`,
`paper/sections/04-whole-space.tex:136-144`) as the 31st contract,
`R44.critical_finite_horizon` version 1.  Its `CriticalFiniteHorizonAPI` is the
nine-field `research/R44/Spec.lean` `RCritical2API`, token-for-token apart from
the registry-conventional structure name:

- universal positive reals `c` and `C`;
- a named `radius : ℝ → ℝ → ℝ`, its explicit formula
  `c * ν ^ (3 / 2 : ℝ) * exp (-(C * ν * S))`, and positivity on `ν,S > 0`;
- the zero-datum finite-horizon conclusion under strict inhomogeneous
  `forceSobolevENormL2 (-1 / 2)` smallness; and
- the same-radius exclusion from `breakdownSetRZero`.

The checked witness chooses `c = R44.theta / 20`, `C = 3`, and
`radius = R44.radius`.  A mechanical source comparison, normalizing only the
structure name, printed `structure_token_match: True`.

## 2. What is now in Lean

- `verification/Contracts/V1/CriticalFiniteHorizon.lean` is the independent V1
  statement and imports only `Contracts.V1.Data`.
- `verification/Bindings/CriticalFiniteHorizon.lean` records the `rfl` bridges
  for `MemForceR` and `forceSobolevENormL2`, proves the implementation constant
  pins `radiusCoefficient = theta/20` and `radiusRate = 3`, and binds
  `R44.main` and `R44.nonDensityBallZero`.  The lifespan conclusion and
  breakdown-set membership use
  `Bindings.maximalPartial_maximalLifespanR_eq`; they do not claim the distinct
  `ClassicalSolutionR` structures are definitionally equal.
- `verification/Tests/CriticalFiniteHorizon.lean` defines
  `checkedCriticalFiniteHorizon`, runs `TestSupport.checkAxioms`, and restates
  the constants, both positivity fields, radius formula, radius positivity,
  `main`, and `nonDensityBallZero` in the public vocabulary.
- `verification/contracts.json` appends the honest 31st entry;
  `collaboration/work_items.json` attaches it to R44, and
  `python3 experiments/tasks.py render` updates the generated queue and R44
  card.
- `ATTEMPTS_CONTRACT.md`, `axioms_contract.lean`, and `COMPARISON.md` record the
  exact fidelity check, binding route, non-vacuity example, and registration.

## 3. Remaining gaps

None for Proposition 4.4 or this V1 registration.  The API has no extra
differential, local-existence, continuation, or regularity premise.  It does
not replace the finite-horizon conclusion by global regularity, generalize the
zero datum, or substitute a homogeneous force norm.  No existing frozen
contract or test was modified.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, ran Lake only from
`verification/`, and used `LEAN_NUM_THREADS=6`.

Focused build:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build Tests.CriticalFiniteHorizon
✔ Built Contracts.V1.CriticalFiniteHorizon
✔ Built Bindings.CriticalFiniteHorizon
ℹ Built Tests.CriticalFiniteHorizon
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
Build completed successfully.
```

Full gate (`LEAN_NUM_THREADS=6 scripts/gates.sh`), exit 0; closure arrays and
already registered test lines are omitted:

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The separately requested architecture command
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
exited 0.  Its requested fields were:

```text
{
  "registered_contracts": 31,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The conformance audit
`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R44/axioms_contract.lean`
exited 0.  Output:

```text
'NSFormalization.Section4.R44.theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2_endpoint_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_memForceR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_forceSobolevENormL2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_radiusCoefficient_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_radiusRate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_breakdownSetRZero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCriticalFiniteHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.c_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.C_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.radiusFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.zeroForceMain' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Registry stat:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output.
