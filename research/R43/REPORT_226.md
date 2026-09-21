# Lane 226 — R43 critical-regularity V1 contract

## 1. The theorem registered

Registered Proposition 4.3 (`prop:Rcritical1`,
`paper/sections/04-whole-space.tex:82-89`) as the 30th contract,
`R43.critical_regularity` version 1.  Its `CriticalRegularityAPI` is the four
fields of `research/R43/Spec.lean`'s `RCritical1API`: a single real `c`, its
positivity field `hc`, and the two conclusions

```lean
universal :
  ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
            < ENNReal.ofReal (c * ν) →
          maximalLifespanR ν a f = ⊤

inhomogeneousAtZero :
  ∀ ν : ℝ, 0 < ν →
    ∀ f : SpaceTimeField, MemForceR f →
      forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) →
        maximalLifespanR ν (fun _ => 0) f = ⊤
```

The only Spec substitution is the canonical registered
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`, whose definition is `rfl`
equal to the local norm.  The witness chooses

```lean
c = min (1 / (8 * R43.trilinearConst))
      (1 / (4 * (A05.gradientL6Const * A05.criticalL3Const)))
```

and binds `hc := R43.criticalConst_pos`.  Both theorem fields therefore use
the same explicit viscosity-independent positive constant.

## 2. What is now in Lean

- `verification/Contracts/V1/CriticalRegularity.lean` is the self-contained V1
  contract, importing only `Contracts.V1.Data` and
  `Contracts.V1.HomogeneousNorm`.  Its field names, binder order, strict norms,
  and conclusions match `RCritical1API`.
- `verification/Bindings/CriticalRegularity.lean` records `rfl` bridges for
  `initialClassR`, `MemForceR`, the spatial homogeneous norm, and the two force
  norms.  It binds `R43.universal_of_memForceR` and
  `R43.inhomogeneousAtZero_of_memForceR`.  Each conclusion uses the existing
  `Bindings.maximalPartial_maximalLifespanR_eq`, because the A02-local and Data
  `ClassicalSolutionR` structures are distinct inductive types.
- `verification/Tests/CriticalRegularity.lean` defines
  `checkedCriticalRegularity`, runs `TestSupport.checkAxioms`, and independently
  restates both Spec theorem fields against the checked public witness.
- `verification/contracts.json` has the append-only 30th entry with an honest
  two-clause scope and the constant's value.  `collaboration/work_items.json`
  adds the contract to R43, and `python3 experiments/tasks.py render` updated
  the generated queue and R43 card.
- `ATTEMPTS_CONTRACT.md`, `axioms_contract.lean`, and the registration update in
  `COMPARISON.md` record fidelity, the bridge route, and trust audit.

## 3. Remaining gaps

None for Proposition 4.3 or this V1 registration.  Neither clause has an added
analytic hypothesis, altered force class, weakened norm, finite-horizon
replacement, or hidden constant.  No existing frozen contract or test was
modified.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, ran Lake only from
`verification/`, and used `LEAN_NUM_THREADS=6`.

Focused build:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build Tests.CriticalRegularity
✔ [10556/10559] Built Contracts.V1.CriticalRegularity (2.9s)
✔ [10557/10559] Built NSFormalization.Section4.R43.Universal (3.2s)
✔ [10558/10559] Built Bindings.CriticalRegularity (2.5s)
ℹ [10559/10559] Built Tests.CriticalRegularity (2.5s)
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
Build completed successfully (10559 jobs).
```

Full gate (`LEAN_NUM_THREADS=6 scripts/gates.sh`), exit 0:

```text
== make check
30 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
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
exited 0; its key fields are (the closure listing is omitted here):

```text
{
  "registered_contracts": 30,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The conformance audit
`cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R43/axioms_contract.lean`
exited 0.  Output:

```text
'NSFormalization.Section4.R43.criticalConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.universal_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_initialClassR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_memForceR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_forceHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_forceSobolevENormL1_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCriticalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.inhomogeneousAtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.constant_value' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Registry stat:

```text
$ git diff --stat verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

`git diff --check` exited 0 with no output.
