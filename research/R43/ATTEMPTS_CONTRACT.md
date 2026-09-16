# Lane 226 — R43 V1 contract registration attempts

## Target and fidelity check

The registered structure is `research/R43/Spec.lean:165-247` with exactly the
four fields `c`, `hc`, `universal`, and `inhomogeneousAtZero`.  The two theorem
fields retain the Spec's binder order, strict `ℝ≥0∞` inequalities, force norms,
zero datum, and infinite-lifespan conclusions.  The only definition
substitution is the required canonical
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`; its body is definitionally
equal to both the Spec-local and D01 implementation spellings.

The deliverable sketch called the positivity assignment `c_pos`.  That is the
implementation theorem `R43.criticalConst_pos`; the Spec field itself is named
`hc`.  To preserve the requested token-for-token field names, the binding uses
`hc := R43.criticalConst_pos` and does not rename the contract field.

## Binding route

- `initialClassR`, `MemForceR`, `dotHomogeneousENorm`,
  `forceHomogeneousENorm`, and `forceSobolevENormL1` all bridge by `rfl`; the
  adapter records each correspondence explicitly.
- `Data.ClassicalSolutionR` and the Section4/A02 copy are distinct inductive
  types.  Consequently `maximalLifespanR` does not bridge by `rfl`; both fields
  rewrite with the existing
  `Bindings.maximalPartial_maximalLifespanR_eq`, exactly as
  `axioms_endpoint.lean` and `axioms_universal.lean` do.
- One record uses `c := R43.criticalConst` and
  `hc := R43.criticalConst_pos`, then binds the two final R43 theorems directly.
  No intermediate estimate or extra hypothesis is exposed in the API.

## Attempts and diagnostics

The first focused invocation ran `lean` directly on the new contract and then
the binding.  The contract elaborated, but direct `lean` does not install its
new `.olean` into Lake's build directory, so the binding stopped with
`object file .../Contracts/V1/CriticalRegularity.olean ... does not exist`.
Running `lake build Tests.CriticalRegularity` from `verification/` built the
dependency in the correct order and passed.  This was a build-order issue, not
a statement or proof mismatch.

No Spec field failed to bind, and no weakening, placeholder proposition,
additional axiom, or heartbeat override was needed.
