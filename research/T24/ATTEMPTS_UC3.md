# T24c Uc3 — assembly and registration attempts

## Result

Uc3 closes without a named input.  The canonical two-field
`ConservativeForcingAPI` is assembled from Uc1 `zero_from_rest` and Uc2
`potential_pairing`, and the V1 binding transports every quantified solution
through the registered fieldwise `ClassicalSolutionT` conversion.

## Rest-solution search and reuse

The required pre-write search was:

```text
grep -rnE "(zero.*ClassicalSolutionT|ClassicalSolutionT.*zero|rest.*solution|zeroSolution)" \
  formalization/NSFormalization/Section3/T11 \
  formalization/NSFormalization/Section3/T24 research/T24
```

There was no existing zero-specific `ClassicalSolutionT`, but the search led
to `Section3/T11/ExtendsBeyond.lean:237`, where
`constantVelocitySolutionT c` constructs the needed solution class (including
the nontrivial Sobolev field) at unit viscosity.  `restSolution` reuses its
Sobolev witness at `c = 0` and checks the zero momentum equation directly, so
the final witness is valid for every viscosity `ν`, not only `ν = 1`.

## Structure-exception route

The contract imports `Contracts.V1.TorusLocalTheory` and reuses its distinct
contract-side `ClassicalSolutionT`.  A direct `rfl` bridge between the two
structures is impossible.  The binding therefore applies
`Bindings.TorusLocalTheory.ofContract` before invoking both canonical fields;
its velocity projection is definitionally unchanged.  The witness travels in
the other direction through `toContract`.

## Small failed attempt

The initial assembly draft tried to simplify the zero force without opening
`NavierStokes.ProblemStatement`; Lean correctly reported unknown identifiers
`pressureGradient` and `Space`.  Opening the canonical namespace fixed the
elaboration.  No increase of `maxHeartbeats` and no new lemma were needed.

## Axiom boundary

`research/T24/axioms_uc3.lean` checks the canonical API, canonical rest
solution, binding API, statement proof, converted rest solution, and checked
test declaration.  Each depends on exactly `propext`, `Classical.choice`, and
`Quot.sound`.
