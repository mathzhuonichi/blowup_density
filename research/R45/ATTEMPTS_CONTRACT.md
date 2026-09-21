# Lane 262 — R45 V1 contract registration attempts

## Target and fidelity

The registered structure is the complete four-field `RClassesAPI` from
`research/R45/Spec.lean`: `density`, `zeroIff`, `schwartzDensity`, and
`regularReference`, in that order. `ForceClassesAPI` copies the entire
structure block byte-for-byte after only the permitted structure-name
substitution. It retains the guarded ambient class, ENNReal exponent and
`q = 1 ∨ q = 2` restriction, strict `criticalOrder q.toReal` threshold,
Schwartz specialization, and every binder and conjunct of the inline rider.

The contract imports only `Contracts.V1.Data`. No local proposition, theorem
hypothesis, placeholder field, or additional definition is introduced. The two
completed-space definitional checks in the research spec remain outside the
structure, as required: they concern Proposition 4.6 rather than this relative
density corollary.

## Accepted binding route

Lane 257 already supplies the exact guarded `density` and `zeroIff` statements
by case analysis between the lane-252 compact instances and its rapid
instances. It also supplies the exact `schwartzDensity` field. The only missing
assembly is `regularReference`: eliminate the guard
`Y = forceClassCompact ∨ Y = forceClassRapid`, substitute `Y`, and return lane
254's `regularReference_compact` or lane 257's `regularReference_rapid`.

All four supplier statements already use `Contracts.V1.Data` vocabulary,
including its `ClassicalSolutionR` and `maximalLifespanR`. Consequently this
registration needs no new A02/Data structure conversion or lifespan bridge;
those transports were performed inside the supplier bindings. The final
`forceClasses` witness assigns the four declarations directly.

## Diagnostics and rejected changes

The first focused build succeeded. No field failed to bind, and no alternate
or weakened statement was attempted. In particular, the rider was not derived
from an arbitrary `forceClassR` theorem, no terminal unbounded-speed conjunct
was added, and the guarded class hypothesis was not generalized to an
arbitrary subclass.

The mechanical fidelity comparison reports
`structure_byte_match: True` after replacing only `RClassesAPI` with
`ForceClassesAPI`.
