# T22 U-REG — lane 423

## Successful route

Continued the uncommitted U-REG assembly/contract/binding/test and ledger draft
already present in this worktree. Assembled the three closed canonical fields.
Imported `Contracts.V1.Data`: it already supplies the registered physical norm
and datum vocabulary and imports the whitelisted Paper3 carrier/realization.
`HomogeneousNorm` is a different norm, and no `Sobolev*.lean` contract exists.
No registered carrier or norm was copied. Seven bounded-domain definitions are
restated verbatim and each has a whole-definition `rfl` bridge.

Copied the API including its field documentation directly from Spec; a textual
comparison checks the API byte-for-byte and the vocabulary modulo comments and
whitespace. Spec has no statement alias: the `Nonempty` alias is added as U-REG
requests. Distinct API structures require fieldwise maps, with `rfl` round trips
and an equivalence between their statement aliases.

Positive witness: a ContDiffBump with radii 1/4 and 1/2 times coordinateVector 0,
on Ω = ball 0 1, K = closedBall 0 (1/2). Its value at zero is nonzero; its zero
extension is supported in K. The test applies the registered two-sided estimate
for every real s to this field. Order-zero conformance repeats Spec's field.

## Constraints and observations

A direct `rfl` identification of independently declared API inductive types is
not available; the documented fieldwise conversion is used instead. No analytic
proof was changed or assumed. The registry records the closed multiplier term
and the smooth-cutoff choice, including the manifold partition-of-unity import.

The exhaustive named-declaration audit reports the exact standard triple for
37 declarations. Lean reports no axioms for the contract structure declaration
and its `Nonempty` alias (2 declarations). Thus the literal request that *every*
declaration print exactly three axioms is not met for those two logical type
declarations. Their output is preserved honestly; no artificial dependency was
introduced to force a diagnostic. No forbidden axiom occurs.

The requested Prop-valued `def boundedDomainNorm` produces Mathlib's `defProp`
style warning; so do the fieldwise conversion defs. These are not proof errors.
The Tests module builds with warningAsError. The generic mutation suite rejects
admissions, extra axioms and a weakened hypothesis; it is infrastructure coverage,
not a T22-specific numerical mutation test. All required gates pass.
