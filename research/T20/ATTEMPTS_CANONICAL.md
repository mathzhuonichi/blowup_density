# T20 canonical statement lane — attempts and decisions

## Canonicalization

- Imported canonical T10 data/solution vocabulary, T11 local-theory and
  assembly vocabulary, and T12 mean-zero calculus modules.
- Restated only the T20 namespace of `research/T20/Spec.lean`: 17 helper
  definitions and the 23-field `CriticalRegularityTAPI`.
- Added the requested existential statement definition
  `criticalRegularityStatement := Nonempty CriticalRegularityTAPI`; it stores
  no witness and proves no API field.
- Did not duplicate any T10/T11/T12 declaration. In particular, the manuscript
  `PeriodicContinuationAPI` already exists canonically in T11 alongside the
  proved narrowing `PeriodicContinuationH3API` and the named H¹ predicates.

## Structure exception

The Spec and canonical `CriticalRegularityTAPI` are distinct inductive types.
The probe therefore uses explicit fieldwise `toModuleAPI` and `ofModuleAPI`
conversions, followed by `rfl` round trips. All 23 fields are copied in both
directions; no theorem about any mathematical field is proved.

## Checks and corrections

- First build exposed that `forceTimeMeasure` is not exported by opening T10;
  it is owned by `Section4.A02`. The canonical module now names that imported
  object explicitly in its `open` declaration.
- The probe cannot compare the two `Nonempty` statement definitions by `rfl`
  because their element structures are distinct. It instead uses the two
  fieldwise conversions and `propext`; this is precisely the structure
  exception, not a proof of API content.
- The initial direct `lake build` output replayed warnings from existing
  dependencies. The target itself builds successfully; the required direct
  `lake env lean` invocation is used to establish zero output for the new
  module.

## H¹ result

The only order-one ball occurrences in the Spec are lines 402 and 437, in the
copied T11 `restart` and `restartBeyond` fields. The T20-specific API does not
mention them. Per `research/T11/H1_GAP.md` §3, the current T20 criterion route
uses the ball-free continuation fields, with the proved H³ package supplying
their implementation; see `H1_CHECK.md`.
