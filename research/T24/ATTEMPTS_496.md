# Lane 496 attempts

Spec-only authorization supersedes COMMON_PHASE5's proof/registration closure
procedure. Added one canonical record module and research specifications/probes.
The only edited existing file is `T24_SPLIT.md`, explicitly authorized by the brief.
No contracts, proof graph statuses or owner modules are edited.

Read the reconciled record, canonical torus component/assembly pipeline, T23
placement/solution/gauge vocabulary and I03 scaling/energy suppliers. Revised
article line numbers are 511–535 rather than the inherited 697–722.

Initial canonical build succeeded. No analytic proof was attempted or claimed.
The packet-indexed research record expands to the canonical raw-field record;
the probe checks each field and both versions of shared field expressions.

`make check` failed at the entrypoint reachability gate:
```
AssertionError: Unreferenced Lean modules: ['NSFormalization.Section3.T24.MultipleOmega']
```
The minimal remedy is one entry in `formalization/blueprint/entrypoints.json`'s
`proof_modules` list (the existing schema has no separate specification list).
This is reachability metadata, not theorem registration or proof coverage.
User clarification requested because that file is outside the explicit lane scope.

Final review: all 30 research field types match canonical fields after replacing
P.velocity/P.pressure/P.force/P.carrier/P.energyBound/P.dissipationBound with
u/p/f/K/M/D. Corrected the future supplier name to the existing
`Source.PacketScaling.speed_unbounded_at_target`. The two remaining commands
in `make check` pass independently (29 contracts, 11 policy tests).
