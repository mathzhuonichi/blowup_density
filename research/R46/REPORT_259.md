# Lane 259 report

1. **Theorems proved.** Proposition 4.6's completed homogeneous density and strong
   trajectory closure, with both Spec field bodies copied verbatim. The only
   named input is `I03.CompactHomogeneousRealization`.

2. **Lean deliverables.** `verification/Bindings/CompletedClosure.lean` contains
   both requested theorems and seven supporting lemmas. The homogeneous estimate
   uses the correction/source scaling powers `3/2` and `1/2`. The completed proof
   combines compact B02 approximation with compact relative density. The audit
   checks all nine declarations and a concrete zero reference; the binding also
   checks the zero completed target. Attempts and COMPARISON are documented.

3. **Remaining scope.** No further premise is needed for these conditional
   statements. The one realization input remains external. The Spec's
   `forceSobolevENorm 1 0` spelling is preserved; the proposed literal mixed-norm
   bridge is not established here. Strong closure uses direct construction from
   R to preserve its global velocity and pressure pins; density uses lane 233's
   record. No existing Lean modules or tests were changed.

4. **Validation.** Build, direct Lean check, axiom audit, `make check`, `make test`,
   mutation tests, and base-ref contract-policy check all passed. Direct Lean
   checking emitted zero output. All nine declarations use exactly
   `[propext, Classical.choice, Quot.sound]`; no heartbeat overrides or prohibited
   proof terms. Both Spec bodies passed byte-for-byte comparison. The build
   succeeds but replays existing supplier warnings, so its raw output is not
   silent. Work is committed on `erenup/259-R46-closure`; no push, merge or rebase.
