# Lane 492 attempts

New modules only for Lean implementation. Placement factors the T24 constructor without editing T24 or T15 Assembly. Correction radius is min(radius/2, 1/4), supplying both positivity and the strict half-period bound.

## Resolved elaboration diagnostics

- `ThreadingAt.lean:41:51: linarith failed to find a contradiction`: the local placement projection had not reduced in the radius inequality. Added `change radius / 2 ≤ radius`.
- Constructor forwarding initially omitted `center radius hρ hcube` from `insertionDataAt_rawPremises`; supplied those arguments.
- `Unknown identifier radius` in `exists_force_close_at`: the theorem's conclusion does not mention geometry, so added the geometry variables to its `include` list.
- `reference_slice`: `linarith failed to find a contradiction` because `hδ` occurred only in the proof; added `include hδ`.
- Slice equality under a spatial derivative/support did not rewrite by the function equality alone (`Type mismatch: After simplification`). Rewrote pointwise via `congrFun` under the lambda.
- Energy equality: `rewrite failed: Did not find an occurrence ...` under unreduced function application. Added the explicit `change` used by the existing Closure proof.
- V2 contract: `Ambiguous term Space` from opening both the implementation and contract namespaces; retained only registered vocabulary. Qualified the registered maximal-partial namespace for `limsupLeft` and `speedENorm`.

All resolved. No existing Lean modules changed; no new heartbeat settings.
