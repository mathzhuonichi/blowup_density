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

## Authorized existing-file edits

- `verification/contracts.json`: append V2 registration, retain V1.
- `formalization/blueprint/{proof_graph.json,entrypoints.json,RESULT_MAP.md,CLOSURE_AUDIT.md,README.md}`: close G36_FULL, add new proof modules and exact scope/counts. The graph schema requires `completion_from` on every node (`check_formalization_plan.py:84`), so its old edge is removed by setting `[]`; `depends_on` is `["G36"]`.
- `paper/formalization_guide.tex`, root `README.md`: article coverage and source links.
- `verification/README.md`: interface count 30.
- `research/T19/T19_SPLIT.md`: P1 status.
- Generated `DEPENDENCY_GRAPH.md` and `AXIOM_AUDIT.json` will be refreshed by the prescribed tools.
- `experiments/check_reader_documents.py`: remove `thm:insertion` from the hard-coded expected Partial labels, retaining the exact-set assertion for the five remaining entries. Required to make the reader gate agree with the newly proved coverage.

## Gate corrections

The first graph/check run reported `AssertionError: Current test roots differ from retained tests`. Added `Tests.PeriodicInsertionV2` to `entrypoints.json.test_modules` as well as the requested proof modules. No checker assertion was weakened.

The next `make check` reached the policy regression but reported `AssertionError: AssertionError not raised` in `test_recoloring_a_missing_clause_cannot_hide_whole_statement_partial`. It used G36_FULL as its formerly missing-clause fixture. Changed only that fixture to the still-Partial C35_FULL; the mutation and exact failure assertion are unchanged. This existing-file edit is required by the new coverage, like the reader's expected Partial set.

All corrected gates pass. `make paper` regenerated both tracked PDFs in `output/pdf/`; both reader build logs are clean. The V2 registry serialization retains the original Unicode text.
