# Lane 501 assembly attempts

The four P5b hypotheses are supplied by RegionsOmegaData's concrete components,
packet, placements and support proofs. The two assembledVelocity definitions
have the same finiteVelocitySum body; definitional equality avoids any dedupe
or edits to unit-lane modules. All raw statement clauses are introduced and the
consumed clauses build RegionsOmegaData, following the torus assembly.

Authorized existing-file edits will cover registration, blueprint, guide,
counts, audit and the split status as requested in the lane brief.

Step 1: canonical assembly built on the first attempt. The concrete probe needed
`T18.isCompact_fundamentalCube` (the guessed T13 name did not exist) and an
explicit `Fin 1` numeral because typeclass synthesis did not unfold `data.N`.
After these changes the probe compiles, constructs the registered packet at
ν=T=1 in the unit box, and reads both blow-up and no-slip. Both canonical
assembly declarations print exactly the three standard axioms.

Step 2: V2 record/domain statement match SpecOmega token-for-token after the
registered substitutions: DomainPlacementData P.toPacketAPI, Scaling3's
packet-indexed scaled fields, and Data.spatialGradient. Registered domain and
solution types come from V1.BoundaryInsertion; all other record fields are
unchanged. Both fieldwise conversions and round trips elaborate by definitional
equality. The V2 statement conjoins the retained V1 torus statement. The test,
registered unit-box probe and all twelve assembly/binding axiom checks pass.
Existing-file edit: contracts.json adds T04.multiple_regions_v2 and keeps V1.

Step 3 existing-file edits: proof_graph closes M316_B with dependencies M316 and
B314, removes its completion edges, and points to the four proof modules and
V2 binding. The graph checker indexes completion_from on every node, so its
value is the empty list (as on other Closed nodes), rather than removing the
required schema key. entrypoints adds the proof/binding and acceptance test;
RESULT_MAP, guide, root/blueprint/verification READMEs and CLOSURE_AUDIT update
coverage, locations, input closure and the 30-interface count. The initial
regeneration caught the missing new test root, then the expected stale audit
fingerprint. A real full audit is running before regeneration and make check.

The first make paper built both PDFs but check_reader_documents.py:61 failed
with AssertionError: its hardcoded Partial set still contained prop:multiple.
Necessary coverage-check maintenance removes that entry and explicitly checks
Closed plus the V2 proof name; every other document check is retained. This is
an existing-file edit required to complete the requested paper/coverage update.

Final step-3 results: article audit 58 declarations / 27 entries / no forbidden
axioms; regenerated graph has 22 Closed / 5 Partial; make check (30 contracts,
11 policy tests), make test, make test-mutations and make paper all pass. Both
PDFs were rebuilt and their logs are clean. No unit-lane proof module changed.
