# Lane 495 — bounded conservative forcing

- Read COMMON_PHASE5 and the article Proposition 3.17. Potential is globally
  smooth, not periodic; no temporal support assumption is introduced.
- Direct pairing: `IBP.integral_pressure_energy_zero` with `ibp_boundedDomain`.
- Rest witness: normalize `-φ`; the existing pressure normalization preserves
  the gradient and neighborhood smoothness.
- Energy route: specialize `difference_energy_identity` against rest, eliminate
  its convection term, and use zero initial energy and nonpositive derivative.
  Finish with `eqOn_of_integral_norm_sub_sq_eq_zero`.
- Uniqueness probe uses `velocity_eq_of_ibp`; the public `noSlip_uniqueness`
  requests compact temporal support, which is not assumed for this potential.

Existing-file edits authorized by the brief: registry, blueprint graph,
entrypoints, result map, closure/axiom audits, reader counts and guide, T24 split.

Canonical build and independent uniqueness probe pass. All five canonical
exports and the probe print exactly `[propext, Classical.choice, Quot.sound]`.
The first build caught a malformed dot-notation expression in pressure slice
integrability (`Unknown constant Space.integrableOn_compact`); an explicitly
typed `ContinuousOn` intermediate resolves it. No mathematical residual.

V2 contract and tests compile; registered as `T04.conservative_forcing_v2`.
The domain record is copied token-for-token over V1 boundary vocabulary;
`BoundaryInsertion.Contract.solutionTo` preserves the velocity definitionally.
The V1 torus record is retained as the first conjunct. Registry check passes.

Blueprint/gate adjustments:
- Regeneration initially reports `Source changed: rerun the article axiom audit`;
  the refreshed audit checks 57 declarations and 27 rows, all standard axioms.
- The graph schema accesses `node['completion_from']` unconditionally
  (`KeyError: 'completion_from'` if deleted). Keep that key empty on the Closed
  node, with both former completion parents moved to `depends_on`.
- `make paper` built both PDFs but the reader checker still hard-coded
  `prop:conservative` in its Partial set (`AssertionError`, line 61).
  Updated `experiments/check_reader_documents.py` as part of the requested
  coverage/gate update: remove that Partial expectation and require Closed
  plus the new canonical guide target. This is the only additional existing
  script edit; no checks are removed.
- Restored registry JSON's original Unicode formatting after registration.
