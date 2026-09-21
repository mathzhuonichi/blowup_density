# Lane 301 report — T15 reconciled specification

## 1. What theorem was specified

`research/T15/Spec.lean` specifies Proposition 3.3, “Scaling at fixed
viscosity,” from `paper/sections/03-torus.tex:101-159`.  For one T14 source
packet and A's shared 17-field placement record, it defines the literal
fixed-viscosity parabolic rescaling, its unit-lattice periodization, and the
mean-normalized pressure.  The Type-valued `ScalingAPI` states the guarded
single-copy construction, one pinned periodic `ClassicalSolutionT`, unbounded
speed at `T`, both exact `eq:packetEscale` identities, the exact
`eq:packetFscale` identity, `eq:packetHs`, and the promoted subcritical
force-convergence conclusion.

Per the binding lane instruction, `forceConvergence` is parameterized by
`q : ℝ≥0∞`, assumes `q = 1 ∨ q = 2`, and uses the threshold
`criticalOrder q.toReal`.  The manuscript and reconciliation prose only spell
out its `q=1` specialization; this is recorded as the first owner question in
`COMPARISON.md`.

## 2. What Lean now contains

- The six lane-291/lane-292 provenance files are copied byte-for-byte.  Their
  Git blob hashes match the corresponding source-branch blobs.
- Registered torus data comes from `Contracts.V1.TorusData`; no registered
  T10 data declaration is recopied.
- Delimited verbatim blocks contain only the still-unregistered T10
  solution-class vocabulary, T13's `LocalizationAPI` and dependencies, and
  T14's packet structures requested by the reconciliation.
- `PlacementData` is A's unchanged 17-field structure and is a parameter of
  `ScalingAPI`, so downstream T17/T18 can share the same
  `T,x₀,B,K_*,ε₀` definitionally.
- The main structure follows reconciliation §3's field order.  It keeps B's
  summability, slice-integrability, and `MemLp` guards; bundles the PDE in one
  pinned `ClassicalSolutionT); uses A's strict `sobolevConst_pos`,
  `alphaT`, and source-point helper; and drops the definitionally true
  pressure-formula fields and A's derivable `energy_finite`.
- `scalingStatement` returns
  `Nonempty (ScalingAPI (𝔉.select ν hν) place)` for the caller's placement
  parameter, rather than pinning only proof-irrelevant localization evidence.
- The requested `rfl` checks elaborate for both
  `CompletedDenseVia` abbreviations, all three registered scaling formulas,
  the dropped pressure-normalization formula, and
  `alphaT = Contracts.V1.alpha`.

No proof, axiom, admission, or placeholder proposition was added.

## 3. Remaining gaps

This lane states but does not inhabit `ScalingAPI`.  The proof still needs the
fourteen dependencies copied verbatim into `COMPARISON.md`: compact support
placement, local finiteness and smooth periodization, pressure normalization,
fixed-viscosity PDE transport, the full periodic Sobolev solution path and
pressure-gradient field, blow-up transport, exact energy and endpoint-aware
mixed changes of variables, T13 localization integrated in time, Sobolev datum
paths, and negative-order monotonicity/limit arguments.

Three owner questions are recorded in `COMPARISON.md`: confirmation of the
lane-required `q=2` strengthening, whether the derived support radius should
receive a later named definition, and how to remove the temporary copied blocks
after T11/T13/T14 registration.

## 4. Commands run and results

- `. scripts/lean-env.sh && cd verification && lake env lean
  ../research/T15/Spec.lean` — passed with no output and zero errors.  This
  includes every `example … := rfl` check.
- `make check` — exited zero.  It retained the repository's known inventory
  notices (`BoundaryCorollary.lean` in the copied-source admission scan and
  `source_hashes_match: false`); no T15 forbidden token was found.
- `make test` — passed; only pre-existing upstream linter warnings were
  replayed.
- `make test-mutations` — passed: implementation refactor accepted; admitted
  proof, extra axiom, and weakened hypothesis rejected as required.
- `git rev-parse <branch>:<path>` versus `git hash-object <copy>` for all six
  provenance files — all six blob hashes matched.
- `git diff --check` and final forbidden-token/status audits are run
  immediately before the lane commit.
