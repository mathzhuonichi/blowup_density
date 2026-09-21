# Lane 495 — Partial P4 closed

## 1. Statements

Proposition 3.17 is Closed on both branches. The new bounded-domain API
quantifies over the registered bounded box-or-regular-level domain and
classical homogeneous no-slip solution. Potentials satisfy `ContDiff ℝ ∞ φ`;
there is no periodicity or compact temporal support hypothesis. The force is
literally `fun z ↦ -pressureGradient φ z.1 z.2`.

`potential_pairingOmega` proves the force-velocity integral is zero directly
using `IBP.integral_pressure_energy_zero` and `ibp_boundedDomain`. It allows
arbitrary viscosity. `restSolutionOmega` has zero velocity and pressure
`domainNormalizePressure Ω (-φ)`; normalization preserves the gradient.

At positive viscosity, `zero_from_restOmega` specializes the difference energy
identity against that rest solution. Its convection term vanishes, its energy
derivative is nonpositive, and its initial energy is zero. The zero-energy
Gronwall lemma with coefficient zero and
`eqOn_of_integral_norm_sub_sq_eq_zero` give pointwise zero velocity on
`Ico 0 T × Ω`. This is the energy route. The independent probe also closes via
`velocity_eq_of_ibp`, the energy-based uniqueness engine underlying
`noSlip_uniqueness`; the latter public wrapper requests unnecessary temporal
force support, so it is not used.

## 2. Files

- Canonical: `formalization/NSFormalization/Section3/T24/ConservativeOmega.lean`.
- Probe and audit: `research/T24/probes/ConservativeOmega495.lean`,
  `research/T24/axioms_495.lean`, `research/T24/ATTEMPTS_495.md`.
- Contract: `verification/Contracts/V2/ConservativeForcing.lean`,
  `verification/Bindings/ConservativeForcingV2.lean`,
  `verification/Tests/ConservativeForcingV2.lean`; registry ID
  `T04.conservative_forcing_v2`. V1 remains the first conjunct of V2.
- Blueprint graph, entrypoints, result map, closure audit, refreshed axiom
  audit, generated dependency graph, guide, README counts, reader checker's
  expected coverage, and both regenerated PDFs. The graph records
  `depends_on: ["C317", "BU"]` and an empty `completion_from` for schema
  compatibility. Inventory: 22 Closed, 5 Partial; 30 registered contracts.
- Status appended to `research/T24/T24_SPLIT.md`.

## 3. Gaps and resolved errors

No mathematical or verification gaps remain. Every new canonical export and
the independent probe print exactly `[propext, Classical.choice, Quot.sound]`.
No added analytic assumption, admission, custom axiom or heartbeat override.

Resolved implementation error: `Unknown constant Space.integrableOn_compact`
from malformed dot notation, fixed with a typed `ContinuousOn` intermediate.
Resolved bookkeeping errors: `Source changed: rerun the article axiom audit`
by refreshing the audit; `KeyError: 'completion_from'` by retaining an empty
schema field; reader-check `AssertionError` at line 61 by updating the old
hard-coded Partial set and adding an explicit Closed/new-target expectation.

## 4. Commands and results

All Lean commands used `scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and the
`verification/` package (the prescribed Make/audit wrappers select it).

- `lake build NSFormalization.Section3.T23.PressureNormalization NSFormalization.Section3.T23.NoSlipUniqueness`: passed.
- `lake build NSFormalization.Section3.T24.ConservativeOmega`: passed.
- `lake env lean ../research/T24/probes/ConservativeOmega495.lean`: passed.
- `lake env lean ../research/T24/axioms_495.lean`: all five exports have exactly the three standard logical axioms.
- `lake build Tests.ConservativeForcingV2`: passed, including four transitive axiom checks.
- `python3 experiments/check_contracts.py --summary`: 30 interfaces.
- `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2`: 57 declarations, 27 article entries, zero forbidden-axiom results; reviewed report copied to `AXIOM_AUDIT.json`.
- `python3 experiments/check_formalization_plan.py`: regenerated successfully; 41 proof nodes, 27 mappings, 2242 source modules.
- `make check`: passed, including 11 policy tests.
- `make test`: passed.
- `make test-mutations`: passed; refactor accepted, admission/extra axiom/weakened hypothesis rejected for their expected reasons.
- `make paper`: passed; both PDF logs clean and reader/source locations verified.
- `git diff --check`: passed.

Detailed run logs are in the worktree's ignored `tmp/495-*.log` files.
