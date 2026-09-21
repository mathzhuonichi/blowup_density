# Lane 494 — Remark 3.13 (R313)

Status: **Closed**. Branch `erenup/494-T18-P3-force-amplitude`.

## 1. Statements

- `T18.packetForce_ne_zero` takes the raw T14 packet clauses. Zero forcing
  makes the energy work term vanish; nonnegative dissipation gives zero kinetic
  energy, continuity gives zero velocity slices, and `SpeedUnboundedAtOne`
  contradicts this. The binding instantiates those clauses at any registered
  packet and at `packetImportFamily.select`.
- `packetForce_sup_pos` and `packetForce_sup_lt_top` give positive finite
  extended supremum amplitude. The canonical bundle also recovers nonzero and
  finite packet amplitude from its scaling record, without extra premises.
- `periodizedScaledForce_amplitude` proves **≥**, the option sufficient for the
  remark, rather than equality. Its exact coefficient is `(ε⁻¹)^3`. The
  single-copy source point is `(T - ε² + ε²τ, x₀ + εy)`, matching the code's
  `scaledStartTime`; it is not the correction chart based at `T`.
- `correctionForce_amplitude_le` uses exactly
  `data.correction.forceProfileConst 0`. Its proof combines the profile's
  order-zero bound, chart identity, support and lattice periodicity, giving
  the global bound `C * (ε⁻¹)^2`. An additional derivative-constant variant
  is also proved.
- `forceAmplitude_lower` proves the displayed lower bound for every
  `InsertionData` and every `PeriodicInsertionAPI data`, at every admissible
  scale. `forceAmplitude_diverges` proves extended-valued convergence to
  `𝓝 ⊤`; `forceAmplitude_real_diverges` proves the finite-real supremum tends
  to `atTop`. Neither canonical conclusion requires extra packet hypotheses.
- `T19.forceAmplitude_diverges` specializes to the fixed-ball `insertion`.
  `Bindings.forceAmplitude_from_data` exports this raw-data corollary.
- New contract `T03.force_amplitude` quantifies over every registered insertion
  record, retaining the nonzero, positive finite packet amplitude, displayed
  lower bound, and both forms of divergence. Its binding proves packet nonzero
  by the raw energy argument, not by assuming it.

## 2. Files

New proof modules:

- `formalization/NSFormalization/Section3/T18/ForceAmplitude.lean`
- `formalization/NSFormalization/Section3/T19/ForceAmplitude.lean`

New acceptance files:

- `verification/Contracts/V1/ForceAmplitude.lean`
- `verification/Bindings/ForceAmplitude.lean`
- `verification/Tests/ForceAmplitude.lean`

Research evidence: `probes/force_amplitude_494.lean`, `axioms_494.lean`,
`ATTEMPTS_494.md`, and the status in `T18_SPLIT.md`. Local command logs are
retained in `tmp/lane494/`.

Registry, proof/test entrypoints, graph, result map, guide, closure audit and
README counts updated. R313 has `depends_on: [S33, C35_T]` and an empty
`completion_from` list, as required by the actual graph schema. Coverage is
**22 Closed / 5 Partial**, with **30 registered contracts**. Both tracked PDFs
were rebuilt. The reader checker now requires the proved Closed remark.
No existing Lean implementation module was modified.

## 3. Gaps and error text

No mathematical residual remains for the requested remark.

One requested type needed correction: `Tendsto amplitude (𝓝[>] 0) atTop` is
false for finite ENNReal amplitudes, because `atTop` on ENNReal requires
eventual equality to its greatest element. The proved ENNReal statement uses
`𝓝 ⊤`; the real-valued statement uses `atTop`, with finiteness proved.

Resolved integration errors:

- `Current test roots differ from retained tests`: added the new test root.
- `KeyError: 'completion_from'`: the checker requires that key on every node;
  replaced its old dependency list with `[]` rather than omitting the key.

Resolved Lean elaboration errors and their fixes are recorded in ATTEMPTS_494.
The single-copy theorem deliberately proves the permitted lower inequality;
it does not claim the stronger equality.

## 4. Commands and results

Lean commands used `. scripts/lean-env.sh` and `LEAN_NUM_THREADS=6`, with direct
Lake commands run from `verification/`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T18.Assembly NSFormalization.Section3.T15.SingleCopy` | Pass; prerequisite closure built. |
| `lake build Tests.ForceAmplitude` | Pass; registered theorem and raw-data/selected-packet exports pass axiom checks. |
| `lake env lean ../research/T18/probes/force_amplitude_494.lean` | Pass. |
| `lake env lean ../research/T18/axioms_494.lean` | Pass; all 22 new theorem exports print exactly `[propext, Classical.choice, Quot.sound]`. |
| `python3 experiments/audit_article_axioms.py --build --output-dir tmp/article-audit --workers 2` | Pass; 61 declarations, 27 article entries, no forbidden axioms or source admission tokens. Reviewed report copied to AXIOM_AUDIT.json. |
| `python3 experiments/check_formalization_plan.py` | Pass; graph regenerated, 41 proof nodes and 27 article mappings. |
| `make check` | Pass; registry, graph, import boundaries and all 11 policy tests. |
| `make test` | Pass; full current Lean acceptance suite. |
| `make test-mutations` | Pass; implementation refactor accepted, admitted proof/extra axiom/weakened hypothesis rejected. |
| `make paper` | Pass; both PDF logs clean, declaration anchors and 30 registry declarations checked. |
| `git diff --check` | Pass. |
