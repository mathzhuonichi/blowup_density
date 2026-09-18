# Lane 358 — T16 `lem:potential` assembly (`localPotential`) — report (Opus prover; transcribed by the lead from the agent's final message, since the report-file guard blocked the agent's own write)

Commit `c60fd8bc` on `erenup/358-T16-assembly` (includes the merge of `erenup/352-T16-lattice-lift` at its fixed local-cancellation interface a6f0e836). No `sorry`/`admit`/`axiom`/`native_decide`, no named input, no placeholder/alias, no goal repackaging; every declaration `[propext, Classical.choice, Quot.sound]`.

## 1. What was proved
`theorem localPotential : localPotentialStatement` (`Section3/T16/Assembly.lean`), i.e. for `v U K x₀ r T δ` with `0 < r < 1/2`, `0 < T`, `0 < δ`, `IsCompact K`, `v` unit-periodic and smooth / divergence-free on `Ioo 0 (T+δ) ×ˢ ball x₀ r`, `U` spatially supported in `K` for `t ∈ Ioo 0 1`: `∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D`. All **26 fields** are discharged for general local `v` (supersedes lane 347's `v = 0` witness). Witnesses: `potential := timePotential v x₀`; `correction ε := latticeLift (physicalCorrection v x₀ T θ η ε)`; `θ, η, O, θRadius, ε₀` from `exists_originCutoff` / `exists_timeCutoff` / `exists_threshold` (347).

Discharge: 16 cutoff/threshold fields (347); 3 potential fields via `exists_potential_on_ball` (351); 7 correction fields via `correction_fields_of_chart` (352) with `hWformula = rfl`, `hWcompact = physical_compact`, `hWtsupp = physical_support`, and the new local-reference companions
- `physicalCorrection_contDiff`, `physicalCorrection_divergence` — global `C^∞` and divergence-freeness of `physicalCorrection v x₀ T θ η ε` from `v` smooth only on the chart cylinder (joint spacetime truncation `cutoffPotential_contDiff` of `(η_ε θ_ε) • timePotential v x₀` via `contDiff_cutoffSmul_of_ballSmooth`, `spatialCutoff_tsupport_ball`, `temporalCutoff_tsupport_Ioo`);
- `latticeLift_sliceSupport_closed` — closed-support companion of 352's `latticeLift_sliceSupport`;
- `physicalCorrection_cancels` — the local cancellation datum `⟨O, IsOpen O, O ⊆ ball x₀ r, packet ⊆ periodicSet O, ∀ x ∈ O, v + W = 0⟩` on the scaled plateau `O = x₀ + ε • O_plateau`, using the local curl identity `spatialCurl_timePotential_on_ball` (351); the packet bound uses `periodicScaledPacket = latticeLift (scaledPacket)`, a time-truncated packet `w' = if z.1 < T then scaledPacket z else 0` (the raw packet has no all-time support bound), and `latticeLift_sliceSupport_closed`;
- helpers `periodicSet_mono`, `plateau_subset_ball`.
The reconciled Spec's statement follows through the probe's `specStatement_of_module localPotential`.

## 2. Files
`formalization/NSFormalization/Section3/T16/Assembly.lean`; `research/T16/probes/assembly_closes.lean` (canonical statement + Spec copy closed; nonzero constant divergence-free instance); `research/T16/axioms_assembly.lean` (11 declarations); `research/T16/ATTEMPTS_ASSEMBLY.md`; status line in `research/T16/COMPARISON.md`.

## 3. Gap
None for T16. Design note: the pre-fix whole-ball `hWcancel` of lane 352 was unsatisfiable for the concrete correction (`W` supported in `ball x₀ (ε·θRadius)`, so `v + W = −v ≠ 0` wherever `θ_ε ≠ 1`); the assembly needed the local-plateau interface.

## 4. Commands and results
`lake build NSFormalization.Section3.T16.Assembly` → success (9360 jobs), 0 errors; `lake env lean` on the module → exit 0 (three `if_pos`/`if_neg` deprecation warnings, same kind as `Source/PacketForceExtension.lean`); probe → 0 errors, `#print axioms` incl. `localPotential` standard; axioms file → 11 × `[propext, Classical.choice, Quot.sound]`; `make check` → OK; forbidden-token grep → none.
