# Lane 453-T17-U12-assembly-registration — T17 U12: assemble `CorrectionAPI` (45 fields) at the concrete `correctionData`, close `correctionStatement` (amended hypotheses, lead ruling G4), register `T02.correction`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) worker in `/data_8T/ping/blowup_density/.claude/worktrees/453-T17-U12-assembly-registration` (branch `erenup/453-T17-U12-assembly-registration`, based on
`origin/erenup/integration-section3` with every T17 unit landed: `Section3/T17/{CorrectionProfile (U3), Transport (U2: correctionData, force_eq), LatticeDeriv (U1), CorrectionDeriv, ForceDeriv (U5/U6),
ForceProfile (U4), Correction (U-CAN: the canonical 45-field CorrectionAPI over raw-field PlacementData + canonical T13/T16 records, and correctionStatement :294), ForceSupport (U7), ForceVolume (U8),
Energy (U9), Mixed (U10), Sobolev (U11)}.lean`, the T16 canonical record + registered `T02.local_potential` (`Contracts/V1/LocalPotential.lean`, `Bindings/LocalPotential.lean`), the T13 registered
`T02.localization` (`Contracts/V1/Localization.lean`, `Bindings/Localization.lean`)). Read `CLAUDE.md` (contract import rules; `rfl` bridges; structure exception → fieldwise conversions; `ensure_ascii=False,
indent=2`), **`research/T17/T17_SPLIT.md` §0 and unit U12** (`:235-246`), **`research/T17/SPEC_ISSUES.md` (G1, G3, and the new G4 lead ruling — binding)**, `research/T17/RECONCILIATION.md` (incl. the
"Lead amendment" at the end), `research/T17/Spec.lean:752-986` (the reconciled `CorrectionAPI` text the contract must match token-for-token, and `correctionStatement :980`), every
`research/T17/REPORT_{342,339,335,350,349,394,425,431,434,444,438}.md` §1 (the exact premise block each unit theorem takes — all share lane 385/425's block `(ν) {v} (hv : ContDiff ℝ ∞ v) (x₀) (T δ r)
(hvper) {θ η} (O) (θR ε₀) (hθ hη hθc hηc hθsupp hηsupp) (hr2) (hε₀) (hεtime) (hεspace)` plus lane 434's `hcube` and lane 431's `hθR`), `research/T17/probes/{correction_canonical,force_profile_canonical,
force_support_closes,force_volume_closes,energy_closes,mixed_closes,sobolev_closes}.lean` (how each field is closed at `correctionData` and how the Spec-form conversions go), the registration precedents
`Contracts/V1/LocalPotential.lean`/`Bindings/LocalPotential.lean`/`Tests/LocalPotential.lean` (lane 371) and lane 427's `MeanZeroCalculus` trio, `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder fields; no edits to existing modules (new files plus registry/work-items additions); every restated definition bridged by `rfl` (or fieldwise
  conversion for `LocalizationAPI`/`LocalPotentialAPI`/`PlacementData` records as the precedents do); every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Lead ruling G4 (binding; amended 2026-09-19 12:53Z after lane 453's counterexample — see `research/T17/SPEC_ISSUES.md` G4 + addendum)
`correctionStatement` as written (`∀ ν place v r δ, ∃ D, LocalPotentialAPI … ∧ Nonempty (CorrectionAPI …)`) is false for non-periodic `v` or `ν ≤ 0`, and the first amended block (without the chart inclusion)
is still false (lane 453's kernel-checked counterexample: chart radius `1/8`, `r = 1/4`). The assembly states and registers the **final amended** statement `correctionStatementAmended`:
`∀ ν u p f K (place : PlacementData u p f K) v r δ, 0 < ν → 0 < r → r < 1/2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v → (∀ t ∈ Ioo 0 (place.T + δ), ∀ x ∈ ball place.x₀ r, spatialDivergence v t x = 0) →
(∀ t ∈ Ioo 0 1, tsupport (fun x ↦ u (t, x)) ⊆ K) → Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius → ∃ D, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧ Nonempty (CorrectionAPI ν place v r δ D)`
— the registered `T02.local_potential` hypothesis block plus `0 < ν`, the global smoothness (G1 option (a) at the statement level; the `CorrectionAPI` field list is unchanged), the raw packet support clause
and the chart inclusion (the `ball_in_chart` field). The unamended `correctionStatement` stays in the contract as documentation only.
## Lead ruling G4 (binding)
`correctionStatement` as written (`∀ ν place v r δ, ∃ D, LocalPotentialAPI … ∧ Nonempty (CorrectionAPI …)`) is false for non-periodic `v` or `ν ≤ 0`. The assembly states and registers the **amended**
statement: `∀ ν u p f K (place : PlacementData u p f K) v r δ, 0 < ν → 0 < r → r < 1/2 → 0 < δ → IsPeriodicOn univ v → ContDiff ℝ ∞ v → (∀ t ∈ Ioo 0 (place.T + δ), ∀ x ∈ ball place.x₀ r,
spatialDivergence v t x = 0) → (∀ t ∈ Ioo 0 1, tsupport (fun x ↦ u (t, x)) ⊆ K) → ∃ D, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧ Nonempty (CorrectionAPI ν place v r δ D)` — i.e. the
registered `T02.local_potential` hypothesis block (`Contracts/V1/LocalPotential.lean:297-305`, with `K := place.Kstar`'s compactness and `0 < place.T` coming from the placement record) plus `0 < ν` plus the
global smoothness (G1 option (a) at the statement level; the field list of `CorrectionAPI` is unchanged). Name the canonical form `correctionStatementAmended` next to the unchanged `correctionStatement`,
prove the amended one, and record in the contract docstring + registry `scope` exactly why the unamended one is not provable.

## Deliverables
1. `formalization/NSFormalization/Section3/T17/Assembly.lean`: `def correctionAPI_of_smooth … : CorrectionAPI ν place v r δ (correctionData …)` assembling all 45 fields (`potential` := the T16 witness
   from the registered statement's canonical form — grep `Section3/T16/Assembly.lean` for the canonical `localPotential` existence theorem; `localization` := the canonical T13 witness
   `Section3/T13/Assembly.lean`; the structural fields `viscosity_pos`, `radius_pos`, `ball_in_chart`, `eps_le_placement` (shrink `D.ε₀ ≤ place.ε₀` — read how `correctionData`'s `ε₀` is chosen; if
   `correctionData` must be instantiated with `min … place.ε₀`, do so and say where), `reference_periodic` from the hypotheses; every quantitative field from the unit theorems at the concrete data,
   discharging their premise blocks from the hypotheses + the T16 record fields (`theta_*`, `eta_*`, `eps_*`) + the placement fields (`chartBall_in_cube` ⇒ `hcube`, `theta_radius_pos` ⇒ `hθR`,
   `eps_le_one` ⇒ `hε₀`)); `theorem correctionStatementAmended_holds`; non-vacuity: instantiate on the cube-centred witness of lane 434/438's probes (nonzero periodic reference).
2. `verification/Contracts/V1/Correction3.lean` (name it to avoid the Section 4 `Correction.lean`): `CorrectionAPI` token-for-token from `research/T17/Spec.lean:752-…` over the registered
   `Contracts/V1/{TorusData,TorusLocalTheory,Packet,PacketImport,LocalPotential,Localization}.lean` vocabulary (restate verbatim only unregistered notions — `CutoffData` if unregistered, `correctionForce`,
   `rescaledForceProfile`, the norm spellings — with provenance comments), `correctionStatement` (unamended, verbatim, documented as not provable) and `correctionStatementAmended`.
3. `verification/Bindings/Correction3.lean`: bridges/conversions, the instance from the canonical assembly, `correctionStatementAmended_holds`.
4. `verification/Tests/Correction3.lean`: `checkedCorrection3`, `run_cmd TestSupport.checkAxioms`, conformance `example`s for three fields against `Spec.lean`, non-vacuity.
5. Registry entry `T02.correction` (`version: 1`, `parent_task` per the T17 work item, honest `scope` spelling out the amended hypothesis block and G1/G3/G4), `work_items.json` + `python3 experiments/tasks.py render`;
   records `research/T17/ATTEMPTS_U12.md`, `research/T17/axioms_u12.lean`, U12 status in `T17_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root; `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0, `registered_contracts` = base + 1, `base_compatibility_checked: true`);
the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T17/REPORT_453.md`.
