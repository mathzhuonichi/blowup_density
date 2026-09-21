# I02 contract review — `I02.correction` (V1)

Lane `011-I02-contract`, HEAD `94acf9c`, merge base `c8bde6e`. Read-only pass. Integration
has moved on only in `Contracts/V1/Data.lean` docstrings and bookkeeping, so every
base-ref check below uses `--base-ref c8bde6e`, as `ATTEMPTS.md` §8 records.

## Verdict: **ACCEPT**

Gates green, axioms exact, the contract asserts nothing (10 `def`s, one `structure`, one
`def … : Prop`; no `theorem`/`example`/`instance`), every re-defined notion is guarded,
and all 73 fields transcribe a claim I opened in Lemma 3.4, Lemma 3.5 or Theorem 4.2's
opening. Six findings, all Low or Trivial; none blocks I03/R42.

## 1. Gates (from WT root; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

| command | result |
|---|---|
| `make check` | exit 0. `Explicit axiom/admission tokens, all copied sources: 11`; `check_contracts` OK; `test_contract_policy` `Ran 13 tests … OK`; `check_work_queue`: `30 work items: ownership, contract registration and task cards consistent.` |
| `make test` | exit 0, three lines: `Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only`, `…checkedPacket: …`, `…checkedCorrection: …`. 9.6 s (warm cache). No `error`/`sorry`/`declaration uses` in the log. |
| `make test-mutations` | exit 0, 1 m 48 s. `implementation_refactor: accepted` / `admitted_proof: rejected as required` / `extra_axiom: rejected as required` / `weakened_hypothesis: rejected as required` / `Mutation suite passed.` |
| `check_contracts.py --base-ref c8bde6e` | exit 0. `registered_contracts: 3`; closures 5 / 534 / 597 modules; **`base_compatibility_checked: true`**. |
| `build_changed_lean.py --base-ref c8bde6e --dry-run` | `Changed Lean modules: Bindings.Correction, Contracts.V1.Correction, NSFormalization.Section4.I02.Energy, NSFormalization.Section4.I02.Mixed, NSFormalization.Section4.I02.Reference, NSFormalization.Section4.I02.Support, Tests.Correction` — exactly the expected seven. |
| same, no `--dry-run` | exit 0, `Build completed successfully (9361 jobs)`, **13.96 s wall** — every job `Replayed`, i.e. a warm cache; this is not a cold-build figure. |
| `tasks.py render` in a `/tmp` copy | exit 0, `diff -r` against `collaboration/` → identical. Cards are regenerated. |

## 2. Axioms

Scratch `/tmp/i02_axioms.lean` importing `Tests.Correction`, run with `lake env lean`
from `WT/verification`, then deleted. **32 declarations, every one**
`depends on axioms: [propext, Classical.choice, Quot.sound]` — nothing else:
`Tests.checkedCorrection`; `Bindings.correction` and all 13 bridges; `Reference`'s
`timePotential_contDiffOn`, `spatialCurl_timePotential_on`, `exists_local_truncation`
and both `_congr_slice`; `Support`'s `spatial_support_volume`,
`temporal_support_length`, `isOpen_spaceMap_image`, `scaledPacket_slice_empty`,
`scaledSupport_eq_spaceMap`; `Energy`'s `energyEssSup_le`, `energyGradient_le`,
`spatialGradient_memLp`, `eLpNorm_spatialGradient_sq`; `Mixed`'s `exists_slicePath`,
`continuous_slicePath`, `slice_memLp`.

## 3. Hygiene

`grep -nE "sorry|axiom|admit|native_decide|unsafe"` over the contract, the binding,
the test and the four new modules: **zero hits**, comments included. Case-insensitive
adds only `import TestSupport.Axioms` and `run_cmd TestSupport.checkAxioms` in
`Tests/Correction.lean`.

## 4. Re-definition ↔ source ↔ bridge

Contract imports are `Contracts.V1.Data` and `Contracts.V1.Packet` only, so the
allowlist of `check_contracts.py` is respected. Every copied notion is verbatim
against the source I opened, and every one has a guard: **13 bridges, 11 by `rfl`.**

| contract notion (`Contracts/V1/Correction.lean`) | source, opened | bridge in `Bindings/Correction.lean` |
|---|---|---|
| `derivativeEntry` :90 | `vendor/…/NavierStokes/SpatialCurl.lean:23-24` | `derivativeEntry_eq` `rfl` |
| `curlLinear` :95 | `SpatialCurl.lean:30-33` | `curlLinear_eq` `rfl` |
| `curl` :102 | `SpatialCurl.lean:49` | `curl_eq` `rfl` |
| `cross` :106 | `Paper1/RadialPotential.lean:15-18` | `cross_eq` `rfl` |
| `scaledSpatialCutoff` :114 | `Paper1/CorrectionProfile.lean:135-136` `spatialCutoff` | `scaledSpatialCutoff_eq` `rfl` |
| `scaledTemporalCutoff` :120 | `CorrectionProfile.lean:138-139` `temporalCutoff` | `scaledTemporalCutoff_eq` `rfl` |
| `dilateField` :125 | `Source/ParabolicScaling.lean:21-23` | `dilateField_eq` `rfl` |
| `parabolicVelocity` :131 | `ParabolicScaling.lean:92-93` | `parabolicVelocity_eq` `rfl` |
| `scaledPacket` :140 | claimed: 3rd summand of `Source.InsertionFamily.velocity` | `scaledPacket_eq` `rfl` — **see finding 1** |
| `alpha` :148 | no single upstream | `alpha_add_one` (`simp only; ring`) |
| `Data.spatialGradient` (used) | `Data.lean:446-447` | `spatialGradient_eq` `rfl` vs new `Section4.I02.spatialGradient` |
| `Data.energyENorm` (used) | `Data.lean:437-469` | `energyENorm_eq` `rfl` |
| `Data.mixedLebesgueENorm` (used) | `Data.lean:242-254` | `mixedLebesgueENorm_le` (`iInf_le`) |

`zeroPastField` is reused from `Contracts.V1.Packet:158`, already guarded by
`Bindings.Packet.zeroPastField_eq`. `Data.forceTimeMeasure` is literally
`abbrev … := positiveTimeMeasure` (`Data.lean:118`), so `mixedLebesgueENorm_le`'s
`iInf_le` is over the right measure. `potential_formula`, `correction_formula` and
`force_formula` are `rfl` against `RadialPotential.timePotential:202` (via
`centeredPotential_eq_integral := rfl` `:177`), `CorrectionProfile.physicalCorrection:141`
(→ `LocalCutoff.localCorrection:48-51`) and `Source.correctionForce`, all opened.

## 5. Paper fidelity — findings, ranked

1. **Low — `scaledPacket_eq` is not a drift guard.** The contract docstring
   (`Correction.lean:138-139`) says `scaledPacket` "is the third summand of
   `NSFormalization.Source.InsertionFamily.velocity`", but the bridge only restates the
   contract's own right-hand side (`parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField U)`),
   so it cannot fail if `InsertionFamily.velocity` drifts. The spec review confirmed the
   identity by scratch `rfl` (probe #4), so the claim holds today; it is the one copied
   notion with no permanent cross-module guard.
2. **Low — the `P.carrier` vs `K_*` narrowing is flagged only outside the contract.**
   `carrier_subset_plateau : P.carrier ⊆ plateau` cites `03-torus.tex:181`, but the paper's
   set there is `K_*` (`03:101-102`), the enlargement containing `K` *and* the spatial
   projection of `supp F`. The narrowing is correct for I02 (nothing here mentions the
   packet force) and `ATTEMPTS.md` §6.1 flags that I03/R42 must supply the enlargement —
   but a reader of the registered `Correction.lean` alone would not learn it. Recommend
   one docstring sentence.
3. **Low — the docstring list of packet facts used is wrong.** `Correction.lean:157-160`
   names `velocity, carrier, carrier_compact, velocity_support, divergence_free` plus
   `velocity_smooth, quietTime, quiet_pos, velocity_quiet`. The binding uses `P.velocity,
   P.carrier, P.carrier_compact, P.velocity_support, P.divergence_free,
   P.velocity_extension_smooth` — the last four named are unused, and the field that
   replaced them is unnamed.
4. **Trivial — one off-by-one citation.** `eps_time` cites `03-torus.tex:104`; the
   display `2ε²<T, x₀+εK_*⊂B` is `:105` (`:104` is the opening `\[`). Every other line I
   opened is exact: `03:` 164, 178-180, 181-182, 183-187, 188-189, 190-193, 212, 220-223,
   225, 227-230, 234, 235-237, 242, 321-325, 332-333; `04:` 8, 23-29, 32, 37-38, 45, 51.
5. **Trivial — asymmetric constant hygiene.** `correctionDerivConst`/`forceDerivConst`
   carry nonnegativity fields; `energyConst` and `mixedConst` do not. Not a soundness
   hole: `ENNReal.ofReal` clamps a negative bound to `0`, which *strengthens* the claim.
6. **Trivial — `contracts.json` also rewrites a neighbouring line.** The diff re-encodes
   the committed `I01.packet` scope from `ν` to a literal `ν`. Semantically identical
   JSON, but it touches another lane's registration.

**Checked and sound (no finding).** `reference_pressure_smooth` is licensed verbatim by
`03-torus.tex:164` "Fix a reference solution `(v,π,g)` smooth on `[0,T+δ]`", opened at that
line; `Source.corrected_background` genuinely needs `DifferentiableAt ℝ (π (t,·)) x`.
`ε₀ = min 1 (min (r/(R+1)) √(δ₁/2))` with `δ₁ = min(T,δ)/4` yields `2ε² ≤ min(T,δ)/4 <
min(T,δ)`: strictly stronger than `03:212`, proof explicit at `hwindow`/`htime`. `eq:H`'s
summands appear in a different order ((w·∇)v before (v·∇)w); the sum is identical and the
docstring says so.
`correction_cancels` on all of `Ioo 0 T` (paper: the active interval) is a strengthening
carried by `scaledPacket_slice_empty`. `force_mixed_bound` is asserted for every
`q : ℝ≥0∞`, beyond the paper's `1 ≤ q ≤ ∞` — a strengthening, and provable, since
`CMN.physical_force_mixed_bound:123` is stated for all `p q` and restricting `mixedNorm`
(all of `ℝ`) to `positiveTimeMeasure` only decreases it. Both norms are canonical and
`ℝ≥0∞`-valued, so neither bound is vacuous. `reference_smooth` and
`reference_divergence_free` are global in space, stronger than Lemma 3.4's "in a spatial
ball" — but exactly Theorem 4.2's setting (`04:32`), and the module docstring declares
it. No field is `True` or an unspecified proposition.

**Spec diff** (`research/I02/Spec.lean` 81 fields → contract 73, common order preserved).
Removed: `viscosity_pos, packet, carrier, carrier_compact, packet_support,
packet_divergence_free, packet_smooth, packetQuietTime, packet_quiet_pos, packet_quiet`
(the `PacketAPI ν` parameter) and `correction_energy_memLp`. Added:
`reference_pressure_smooth, correction_slice_memLp, correction_gradient_memLp`. Exactly
`ATTEMPTS.md` §6 items 1, 3 and 5 — no undocumented change. `Ico 0 T` in
`perturbation_divergence_free` and the seven `correctionStatement` identities are present.

**Six spec-review notes.** 1 (`Ico 0 T`) applied. 2 (`correctionStatement` reflow) applied
— the `∀ τ` binder is gone with the packet parameter. 3 (five citations) applied; I
re-opened all five. 4 (`gradientNorm_eq_timeL2` naming) N/A, explained at
`ATTEMPTS.md:119-123`: neither real-valued `energyNorm` lemma is used. 5 (vacuity step)
applied as `Support.scaledPacket_slice_empty`. 6 (`LI:20` vs `:21`) trivial; the review
proposed no fix. Notes 4-6 concerned `COMPARISON.md`, left unchanged here; only 5 had
Lean substance, and it was implemented.

**Registration.** `contracts.json`: `id I02.correction`, `parent_task I02`, `version 1`,
spec/binding/test paths and `declaration BlowupDensity.Tests.checkedCorrection` all match
the files; `enabled true`. Scope excludes Theorem 4.2's lifespan and density statements —
accurate, and if anything under-claiming (`corrected_background` and
`perturbation_divergence_free` come from the insertion proof, `03:321-325, 332`).
`work_items.json` I02 lists `I02.correction`; `TASKS.md` and `tasks/I02.md` agree.

## 6. Not verified

* The mathematics of the `Paper1`/`Source` chain. I opened the *statements* of
  `CP.physical_mixed_derivative_bound:291`, `CFP.physicalForce_spatial_derivative_bound`,
  `CMN.physical_force_mixed_bound:123`, `CE.physicalCorrection_uniform_energy:54` and
  `IE.correction_gradientSquare_bound` and confirmed each matches the field it supplies;
  their proofs and the rest of the 597-module closure were not re-audited.
* Compatibility against the live `erenup/integration` tip — `c8bde6e` was used as
  instructed; the lane still needs the rebase `ATTEMPTS.md` §8 calls for.
* Cold-build cost: every Lean job replayed from cache, so 13.96 s is a no-op rebuild.
* `eq:HHs`, fractional/negative-order scaling, Theorem 4.2's conclusions — I03/R42.
