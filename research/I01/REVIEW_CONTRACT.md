# I01 contract review — `I01.packet` (lane 007, `erenup/007-I01-contract`)

**ACCEPT-WITH-NOTES.** Every gate passes; `checkedPacket` really inhabits
`PacketAPI ν` for all `ν > 0` on the three standard axioms only; all twenty
re-defined notions are the pinned upstream objects and all fourteen bridges are
`rfl`; every `PacketAPI` field matches the manuscript clause it cites. Notes are
documentation-level: one false "character-for-character" claim, eight notions with no
direct bridge, a scope sentence saying "Theorem 1.1 properties" while the file omits
that theorem's corollary, and four `REVIEW.md` notes on `COMPARISON.md` left open.
Nothing blocks I02/I03.

## 1. Gates (worktree root; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

| Command | Result |
|---|---|
| `make check` | exit 0. `check_formalization_plan --check`: 30 tasks, 2975 manifest entries, `missing_copied_imports: []`, `tracked_cache_free: true`, one pre-existing `sorry` at `Paper1/BoundaryCorollary.lean:90` (outside both contract closures). `check_contracts` ok; `test_contract_policy` 7 tests OK; `check_work_queue`: `30 work items: ownership, contract registration and task cards consistent.` |
| `make test` (`lake -d verification test`) | exit 0, 2.4s wall / 9302 jobs, fully cache-replayed. Both required lines printed: `Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only` and `Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only`. Two pre-existing warnings (`Source/PacketForceExtension.lean:44` deprecated `if_pos`; `Source/ViscosityPacket.lean:34` unused simp arg) — neither in a lane-007 file; `warningAsError` covers only `Tests`. |
| `make test-mutations` | exit 0, 9.2s. `implementation_refactor: accepted`; `admitted_proof`, `extra_axiom`, `weakened_hypothesis` each `rejected as required`; `Mutation suite passed.` |
| `check_contracts.py --base-ref erenup/integration` | exit 0, `base_compatibility_checked: true`, `registered_contracts: 2`. `I01.packet` closure = 534 modules, containing `Contracts.V1.Packet`, `Bindings.Packet`, `Tests.Packet`, `TestSupport.Axioms`, the three `Section4.I01.*`; no `Paper1.BoundaryCorollary`, no `Citations.*`. |
| `build_changed_lean.py --base-ref … --dry-run` | exit 0, exactly the six expected: `Bindings.Packet, Contracts.V1.Packet, NSFormalization.Section4.I01.{Energy,Extension,Quiet}, Tests.Packet`. |
| same, no `--dry-run` | exit 0, `Build completed successfully (9298 jobs)`, **1.99s wall / 2.69s user** — replayed from cache, not a cold build. |

`Contracts.V1.Packet` imports only `Mathlib.*` (8), as `check_contracts.py` enforces
alongside `axiom|sorry|admit`-freedom under `Contracts.`.

## 2. Axioms

Scratch `/tmp/I01_axioms_check.lean` (`import Tests.Packet`, `import Bindings.Packet`),
`lake env lean` from `verification/`, exit 0, then deleted. Each of
`Tests.checkedPacket`, `Section4.I01.{exists_l2_isLUB, exists_quiet_of_compactPositiveTimeSupport,
exists_packet_quiet, extension_smoothOn, extension_navierStokes, extension_divergence_free}`,
`Bindings.packet` and `Bindings.packetFamily` printed exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool`.
`TestSupport.checkAxioms` uses `Lean.collectAxioms`, the real transitive set.

**Hygiene.** `grep -rnE "sorry|axiom|admit|native_decide|unsafe"` over
`Contracts/V1/Packet.lean`, `Bindings/Packet.lean`, `Tests/Packet.lean`,
`formalization/NSFormalization/Section4/I01/` → **no matches at all**, comments included.

## 3. Re-definition ↔ upstream ↔ bridge

`PS0` = `vendor/.../NavierStokes/ProblemStatement.lean`; `R3PS` = `.../R3/ProblemStatement.lean`;
`R3CE` = `.../R3/CompactEnergy.lean`; `PS` = `formalization/NSFormalization/Source/PacketScaling.lean`.
All bridges are `:= rfl` (definitional, no rewriting).

| Contract notion | Upstream | Same object? | Bridge |
|---|---|---|---|
| `Space` | PS0:30 | verbatim | `space_eq` |
| `SpaceTime`, `VelocityField`, `PressureField` | PS0:33,35,36 | verbatim | — (reducible `abbrev`s; defeq forced by the other bridges typechecking) |
| `coordinateVector` | PS0:39 | verbatim | `coordinateVector_eq` |
| `preSingularDomain` = `Ico 0 1 ×ˢ univ` | PS0:42 | verbatim | `preSingularDomain_eq` |
| `positiveTimeDomain` = `Ioi 0 ×ˢ univ` | R3PS:53 | verbatim | `positiveTimeDomain_eq` |
| `temporalDerivative`, `advection`, `pressureGradient`, `spatialLaplacian` | PS0:55,63,71,76 | verbatim | — (only via the composite `navierStokesResidual_eq`) |
| `spatialDerivative` | PS0:59 | verbatim | — (only via `spatialDivergence_eq`) |
| `spatialDivergence` | PS0:67 | verbatim | `spatialDivergence_eq` |
| `navierStokesResidual ν` | R3PS:57-62 | verbatim; `ν •` on the Laplacian only | `navierStokesResidual_eq`, `…_eq_source` |
| `CompactPositiveTimeSupport` | R3PS:66 | verbatim | `compactPositiveTimeSupport_eq` |
| `SquareIntegrableAtTime` | R3PS:71 | verbatim, `volume : Measure Space` | `squareIntegrableAtTime_eq` |
| `SpeedUnboundedAtOne` | PS0:94 | verbatim | `speedUnboundedAtOne_eq` |
| `l2Sq` | R3CE:190 | verbatim | `l2Sq_eq` |
| `dissipation` | R3CE:195 | **defeq, not verbatim**: upstream `spatialPartial i (fun y => u (t,y)) x`; contract inlines `fderiv ℝ (fun y => u (t,y)) x (coordinateVector i)`, which is exactly how `spatialPartial` unfolds (`PeriodicIntegration.lean:43-45`) | `dissipation_eq` |
| `zeroPastField` | PS:243 | verbatim | `zeroPastField_eq`, `zeroPastPressure_eq` |

Measure (`volume` on `EuclideanSpace ℝ (Fin 3)`), viscosity placement, domains and
quantifiers agree throughout. Eight notions carry no direct bridge — see finding 2.

## 4. Contract vs paper

Every doc-comment citation was opened and resolves (`01-introduction.tex:4-7, 15-34,
61-66`; `02-preliminaries.tex:127-133, 150, 152`; `03-torus.tex:108-109, 122-126,
141`; `04-whole-space.tex:31-43`). Confirmed: one compact `K` for both supports
(`01:24-25`); `u(·,0)=0`, `∇·u=0` (`01:22`); the equation on the open `Ioo 0 1`
(`01:20-23`, half-domain convention); `sup‖u‖_{L²}<∞` and `limsup‖u‖_∞=∞`
(`01:27-28`); `M := sup_{0≤t<1}‖U(t)‖₂` as `IsLUB ((sqrt ∘ l2Sq) '' Ico 0 1)`
(`02:130` — LUB not a bound, because `eq:packetEscale` is an equality);
`D := ‖∇U‖_{L²((0,1)×R³)}` as `sqrt (∫_{Ioo 0 1} dissipation)`, no `ν` factor
(`02:131`); `dissipation_integrable` = the monotone-convergence step (`02:150`);
the **closed** quiet interval `Icc 0 τ` for `F`, `U`, `P` (`02:152`, "`F=0` on
`[0,τ]`"); both zero extensions smooth on `Iio 1 ×ˢ univ` (`02:133`, `03:141`);
`force_zero_nonpos` = clarification `C1` as inserted at `03:108-109`. Theorem 1.1's
"Consequently …" clause is excluded, and the module docstring says so.

`PacketAPI` vs the accepted draft `research/I01/Spec.lean`, doc comments stripped:
**45 field lines each, exactly three differ** — `force_quiet`, `velocity_quiet`,
`pressure_quiet`, each `Ioo (0:ℝ) quietTime` → `Icc (0:ℝ) quietTime`. Everything
else in the diff is prose, `ℝ³`→`R³`, and the self-contained definition block
replacing the `open …` lines.

Findings, ranked:

1. **minor, docstring false.** `Packet.lean:34-36` claims every definition is
   "character-for-character the pinned upstream one" — true for nineteen of
   twenty, false for `dissipation`. The `rfl` bridge carries the real content.
2. **minor, drift-guard gap.** `SpaceTime`, `VelocityField`, `PressureField`,
   `temporalDerivative`, `spatialDerivative`, `advection`, `pressureGradient`,
   `spatialLaplacian` have no direct bridge. Four operators are guarded only
   through the composite `navierStokesResidual_eq`, which would survive two
   compensating upstream edits; `spatialDerivative` only through
   `spatialDivergence_eq`. Five one-line `rfl` theorems would close it.
3. **minor, scope wording.** `contracts.json` says "the Theorem 1.1 properties"
   while the contract deliberately omits Theorem 1.1's nonexistence corollary.
   Suggest "the Theorem 1.1 construction properties (not its nonexistence
   corollary)". The rest does **not** overclaim: it states plainly "Not the local
   insertion theorem and not any density statement."
4. **cosmetic.** `preSingularDomain` / `positiveTimeDomain` doc comments write
   `R^3 x [0,1)` and `R^3 x (0,∞)` while the terms are time-first (`Ico 0 1 ×ˢ univ`);
   `velocity_extension_smooth`'s comment uses the opposite order (`(-∞,1) × R³`).
5. **cosmetic.** The commit message claims "collaboration: … Attempts appended";
   nothing of the sort is in the diff and `experiments/tasks.py` has no attempts field.

## 5. `REVIEW.md`'s eight notes

* **1, 2, 7, 8** (`COMPARISON.md`: `energy_isLUB` and `pressure_support` rows, two
  off-by-one ranges, follow-up A) — **not applied, not marked N/A.** `COMPARISON.md`
  is untouched. None affects `Packet.lean`, the binding or the registry, so they are
  genuinely out of scope at contract level, but they remain open.
* **3** (quiet interval) — **applied, and more strongly than suggested.** `REVIEW.md`
  proposed keeping `Ioo` plus a doc note; the lane strengthened all three fields to
  `Icc 0 τ`, matching `02:152` literally. `Extension.lean` re-weakens `Icc`→`Ioo`
  (`fun t ht x => hq t ⟨ht.1.le, ht.2.le⟩ x`) at the two `PacketScaling` call sites,
  so the `Ioo`-germ consumers still apply. An improvement.
* **4** (`dissipation_eq` doc) — **applied verbatim**, new clause on gradient
  integrability following from `velocity_smooth` + `velocity_support`.
* **5** (`quiet_lt_one` redundant) — N/A, `REVIEW.md` said keep; kept.
* **6** (`PacketFamily` over all `ν`) — note only; `Bindings.packetFamily` axiom-clean.

## 6. Registry and work queue

`contracts.json`: `id I01.packet`, `parent_task I01` (a real `tasks.json` node),
`version 1`, `specification verification/Contracts/V1/Packet.lean` (has the required
`/V1/`), `binding_module Bindings.Packet`, `test_module Tests.Packet`, `declaration
BlowupDensity.Tests.checkedPacket`, `enabled true` — all present, all in the closure;
the pre-existing `R41.threshold_arithmetic` entry is byte-identical to base.
Scope accurate except finding 3. `work_items.json` I01 lists `["I01.packet"]`,
still `in-progress`/`erenup`. I re-ran `experiments/tasks.py render` in a throwaway
copy at `/tmp/i01render` (no repository file touched): the regenerated `TASKS.md`
and **all 30** `collaboration/tasks/*.md` are byte-identical to the committed ones.

## 7. Not verified

* **Cold-build time.** Both Lean runs replayed an existing `.lake` cache (~2s wall);
  no cache was cleared, so no from-scratch build was measured.
* **The source packet's mathematics.** `Bindings.packet` demonstrably inhabits
  `PacketAPI` from `Source.selected_packet_every_viscosity` on standard axioms; that
  theorem's ~530-module closure and the `UniformFiniteEnergy` witness `Energy.lean`
  consumes were not re-audited.
* `make paper` not run; `COMPARISON.md` not re-reviewed beyond the four notes above.

No repository file was modified and no git write command was run; this is the only output.
