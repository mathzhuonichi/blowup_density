# Lane 021 / I03.scaling — contract review

Reviewer pass on `erenup/021-I03-contract` @ `21ef789` (rebased on `erenup/integration`):
gates, transitive axioms, self-contained definitions vs sources, and fidelity to Theorem 4.2
(`thm:Rinsert`) and Proposition 3.3 (`prop:scaling`).

## Verdict

**ACCEPT-WITH-NOTES.** All six gates green; all 115 relevant declarations carry exactly the
three standard axioms; each of the three re-defined notions has a `rfl` bridge; every
`ScalingAPI` field matches its manuscript display in object, exponent and range, with
equalities where the paper has equalities. One medium note concerns the hand-off to `R42`
(§5.1, item 4); two are cosmetic. Nothing was fixed.

## 1. Gates (all from the worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `make check` | pass — plan check (only pre-existing `sorry` is `Paper1/BoundaryCorollary.lean:90`, not in any closure), `check_contracts` OK, 13 policy tests OK, 30 work items consistent |
| `make test` | pass — `checkedThresholds`, `checkedPacket`, `checkedCorrection`, `checkedScaling` each print `checked; standard logical axioms only`; 2.9 s user (warm replay) |
| `make test-mutations` | pass — `implementation_refactor: accepted`; `admitted_proof`, `extra_axiom`, `weakened_hypothesis` each `rejected as required` |
| `check_contracts.py --base-ref erenup/integration` | pass — `registered_contracts: 4`, `base_compatibility_checked: true` |
| `build_changed_lean.py --base-ref … --dry-run` | exactly the expected 8 modules: `Bindings.{Scaling,ScalingEnergy,ScalingNorms}`, `Contracts.V1.Scaling`, `NSFormalization.Section4.I03.{Angular,Energy,Mixed}`, `Tests.Scaling` |
| `build_changed_lean.py --base-ref …` (real) | `Build completed successfully (9385 jobs)`, exit 0, 2.25 s wall (closure already built) |

`I03.scaling` closure = 621 modules; no `Citations.*`, no `Paper1.BoundaryCorollary`, no
HeliCorgi `Formal.*`.

## 2. Axioms

Scratch file `/tmp/r021_axioms2.lean` (`import Tests.Scaling` + the three `Section4/I03`
modules), run with `lake env lean` from `verification/`, then deleted. **115** `#print axioms`
targets — **no sampling**: `BlowupDensity.Tests.checkedScaling`,
`Contracts.V1.scalingStatement`, all **75** declarations of
`Bindings/{Scaling,ScalingEnergy,ScalingNorms}.lean`, and all **38** of
`Section4/I03/{Angular,Energy,Mixed}.lean`. Every one printed exactly `[propext, Classical.choice, Quot.sound]`; zero other output lines.
`Tests/Scaling.lean` itself runs `TestSupport.checkAxioms`, which inspects
`Lean.collectAxioms` rather than printed text.

## 3. Hygiene

Grep over the eight new Lean files: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`TODO`/`FIXME`/`XXX`/`HACK` anywhere, in comments or code. `Contracts/V1/Scaling.lean` imports
only `Contracts.V1.Correction` and `Contracts.V1.Thresholds` — inside the contract import rule
without touching the canonical-module whitelist. Four `set_option linter.unusedVariables
false in` sites (`Mixed.lean:94`, `Energy.lean:227,333`, `ScalingEnergy.lean:262`), each with a
docstring saying which hypothesis is kept only for signature uniformity. Benign.

## 4. Self-contained definitions ↔ source ↔ bridge

`Contracts/V1/Scaling.lean` re-defines exactly three notions. All three are bridged by `rfl`;
**none is missing a bridge**.

| contract notion | source | bridge (`Bindings/Scaling.lean`) |
|---|---|---|
| `scaledPressure` (`:110`) = `dilateField (ε⁻¹)² (ε⁻¹)² ε⁻¹ (T-ε²) x₀ ∘ zeroPastField` | `Source.parabolicPressure` (`ParabolicScaling.lean:98`) applied to `zeroPastField P` | `scaledPressure_eq := rfl` (`:38`) |
| `scaledForce` (`:120`) = `dilateField (ε⁻¹)³ (ε⁻¹)² ε⁻¹ (T-ε²) x₀` | `Source.parabolicForce` (`ParabolicScaling.lean:100`) | `scaledForce_eq := rfl` (`:44`) |
| `SpeedUnboundedAt` (`:131`) | `Source.PacketScaling.SpeedUnboundedAt` (`PacketScaling.lean:22`) — character for character | `speedUnboundedAt_eq := rfl` (`:49`), plus `speedUnboundedAt_one` to `Contracts.V1.SpeedUnboundedAtOne` (`:53`) |

With `k = ε⁻¹`, `dilateField a c d t₀ x₀ f z = a • f (c(z₁-t₀), d•(z₂-x₀))` reproduces the
amplitudes `ε^{-2}`, `ε^{-3}` and the parabolic time factor of `eq:scaling`
(`03-torus.tex:113-118`) exactly, with `t_ε = T - ε²`. Everything else is **reused, not copied**: `scaledPacket`, `alpha`, `dilateField`,
`navierStokesResidual`, `zeroPastField` from `Contracts.V1.{Correction,Packet}` (bridged in
`Bindings/Correction.lean` by I02; `navierStokesResidual_eq` re-recorded here at `:58`), all
norms from `Contracts.V1.Data`, all exponents from `ThresholdAPI.exponent`. The projections
`ScalingAPI.{U,P,F,perturbation,forceDifference}` are new abbreviations of already-bridged
objects, not re-definitions; `forceDifference` additionally has `forceDifference_eq` (`:442`).

**Structural claim confirmed.** `Bindings.correction_eq` (`:138`) proves
`C.correction ε = physicalCorrection C.v C.x₀ C.T C.θ C.η ε` by `funext`, `C.correction_formula`,
`potential_eq` (itself `C.potential_formula`), `rfl`; `Bindings.forceCorrection_eq` (`:147`)
proves `C.forceCorrection ε = Source.correctionForce ν C.v (physicalCorrection …)` by `funext`,
`C.force_formula`, `correction_eq`, `rfl`. Both follow from `CorrectionAPI`'s *formula* fields
(`Correction.lean:337`, `:415`) for an arbitrary inhabitant — no new hypothesis, no re-running
of I02's construction — and this is what lets `scalingStatement` assert `A.correction = C`.

## 5. Fidelity to Theorem 4.2 and Proposition 3.3

31 fields, all checked. Exponents are always `thresholds.exponent q.toReal s = 2/q - 3/2 - s`
(`Thresholds.lean:12`); at `q = ⊤`, `q.toReal = 0` and Lean's `2/0 = 0` gives the correct
`β(∞,s) = -3/2 - s`.

Matches confirmed: `scaledEquation`/`scaledDivergenceFree`/`scaledBlowup` ↔ `prop:scaling`
(`03-torus.tex:123,141`), same viscosity, whole inactive past covered;
`packetEnergyIdentity`/`packetDissipationIdentity` ↔ `eq:packetEscale` (`:125-128`) as
**equalities** against `P.energyBound` (the `IsLUB` of `PacketAPI.energy_isLUB`) and
`P.dissipationBound`; `packetMixedScaling` ↔ `eq:packetFscale` (`:129-131`) as an **equality**
with `alpha p q = -3 + 3/p + 2/q`, endpoints included (`p.toReal = q.toReal = 0`);
`perturbationEnergyBound` ↔ `eq:REclose` (`04-whole-space.tex:39-41`) with the exact shape
`(M+D)ε^{1/2} + Cε^{3/2}`; `packetPositiveScaling`/`correctionPositiveScaling` ↔
`eq:RpositiveScale` (`:64-69`), two-term shape `ε^{β(q,0)} + ε^{β(q,s)}` and the `+1` on the
correction line, range `0 ≤ s ≤ 1`; `packetNegativeScaling`/`correctionNegativeScaling` ↔
`eq:RnegativeScale` (`:72-76`) on `-3/2 < s < 0`, correction again `β(q,s)+1`;
`forceConvergence` ↔ the theorem's force clause (`:42-43`) for `q ∈ {1,2}`, `s < 2/q - 3/2`,
on `g_ε - g = H_ε + F_ε`, along `𝓝[>] 0`, both `q` discharged by
`InsertionFamily.force_L1_tendsto_zero` / `force_L2_tendsto_zero`.

**The `L^∞L²` equality proof exists and is real.** `Section4/I03/Energy.lean:487`
`energyEssSup_scaled_eq := le_antisymm energyEssSup_scaled_le le_energyEssSup_scaled`; the `≥`
half (`:398`) genuinely consumes `IsLUB` as a *least* bound, turning a near-maximal reference
time into a positive-measure set via `continuousAt_l2Sq_zeroPastField` (`:350`) and
`le_essSup_of_le_on_pos_measure` (`:83`). Bridged to `ε^{1/2}` by `sqrt_mul_eq_rpow_half`.

**Intermediate index.** `forceLowOrderBound` produces `r` with `-3/2 < r < 0`, `s ≤ r`,
`r < β(q,0)` — the last is exactly `β(q,r) > 0`, so the bound converges. For `q = 2` this is
the paper's `r ∈ (-3/2,-1/2)`; for `q = 1` the paper uses `r = 0` and the contract uses a
negative `r` (via `ThresholdAPI.negativeIndex`, or `r := s` when `-3/2 < s`), which stays inside
the range where `packetNegativeScaling` holds and yields *faster* decay. Faithful.

### 5.1 The four listed paper–Lean differences

1. **`ε₀ = min C.ε₀ √(min(T,δ)/8)`** (`scalingThreshold`, `window = min(T,δ)/4`). Harmless:
   the manuscript says only "for all sufficiently small `ε`", and `eps_le_correction` records
   the direction. Needed for `temporalCutoff_zero_outside`, not for `eps_time` (which `I02`
   already gives). `eps_space` is inherited unchanged from `C`.
2. **`lowOrderConst : ℝ≥0∞ → ℝ → ℝ → ℝ`.** Verified as stated: `sobolev_bound_of_cycles`
   (`ScalingNorms.lean:224`) emits `frequencyUnit ^ |s| = (2π)^{|s|}`
   (`Source/FourierConvention.lean:15`) at the *measured* order `s`, unbounded as `s → -∞`, so
   it cannot be absorbed into a constant indexed by `r`. Harmless for `R42`: the paper's
   `C_{q,s}` are unspecified, and `forceConvergence` carries no constant at all.
3. **`correctionEnergyConst := max C.energyConst 0`**, pinned back to I02's bound by
   `correctionEnergyBound`. Harmless and in fact necessary — `CorrectionAPI` has no sign field,
   and a negative constant would make `eq:REclose` false.
4. **`force_carrier_subset` (the `K → K_*` premise) — MEDIUM, the one note for `R42`.**
   The binding stores `hFR` verbatim (`Bindings/Scaling.lean:717`) and **no `ScalingAPI`
   conclusion depends on it**: it is a pure pass-through. It is also not dischargeable from the
   registered contracts. `PacketAPI.force_support` is only
   `CompactPositiveTimeSupport force` (`Packet.lean:214`) — unrelated to `carrier`; and
   `correctionStatement` (`Correction.lean:542`) existentially binds `θRadius`, whose witness
   `Bindings.correction` fixes as `R = Rb + 1` from `P.carrier` alone
   (`Bindings/Correction.lean:174-178`). So `R42`, which can only obtain its `C` through
   `checkedCorrection`, gets a `θRadius` with no relation to `supp F` and cannot prove the
   premise. Not a soundness problem — `03-torus.tex:101-102` makes it true by construction —
   and cheap to resolve (drop the inert field, or an `I02` V2 letting the caller pin `θRadius`
   above a given compact set). `ATTEMPTS.md` §2 diagnoses the cause correctly but does not
   record that the obligation is currently unmet downstream.

Also checked: `carrier_subset` is **derived** in the binding (`carrier_subset_ball`, from
`carrier_subset_plateau` + `theta_one` + `theta_support`), so it is not a caller burden.

## 6. The homogeneous gap

`HomogeneousScalingAPI` (`Contracts/V1/Scaling.lean:509`) is **not** in `contracts.json` — the
registry holds exactly four entries and the file is reachable only through the `Contracts` lib.
Its docstring states the gap correctly and substantively: `Data.forceHomogeneousENorm` is an
infimum over `Data.IsHomogeneousPath`/`IsHomogeneousDatum` witnesses, nothing in the project
constructs one, `⨅ ∅ = ⊤` in `ℝ≥0∞`, hence both fields are unprovable; Theorem 4.2 does not
block on it (all clauses of `04-whole-space.tex:42` are inhomogeneous), Proposition 4.6's
`L²(0,∞;Ḣ^{-1})` clause blocks on it and nothing else. **Cosmetic (LOW):** the docstring does
not use the token `U7c`; it defers to `research/I03/{COMPARISON,ATTEMPTS}.md`, which do name it.

## 7. Registry, ledger, cards

`contracts.json` entry: id `I03.scaling`, parent `I03`, version 1, spec/binding/test/declaration
paths all correct, `enabled: true`. **Cosmetic (LOW):** the `scope` string names the scaling
identities, the inhomogeneous `L^q_tH^s_x` bounds and the force-convergence clause, and the two
exclusions, but not the Prop 3.3 transport fields or `eq:REclose`, which are also in the record.
`work_items.json` I03 lists `I03.scaling`; `TASKS.md` and `tasks/I03.md` agree.
`python3 experiments/tasks.py render` leaves the tree clean — cards regenerate byte-identically.

## 8. `research/I03/ATTEMPTS.md`

Accurate. Spot-verified: §1's formula-field discovery and the `window`/`ε₀` consequence; §2's
`max C.energyConst 0`, derived `carrier_subset`, and the `scalingStatement` strengthening; §3's
`(2π)^{|s|}` factor and the third index; §4's homogeneous status and the `⨅ ∅ = ⊤` argument;
§5.1's `IsLUB` claim, §5.2's `eq:REclose` shape, §5.3's attained infimum
(`mixedLebesgueENorm_eq`), §5.4's threshold, §5.6's `q = ⊤`. The four failed approaches are
stated plainly, including the correct reason why abstract-`CorrectionAPI` monotonicity runs the
wrong way. The one omission is the downstream consequence flagged in §5.1 above.
