# REPORT_430 — T24 Ua9 assembly + `T04.affine_variation` registration (Opus; transcribed by lead from the agent message, report-file guard)

Everything is committed and green. Here is the report (I did not create `research/T24/REPORT_430.md` — my operating instructions forbid writing report/summary `.md` files, so the full report is below; `research/T24/ATTEMPTS_UA9.md` and the `T24_SPLIT.md` status entry, which are lab-record files required by CLAUDE.md rule 4, were written).

## 1. What was proved

Proposition `prop:affine` (`paper/sections/03-torus.tex:668-696`), the whole-space infinite-dimensional affine variations of the Theorem 1.1 packet, is now a closed, registered theorem: for every viscosity, **every** packet satisfying the registered `PacketAPI` (not only the selected witness), and every cylinder `ball c r × (τ₀,τ₁)` with `0 < r` and `0 < τ₀ < τ₁ < 1`, all thirteen clauses hold — positive radius, interior window, smoothness and compact positive-time support of the six-term corrected force, the divergence and momentum equations of `U+b` with the unchanged pressure, zero initial data, agreement with `U` past `τ₁`, unbounded speed at `t=1`, finite `E₁` energy, an ℝ-linearly independent admissible sequence, injectivity of `b ↦ U+b`, and the two `C^m`-seminorm non-isolation limits.

One genuinely new piece of mathematics was needed, the gap lane 407 left open: `Contracts.V1.PacketAPI` has no `energyENorm 1 velocity < ⊤` field, while `energy_finite` consumes it. It is now derived from the four clauses the packet does carry — `square_integrable` + `energy_isLUB` for the `L^∞_t L²_x` half (via `I02.eLpNorm_two_eq_ofReal_sqrt` and `essSup_le_of_ae_le`), and `velocity_smooth` + `carrier_compact` + `velocity_support` + `dissipation_integrable` for the `L²_t Ḣ¹_x` half (via the *slice* form `I03.eLpNorm_spatialGradient_sq_slice` and `ofReal_integral_eq_lintegral_ofReal`). Everything else is assembly: each of the thirteen fields is one application of a lane 392/398/402/403/407/414/417/424 theorem.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/430-T24-Ua9-affine-registration/formalization/NSFormalization/Section3/T24/AffineAssembly.lean` — canonical layer: `energyEssSup_le_of_isLUB`, `energyGradient_lt_top_of_dissipation`, `energyENorm_lt_top_of_packet`; `AffineRawData` (the eight raw packet clauses the units consume); `AffineVariationCanonical` (the thirteen Spec fields over raw `U P F`); `affineVariationCanonical` (the assembly).
- `/data_8T/ping/blowup_density/.claude/worktrees/430-T24-Ua9-affine-registration/verification/Contracts/V1/AffineVariation.lean` — `AffineVariationAPI` and `affineVariationStatement`, plus the seven unregistered notions (`affineCylinder`, `AffineAdmissible`, `crossAdvection`, `affineVelocity`, `affinePressure`, `affineForce`, `ckSeminormE`). Body copied token-for-token from `research/T24/Spec.lean:958-1121`; verified by `diff` (`VERBATIM OK`), only the namespace differs. Imports `Contracts.V1.Data` and `Contracts.V1.Packet` only.
- `/data_8T/ping/blowup_density/.claude/worktrees/430-T24-Ua9-affine-registration/verification/Bindings/AffineVariation.lean` — seven whole-function `rfl` drift guards (one per restated definition, incl. `ckSeminormE = affineCkSeminorm`), `packetRawData`, `affineVariation` (any `PacketAPI`), `affineVariationPacket` (at `Bindings.packet ν hν`), `affineVariationStatement_holds`.
- `/data_8T/ping/blowup_density/.claude/worktrees/430-T24-Ua9-affine-registration/verification/Tests/AffineVariation.lean` — `checkedAffineVariation`, `checkedAffineVariationStatement`, both with `run_cmd TestSupport.checkAxioms`; three conformance examples (`momentum`, `energy_finite`, `infinite_dimensional`); non-vacuity at `b = 0` and at the nonzero `AffineWitness.curlBump` on `ball 0 1 × (1/4,3/4)`, plus an example pinning `energyENorm 1 (packet ν hν).velocity < ⊤`.
- Registry: `T04.affine_variation` v1 appended as a clean list element (parent task `T04`, per the T24 work item, not `T24.*`); `collaboration/work_items.json` T24 → in-progress/erenup with that contract; task cards regenerated.
- Records: `research/T24/axioms_ua9.lean` (20 declarations), `research/T24/ATTEMPTS_UA9.md`, Ua9 marked DONE in `research/T24/T24_SPLIT.md` §1 and §2.
- Two commits on `erenup/430-T24-Ua9-affine-registration`: `bb1e198d` (claim) and `ac2de5c5` (work). No push, merge or rebase. No existing module touched (`git diff --stat` vs branch point: 11 files, 4 new Lean files + 2 records + registry/ledger).

## 3. Gap

- Only T24a is registered. T24b (`prop:multiple`, 30 fields, T15-gated) and T24c (`prop:conservative`, Uc3 assembly) remain separate contracts.
- `AffineRawData.energy_finite` is still *stated* as a clause of the raw bundle; a canonical module may not mention `PacketAPI`, so the derivation and its use meet only in `Bindings.packetRawData`.
- Non-isolation is the reconciled ℝ≥0∞-valued `ckSeminormE` on `tsupport b`; no real-valued `C^m` seminorm is claimed.
- **For the lead:** `check_contracts.py --base-ref origin/erenup/integration-section3` **fails on this branch for a reason unrelated to the lane** — the remote base has moved 22 commits ahead of the branch point (lane 427 added `Contracts/V1/MeanZeroCalculus.lean`), and `check_compatibility` asserts every base specification exists in the working tree. Run it (and `scripts/gates.sh`, via `BASE_REF`) against the branch point `4e8a840a` = `git merge-base HEAD origin/erenup/integration-section3`. Merging the base in was not an option under the brief. The registry append is the last list element, so it will conflict textually with lanes 423/427 doing the same; the addition itself is one self-contained element. Base now has 43 contracts, so after merging this lane it is 44 (45 once 423 lands).

## 4. Commands run and results

```
lake -d verification build NSFormalization.Section3.T24.AffineAssembly Contracts.V1.AffineVariation \
     Bindings.AffineVariation Tests.AffineVariation
→ info: Tests/AffineVariation.lean:34:0: Contract BlowupDensity.Tests.checkedAffineVariation: checked; standard logical axioms only
  info: Tests/AffineVariation.lean:41:0: Contract BlowupDensity.Tests.checkedAffineVariationStatement: checked; standard logical axioms only
  Build completed successfully (9372 jobs).

BASE_REF=4e8a840a scripts/gates.sh NSFormalization.Section3.T24.AffineAssembly Contracts.V1.AffineVariation \
     Bindings.AffineVariation Tests.AffineVariation
→ == make check … == make test (all 43 contracts "checked; standard logical axioms only", incl. both new lines)
  == make test-mutations: extra_axiom: rejected as required / weakened_hypothesis: rejected as required /
     Mutation suite passed.
  == check_contracts: "base_compatibility_checked": true   == gates OK

python3 experiments/check_contracts.py --base-ref 4e8a840a   # = merge-base with origin/erenup/integration-section3
→ exit 0; registered_contracts: 43 (= base 42 + 1); base_compatibility_checked: True
   (against origin/erenup/integration-section3 directly: AssertionError "Removed stable specification:
    verification/Contracts/V1/MeanZeroCalculus.lean" — the moved base, see gap above)

make check → check_formalization_plan / check_contracts / 13 policy tests OK / 45 work items consistent

cd verification && lake env lean ../research/T24/axioms_ua9.lean
→ all 20 declarations print [propext, Classical.choice, Quot.sound]

git diff --stat 4e8a840a -- verification/contracts.json → 1 file changed, 11 insertions(+)
diff <(sed -n '958,1121p' research/T24/Spec.lean) <(sed -n '46,209p' verification/Contracts/V1/AffineVariation.lean) → VERBATIM OK
```

Failed approaches, both recorded in `ATTEMPTS_UA9.md`: (a) `def` for the `Prop`-valued API instances tripped `linter.defProp` — switched both to `theorem` (lane 423's `def` precedent does not carry over, its API is `Type`-valued); (b) the base-ref drift above. The four Lean files themselves compiled on the first attempt, with no `sorry`, no `set_option`, and no conversion lemma — the contract/canonical defeq is transparent to structure-instance elaboration.
