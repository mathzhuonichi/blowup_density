# T24a Ua9 — canonical assembly + registration of `T04.affine_variation` — attempts log (lane 430)

Target: assemble the thirteen fields of `research/T24/Spec.lean:1010-1116`
(`AffineVariationAPI`) plus `affineVariationStatement:1117` from the eight T24a
unit modules, register them as the versioned contract `T04.affine_variation`.

Files: `formalization/NSFormalization/Section3/T24/AffineAssembly.lean`,
`verification/Contracts/V1/AffineVariation.lean`,
`verification/Bindings/AffineVariation.lean`,
`verification/Tests/AffineVariation.lean`,
audit `research/T24/axioms_ua9.lean`.

## The one piece of real mathematics: `‖U‖_{E_1} < ∞`

Lane 407 (`ATTEMPTS_UA6.md`, "Open gap (not Ua6)") left exactly one clause of
the assembly unproved: `Contracts.V1.PacketAPI` carries no `energyENorm 1
velocity < ⊤` field, while `energy_finite` consumes it. Closed here, in the
**canonical** layer rather than in the binding (both were allowed; the canonical
layer keeps the binding to `rfl` bridges and record transport, and the clause is
a statement about raw fields only):

- `energyEssSup_le_of_isLUB` (hyps `square_integrable`, `energy_isLUB`):
  `I02.eLpNorm_two_eq_ofReal_sqrt` turns each presingular slice `eLpNorm` into
  `ofReal (√(l2Sq U t))` — the integrability hypothesis is exactly the packet's
  `square_integrable`, so there is no totalization gap — and `energy_isLUB.1`
  bounds it by `ofReal M`. `essSup_le_of_ae_le` over
  `volume.restrict (Ioo 0 1)`, the a.e. statement supplied by
  `self_mem_ae_restrict measurableSet_Ioo` (`Ioo 0 1 ⊆ Ico 0 1`).
- `energyGradient_lt_top_of_dissipation` (hyps `velocity_smooth`,
  `carrier_compact`, `velocity_support`, `dissipation_integrable`):
  `I03.eLpNorm_spatialGradient_sq_slice` — the *slice* form, because `U` is not
  globally smooth and not globally compactly supported — identifies the squared
  gradient `eLpNorm` with `ofReal (dissipation U t)` at each `t ∈ Ioo 0 1`; its
  two hypotheses are the slice smoothness `hsmooth.comp_contDiff
  (contDiff_const.prodMk contDiff_id)` (the `AffineDivergence` idiom) and
  `hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t _)`. Then
  `setLIntegral_congr_fun measurableSet_Ioo` + `ofReal_integral_eq_lintegral_ofReal`
  turn the outer `∫⁻` into `ofReal (∫ t in Ioo 0 1, dissipation U t)`, and
  `ENNReal.rpow_lt_top_of_nonneg` survives the `^(2⁻¹)`.

This is the route `ATTEMPTS_UA6.md` sketched; no step of it needed a new lemma.
Everything else in the lane is bookkeeping.

## Design decisions (and the alternatives rejected)

1. **Two structures, not one.** `AffineRawData` bundles the eight raw clauses
   the units actually consume; `AffineVariationCanonical` restates the thirteen
   Spec fields over raw `U P F`. Rejected: putting the parameter hypotheses
   (`0 < r`, `0 < τ₀ < τ₁ < 1`) into `AffineRawData` — they are *cylinder*
   parameters of `affineVariationStatement`, not packet clauses, and lanes
   403/414/424 already carry them as explicit arguments; keeping them separate
   keeps `AffineRawData` reusable for a different cylinder.
2. **The binding proves the statement for an arbitrary `P : PacketAPI ν`,** not
   only for `Bindings.packet ν hν`. `affineVariationStatement:1117` quantifies
   over every packet, and every clause the assembly uses is a `PacketAPI` field,
   so the general form costs nothing; `affineVariationPacket` is the
   specialization at the registered `I01.packet` witness, and
   `Tests.checkedAffineVariation` is stated at that witness.
3. **No new probe file.** The eight unit probes
   (`research/T24/probes/affine_*_closes.lean`) already discharge each field on
   `Bindings.packet ν hν`; Ua9's job is the *record*, and
   `verification/Tests/AffineVariation.lean` is the registered-vocabulary
   version of those probes (three field-shape conformance examples, the
   `b = 0` instance, the nonzero `AffineWitness.curlBump` instance).
4. **`energyENorm 1 velocity < ⊤` also appears as a test example.** At `b = 0`
   the `energy_finite` field collapses to the packet's own `E_1` bound, which
   makes the new derivation visible at the contract level and shows the field is
   not vacuous.

## What did not work / cost time

1. **`def` for a `Prop`-valued API.** `AffineVariationAPI` is a `structure … :
   Prop`, so `def affineVariation … : AffineVariationAPI …` triggers
   `linter.defProp` ("Definition … is a proposition; use `theorem`"). Harmless
   in `Bindings/` but fatal under `Tests`' `warningAsError = true` if it ever
   moved there. Both instances are `theorem`s. (Lane 423's `boundedDomainNorm`
   is a `def` because its API is `Type`-valued — the precedent does not carry
   over.)
2. **`check_contracts.py --base-ref origin/erenup/integration-section3` fails on
   this branch, for a reason unrelated to the lane**: the remote base moved 22
   commits ahead of this worktree's branch point (lane 427 registered
   `Contracts/V1/MeanZeroCalculus.lean` in the meantime), and
   `check_compatibility` asserts every specification present in the *base* is
   present in the working tree. Run it against the branch point instead
   (`--base-ref 4e8a840a`, equivalently `git merge-base HEAD
   origin/erenup/integration-section3`): exit 0, `registered_contracts` 43 =
   42 + 1, `base_compatibility_checked: true`. The same applies to
   `scripts/gates.sh` through `BASE_REF`. Merging the base into the lane was not
   an option (the brief forbids merge/rebase), and it would not have been the
   honest check anyway.
3. **Nothing else failed.** The four Lean files compiled on the first attempt;
   no `sorry`, no `set_option`, no new axiom. Worth recording as a positive
   example: when the eight unit theorems are phrased over raw fields with their
   hypotheses written out, the assembly is thirteen one-line field assignments
   and the contract/canonical defeq (`ckSeminormE ≡ affineCkSeminorm`,
   `Data.energyENorm ≡ Section3.T24.energyENorm`, `SpaceTimeField ≡
   VelocityField`) is transparent to structure-instance elaboration — no
   `show`, no conversion lemma.

## Gap left after this lane

- **T24b** (`prop:multiple`, 30 fields, T15-gated) and **T24c**
  (`prop:conservative`, Uc3 assembly) are separate contracts; this lane
  registers only `T04.affine_variation`.
- The non-isolation field is the `ℝ≥0∞`-valued `ckSeminormE` on `tsupport b`
  (`Spec.lean:1104`), as reconciled; no real-valued `C^m` seminorm is claimed.
- `AffineRawData.energy_finite` is now derivable for every registered packet,
  but it is still *stated* as a clause of the raw bundle: a canonical module
  cannot mention `PacketAPI`, so the derivation
  (`energyENorm_lt_top_of_packet`) and its use are connected only in
  `Bindings/AffineVariation.lean` (`packetRawData`).
