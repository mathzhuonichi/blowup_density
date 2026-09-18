# Haar/cube attempts

> **Superseded preamble (r0, astra):** the paragraphs below up to the first `## completion` / r1 section describe the rejected r0 foundations-only delivery and are kept for provenance only; the authoritative content is the lane 366 r1 (Opus) section — codex re-review ACCEPT-WITH-NOTES, 2026-09-18 13:20Z.

The API bridge is definitional. The support transfer closes with Mathlib's
`eLpNorm_restrict_eq_of_support_subset`. The remaining general-p transfer is
reduced to equality of the `‖·‖ₑ ^ p.toReal` lintegrals; the existing T13
fundamental-domain result is stated for continuous real integrands, so a
measurable ENNReal extension remains to be connected.

## r1 (lane 366, post-REJECT) — the master measure route

**Positive (what worked).** Rather than reducing the periodic transfer to a
hypothesised lintegral identity (the r0 stub the reviewer rejected), the whole
`eLpNorm` family — including `p = 0` and `p = ⊤` — is closed by **one** measure
identity `map_torusChart : Measure.map torusChart periodicTorusMeasure =
volume.restrict fundamentalCube`, where `torusChart z = toSpace
((UnitAddTorus.measurableEquivPiIoc 0 z).val)` is the fundamental-domain chart and
`torusLift v = v ∘ torusChart` by `rfl`.  Then `eLpNorm_torusLift_eq_restrict` is
just `(measurableEmbedding_torusChart).eLpNorm_map_measure` (Mathlib's
`MeasurableEmbedding.eLpNorm_map_measure`, which handles `p = 0` / finite / `⊤`
uniformly) rewritten by `map_torusChart`.  No exponent case split in this module.

`map_torusChart` is proved by `Measure.map_map`-composing three pieces:
- `UnitAddTorus.measurePreserving_equivPiIoc 0` (torus Haar ≃ `comap Subtype.val volume`);
- `map_comap_subtype_coe` (`Subtype.val` pushforward = `volume.restrict` of the
  half-open box `(0,1]³`);
- `PiLp.volume_preserving_toLp` + `Measure.restrict_map` +
  `toSpace_preimage_fundamentalCube` (`toSpace ⁻¹' fundamentalCube = Icc 0 1`),
  bridging the half-open box to the closed cube via `Measure.univ_pi_Ioc_ae_eq_Icc`
  and `Measure.restrict_congr_set`.

**Negative / dead ends.**
- The r0 attempt stated `eLpNorm_torusLift_eq_restrict_of_lintegral` taking the
  norm-density lintegral equality `hlin` as a hypothesis: this is goal
  repackaging (its only input `hlin` is the rpow-conclusion), leaves `p = ⊤`
  uncovered, and its `hv` was unused with a linter warning — correctly rejected.
- Deprecated `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` (two warnings) is
  avoided entirely by not doing a manual finite-`p` rpow rewrite; the map-measure
  lemma does it internally with the non-deprecated `…_toReal` form.
- `MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)` does not directly unify
  with the set-builder `{x | ∀ i, x i ∈ Ioc ..}`; convert with `ext x; simp` to
  the `Set.univ.pi` form first (`iocBox_measurable`).
- reusing `T15/HaarBridge.lean lintegral_enorm_torusLift` was possible for finite
  `p` but still leaves the `p = ⊤` essSup endpoint; the measurable-embedding
  pushforward supersedes it and keeps the import surface to `MeanZeroCalculus` +
  `T13.{TorusIdentity,ConstantEndpoints}` (no `HaarBridge` dependency).
