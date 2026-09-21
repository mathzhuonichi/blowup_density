# T22 (bounded-domain norm layer, `03-torus.tex:600-626`: `eq:restriction-norm`, `eq:zero-extension`) — reconciliation of drafts A (lane 275, gpt-5.6-sol) and B (lane 276, gpt-6-astra)

Lead: erenup, 2026-09-17 (UTC 21:15).

## 1. Agreement
Both define the quotient norm `‖z‖_{H^s(Ω)} = inf_{Z|_Ω = z} ‖Z‖_{H^s(ℝ³)}` (`eq:restriction-norm`) on top of the registered ℝ³ datum norm (`sobolevENorm`/`IsSobolevDatum`, `Data.lean:150-260`), state that order zero is the usual `L²(Ω)` norm, and state `eq:zero-extension`: for a fixed compact `K ⋐ Ω` and `s ∈ ℝ`, smooth fields supported in `K` satisfy `‖z‖_{H^s(Ω)} ≤ ‖E₀z‖_{H^s(ℝ³)} ≤ C_{s,K,Ω} ‖z‖_{H^s(Ω)}` with the constant chosen **before** `z` (uniform over smaller supports and `ε`-families). Both include the cutoff-multiplier bound (`χ ∈ C_c^∞(Ω)`, `χ = 1` near `K`, an `H^s(ℝ³)` multiplier with a constant depending on `s, χ` only) — the mechanism the paper's proof uses and the "`H^s(ℝ³)` multiplier bounds, constants independent of `ε`" the T22 row asks for.

## 2. Rulings
| point | A | B | ruling |
|---|---|---|---|
| shape | `SobolevExtension` (extension record) + a large API with the cutoff `χ` and constants `C(Ω,K,s)` as **fields**, plus `restriction_norm`, `restriction_zero`, `zero_extension`, `cutoff_multiplier`, `cutoff_extension_identity` | `domainSobolevENorm Ω s` (a `def` = the infimum), `restrictField`, `zeroExtension`, `IsCutoffDatum`; `BoundedDomainNormAPI : Prop` with `orderZero`, `cutoffMultiplier`, `zeroExtensionComparison` | **B**: the quotient norm is a definition (`eq:restriction-norm` is a definition in the paper), the API has three propositional fields; constants are existential inside the fields, chosen before `z`. A's `cutoff_extension_identity` (`E₀z = χ·Z` for any extension `Z`) becomes a lemma in the proof plan. |
| hypotheses on `z` | `HasIntegrableSchwartzPairings` etc. | `ContDiffOn ℝ ∞ z Ω`, `tsupport (zeroExtension Ω z) ⊆ K` | **B** (the paper: "smooth fields supported in `K`"). |
| domain class | `IsBoundedOpenDomain Ω`, `CompactlyContained K Ω` | `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω` | **B's** (weaker hypotheses, same statement; the paper's `Ω` is a bounded open set — add `Bornology.IsBounded Ω` only if a proof needs it; note in COMPARISON). |
| names | — | `domainSobolevENorm`, `restrictField`, `zeroExtension`, `IsCutoffDatum` | keep B's. |

## 3. Decisions
`research/T22/Spec.lean` = B's definitions and three-field API, A's citations merged, ℝ³ vocabulary from the registered `Data.lean` (no torus objects needed — T22 is an ℝ³-side layer consumed by T23). Proof plan: `orderZero` from the datum characterization at `s = 0`; `cutoffMultiplier` from Section 4's B02/HomogeneousPartial cutoff lemmas (`Contracts/V1/HomogeneousPartial.lean` `annularSmoothing`/Schwartz multiplier bounds) or A03's tame product at integer orders + interpolation — the proof lane decides; `zeroExtensionComparison`: left inequality by definition (`E₀z` is an extension), right via `E₀z = χ·Z` and the multiplier bound.

## 4. Next
Lane 281: reconciled `research/T22/Spec.lean` + merged `COMPARISON.md`; then the proof lane (M, sol).
