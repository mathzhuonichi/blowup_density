# Lane 449 — T23 proof-lane split report

## 1. What was proved / planned

Planning only: no Lean theorem was proved or module changed. `research/T23/T23_SPLIT.md` now assigns all 48 `BoundaryInsertionAPI` fields, all 16 `DomainPlacementData` fields, all 10 `ClassicalSolutionOmega` fields, the seven cutoff data fields, the three T22 norm fields and the final quantified statement. Nine units include exact Spec targets, source routes, S/M/L sizing, codex-sol/codex-astra assignments, dependencies, waves and registration risks. The first skeleton was committed before extended supplier reading; each section was committed separately.

## 2. What is in the Lean tree

Verified registered suppliers are I02 V1/V2, I03 and T22 (`verification/contracts.json:27,38,71,478`). T22's historical copied record is replaced at proof time by the registered contract and existing fieldwise canonical adapters (`verification/Bindings/BoundedDomainNorm.lean:54–88`). T18 U1–U6 and U8 provide checked source patterns, but their `InsertionData` requires periodic solutions and does not convert to Ω. The split distinguishes generic reusable helpers from domain re-proofs. T11 uniqueness is periodic (`formalization/NSFormalization/Section3/T11/Uniqueness.lean:27`). The full evidence ledger and scoped searches are in split §2.

## 3. Gaps and next handoff

The current statement has a concrete quantifier defect: arbitrary `D : CutoffData` may have `D.ε₀=0`, contradicting the required positive threshold below D.ε₀ (`Spec.lean:158,728,734,1037`). Registration requires an owner-approved compatible/existential cutoff construction; merely citing an inhabited I02 record cannot supply it. No existing Spec was edited.

I02 requires global smoothness and divergence, whereas the given reference has them on Ω; U2 owns the local solenoidal extension/transport bridge. No domain no-slip uniqueness supplier was found in Section4/Paper1/vendor; U7 is an L unit with its exact target. U8 uses the explicit solution plus this uniqueness and compact-domain boundedness to prove lifespan=T, without requiring a full domain continuation theory. It must retain interior blow-up witnesses. The proposed boundary helper modules import the sorry-bearing `BoundaryCorollary.lean`; reuse their geometry only in a clean module. Force rates additionally require a measurable-path-to-per-slice norm inequality and an all-negative-order L² contraction.

Next: start geometry, local correction and domain uniqueness independently; resolve statement repair and domain registration/shape/gauge decisions with the owner; gate final assembly and registration on T18 U12. No push, merge, rebase or external message was performed.

## 4. Commands and results

Read `CLAUDE.md`, session/plan context, T23 Spec/reconciliation/comparison, T18 report/split, T20 split, registered contracts/bindings and cited implementation sources with `sed -n` and declaration searches with `grep -rn`/`rg`. Read paper `03-torus.tex:600–667` directly. The exact no-result uniqueness/domain-record grep commands and interpretation are preserved in split §2.

A comment-stripped field inventory found 16 placement, 10 solution and 48 API fields; every field name is included in the split. `git diff --check` passed. `. scripts/lean-env.sh; make check` exited 0: 46 registered contracts, 13 contract-policy tests passed, 45 work items consistent. Its existing audit inventory reports `source_hashes_match=false` and the copied `BoundaryCorollary.lean:90` sorry; these were not changed. No Lean build/test or mutation run was needed for this documentation-only lane, and no Lean validation is claimed.

Section commits: `7c0d2e8b` skeleton; `9c05aa5f` ground rules/supplier audit; `7e6f646b` units; `dfed3dd8` ledger; `36314903` waves; `6fc0a22e` risks. Final report/field-name audit follows in the final documentation commit.
