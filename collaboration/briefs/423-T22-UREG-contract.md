# Lane 423-T22-UREG-contract — T22 U-REG: assemble `BoundedDomainNormAPI` and register `T04.bounded_domain_norm`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) contract-registration worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/423-T22-UREG-contract` (git branch `erenup/423-T22-UREG-contract`, based on lane 418's branch merged with `origin/erenup/integration-section3`:
`Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry,CutoffKernel,OrderZero,CutoffMultiplier,CutoffMultiplierField,ZeroExtRegularity,CutoffDatum,ZeroExtensionComparison}.lean` —
all three canonical fields proved: `orderZero` (393), `cutoffMultiplier` (406), `zeroExtensionComparison` (418)). Read `CLAUDE.md` (contract import rules: `Contracts/*` import only
`Mathlib`/`Contracts.*` + the whitelist in `experiments/check_contracts.py`; restated definitions bridged by `rfl` in `Bindings/`; `ensure_ascii=False, indent=2`; frozen V1 files untouched),
**`research/T22/T22_SPLIT.md` §0 and unit U-REG** (`:175-180`), `research/T22/Spec.lean` (the `BoundedDomainNormAPI`, its statement def, and the vocabulary: `RealVectorSobolev`,
`domainSobolevENorm`, `restrictField`, `restrictDatum`, `zeroExtension`, `IsCutoffDatum`, `angularRealization`, `DomainTest`, …), the canonical module `Section3/T22/Domain.lean`
(canonical spellings; note lane 409 brought `Mathlib.Geometry.Manifold.PartitionOfUnity` into the import closure), `research/T22/RECONCILIATION.md`, `REPORT_{383,393,406,409,418}.md`, the
registration precedents `verification/Contracts/V1/Localization.lean` / `Bindings/Localization.lean` / `Tests/Localization.lean` (lane 371, `T02.localization`) and
`Contracts/V1/LocalPotential.lean` (lane 371's sibling), the registry `verification/contracts.json`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`/placeholder `Prop` fields; do not modify existing `Contracts/V*` or `Tests/*`; new files only except the registry/work-items additions.
- Every restated definition needs a `rfl` bridge (or a documented fieldwise conversion when `rfl` is impossible). Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

## Deliverables
1. `formalization/NSFormalization/Section3/T22/Assembly.lean`: `def boundedDomainNorm : BoundedDomainNormAPI := ⟨orderZero, cutoffMultiplier, zeroExtensionComparison⟩` (canonical record) and the
   statement alias (`Nonempty …`), plus a non-vacuity example (nonzero `ContDiffBump` on a ball `K ⋐ Ω`, per the split).
2. `verification/Contracts/V1/BoundedDomainNorm.lean`: `BoundedDomainNormAPI` **token-for-token from `research/T22/Spec.lean`** with the vocabulary restated verbatim (provenance comments)
   over the registered `Contracts/V1/HomogeneousNorm.lean`/`Data.lean`/`Sobolev*` vocabulary where it exists (import, do not copy registered names; grep `Contracts/V1` for `RealVectorSobolev`,
   `sobolevENorm`, `IsSobolevDatum`, `angularRealization` — reuse whatever is registered, restate the rest), and `boundedDomainNormStatement`.
3. `verification/Bindings/BoundedDomainNorm.lean`: `rfl` bridges for every restated definition to the canonical `NSFormalization.Section3.T22.*` (or `Section4.D01`/`Paper3`) ones, the instance
   `boundedDomainNorm : BoundedDomainNormAPI` from the canonical record, `boundedDomainNormStatement_holds`.
4. `verification/Tests/BoundedDomainNorm.lean`: `checkedBoundedDomainNorm`, `run_cmd TestSupport.checkAxioms`, a conformance `example` restating one field against `Spec.lean`, non-vacuity.
5. Registry entry `T04.bounded_domain_norm` (`version: 1`, `parent_task`, honest `scope`: constants closed terms; the manifold partition-of-unity import in the closure), `ensure_ascii=False, indent=2`,
   additions only; `collaboration/work_items.json` + `python3 experiments/tasks.py render`. Records `research/T22/ATTEMPTS_UREG.md`, `research/T22/axioms_ureg.lean`, U-REG status in `T22_SPLIT.md`.

## Gates (paste outputs)
`scripts/gates.sh` from the worktree root (`make check`, `make test`, `make test-mutations`); `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` (exit 0,
`registered_contracts` = base + 1, `base_compatibility_checked: true`); the axioms file; `git diff --stat verification/contracts.json`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T22/REPORT_423.md`.
