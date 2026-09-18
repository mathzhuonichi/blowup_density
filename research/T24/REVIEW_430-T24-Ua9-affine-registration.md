ACCEPT-WITH-NOTES

## what the lane claims

The report claims a 13-field `AffineVariationAPI`, raw-packet assembly, registration as `T04.affine_variation`, and standard logical axioms. The contract declarations match `research/T24/Spec.lean:958-1121` byte-for-byte apart from namespace (`verification/Contracts/V1/AffineVariation.lean:46-209`); the paper citation is `paper/sections/03-torus.tex:668-696`.

## what is in Lean

`AffineAssembly.lean` supplies the raw bundle and assembly (`formalization/NSFormalization/Section3/T24/AffineAssembly.lean:1-260`). The binding derives the missing energy bound from packet fields (`verification/Bindings/AffineVariation.lean:49-68`) and maps all thirteen fields (`:75-96`). Tests include conformance, non-vacuity, and axiom checks (`verification/Tests/AffineVariation.lean:1-70`). Whole-tree grep for the report's “not in tree” gap names found no matching Section4 declarations.

Statement fidelity checks found no silently vacuous hypotheses: `radius_pos`, strict window, explicit affine operators, and all quantifier orders are present. The cylinder definition is consistently `Ioo τ₀ τ₁ ×ˢ Metric.ball c r` in both Spec and contract (`research/T24/Spec.lean:958-964`, `verification/Contracts/V1/AffineVariation.lean:46-52`).

## gaps

The required command against the current moving base does not pass: `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` reports `Removed stable specification: verification/Contracts/V1/MeanZeroCalculus.lean` and `base_compatibility_checked: false`, because the remote base has advanced beyond this lane's branch point. The lane's documented workaround at merge-base `4e8a840a` passes; after rebasing/merging the current base, rerun the required command and `scripts/gates.sh` with the literal base ref. This is one infrastructure fix, not a mathematical defect.

The substantive negative probe widened `τ₁ < 1` to `τ₁ ≤ 1`; Lean fails at `research/T24/probes/rev430_mutation.lean:9` with “has type `τ₁ ≤ 1` but is expected … `τ₁ < 1`.”

## commands and results

`lake build NSFormalization.Section3.T24.AffineAssembly Contracts.V1.AffineVariation Bindings.AffineVariation Tests.AffineVariation`: **Build completed successfully (9372 jobs)**; lane tests print standard logical axioms only. `make check`: plan/policy/work-queue checks pass; `make test` and `make test-mutations`: all registered tests pass, mutation suite passed. `cd verification && lake env lean ../research/T24/axioms_ua9.lean`: all 20 declarations print `[propext, Classical.choice, Quot.sound]`. `rg` hygiene scan over the four lane Lean files found no `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`. `git diff --name-only origin/erenup/integration-section3...HEAD` shows only the four new Lean files, records, and generated registry/ledger files; no existing module is edited. `git diff --stat 4e8a840a -- verification/contracts.json`: one file, 11 insertions.

ACCEPT-WITH-NOTES — merge/rebase onto the current integration base, then rerun the literal base-ref compatibility gate.
