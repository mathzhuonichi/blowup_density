ACCEPT

## what the lane claims

`REPORT_421.md:1-69` claims four generic lattice lemmas and six canonical U3 fields. The six statements are exactly the `ScalingAPI` fields at `formalization/NSFormalization/Section3/T15/Scaling.lean:219-277`: same `Ioc (0 : ℝ) place.ε₀`, time quantifiers, lattice summands, and periodized/scaled equalities. The requested paper citation is recorded in the API docstrings (`Scaling.lean:204-274`); the geometric premise is the placement result.

## what is in Lean

The generic support conversion, summability, nonzero-term vanishing, and tsum equality are implemented at `formalization/NSFormalization/Section3/T15/SingleCopy.lean:34-91`. The six proofs use the placement slice-support lemmas and raw `PlacementData` hypotheses at `SingleCopy.lean:97-191`; no hypothesis is silently discarded. The probe contains exact field checks and an active-time nonzero instance (`research/T15/probes/single_copy_closes.lean`). No forbidden tokens occur in the module/probe/audit, and the only changed tracked files versus `origin/erenup/integration-section3` are the lane deliverables (`git diff --name-only` showed the module plus the specified research files). The whole Section4 tree search found no alternative declarations for these six gaps.

## gaps

No correctness gap found. The substantive negative probe `research/T15/probes/rev421_negative.lean` changes the conclusion from `= g x` to `= g x + g x`; Lean rejects the attempted proof at line 12 with:

```
error: Type mismatch
  tsum_eq_single_copy_of_mem_cube hsupp hx
has type
  ∑' (n : PeriodicFrequency), g (x - latticeVector n) = g x
but is expected to have type
  ∑' (n : PeriodicFrequency), g (x - latticeVector n) = g x + g x
```

This is a substantive RHS mutation, not argument deletion.

## commands and results

All commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran `lake` from `verification/`:

- `lake build NSFormalization.Section3.T15.SingleCopy`: **Build completed successfully (10003 jobs)**; only replayed upstream warnings.
- `lake env lean ../formalization/NSFormalization/Section3/T15/SingleCopy.lean`: pass, 0 output.
- `lake env lean ../research/T15/probes/single_copy_closes.lean`: pass, 0 output.
- `lake env lean ../research/T15/axioms_u3.lean`: pass; all ten declarations print exactly `[propext, Classical.choice, Quot.sound]` (the exact ten lines are in the command output and declarations are listed at `axioms_u3.lean:10-19`).
- `make check`: pass; formalization-plan, contract policy (13 tests), and 45-work-item queue checks completed successfully.
- `scripts/gates.sh NSFormalization.Section3.T15.SingleCopy`: completed; module build/test-mutations gates passed (upstream replay warnings only).
- `python3 check_contracts.py --base-ref origin/erenup/integration-section3`: completed architecture checks; reports `base_compatibility_checked: false` and `source_hashes_match: false` for the repository-wide snapshot, with no lane-specific contract error.
- Forbidden-token grep on the new module/probe/audit: no matches.
- `grep -rn` over `formalization/NSFormalization/Section4` for all six names: no matches.
