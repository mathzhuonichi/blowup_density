ACCEPT

## 1. What the lane claims

The worker claims exactly two U4 results: `scaled_classes` and
`inverse_identities`, with their full statements printed in
`research/T11/REPORT_314.md:6` and `research/T11/REPORT_314.md:14`. It also
claims that positive time dilation sends a compact force-support set to the
compact image `(fun t ↦ ν * t) '' K` (`research/T11/REPORT_314.md:21`), that no
named input remains (`research/T11/REPORT_314.md:38`), and that both public
results use exactly the standard three axioms (`research/T11/REPORT_314.md:43`).

These are the two fields allocated to U4 by the binding split
(`research/T11/T11_SPLIT.md:62`), and they are byte-for-byte the corresponding
canonical API field types (`research/T11/probes/api_on_canonical.lean:195` and
`research/T11/probes/api_on_canonical.lean:200`). The mathematical scaling is
the manuscript's `τ = ν t`, `ũ = ν⁻¹u`, `p̃ = ν⁻²p`, `f̃ = ν⁻²f`, followed by
restoration of `ν` (`paper/sections/appendix-a-local-theory.tex:79`). The data
classes are exactly smooth divergence-free periodic initial data and smooth
periodic forces compactly supported in positive time
(`paper/sections/02-preliminaries.tex:9` and
`paper/sections/02-preliminaries.tex:23`).

## 2. What is in Lean

The declarations exist at
`formalization/NSFormalization/Section3/T11/Rescaling.lean:69` and
`formalization/NSFormalization/Section3/T11/Rescaling.lean:80`, and their types
match the report and canonical API exactly. The underlying scaling definitions
also match the manuscript formulas
(`formalization/NSFormalization/Section3/T11/LocalTheory.lean:129` through
`formalization/NSFormalization/Section3/T11/LocalTheory.lean:154`).

For `scaled_classes`, the proof preserves all three conjuncts of
`initialClassT` (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:234`)
and all support/smoothness/periodicity clauses of `forceClassT`
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:239`). In
particular, its image set is compact, remains in `Ioi 0` using `0 < ν`, and
contains the rescaled temporal support
(`formalization/NSFormalization/Section3/T11/Rescaling.lean:41` through
`formalization/NSFormalization/Section3/T11/Rescaling.lean:65`). For
`inverse_identities`, positivity supplies `ν ≠ 0` and each of the three
function identities is proved extensionally
(`formalization/NSFormalization/Section3/T11/Rescaling.lean:85`). There are no
empty-interval, `⊤.toReal`, unused-binder, or named-input escape hatches.

The supplied probe checks both exact target types and gives a genuinely
nonzero periodic initial datum to which `scaled_classes` applies
(`research/T11/probes/rescaling_closes.lean:17` and
`research/T11/probes/rescaling_closes.lean:33`). It typechecks with no output.
The raw reviewer axiom probe confirms:

```text
'NSFormalization.Section3.T11.scaled_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.inverse_identities' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This agrees with the guarded audit at `research/T11/axioms_rescaling.lean:7`
and `research/T11/axioms_rescaling.lean:11`.

The substantive negative probe changes the first restoration constant from
`ν` to `-ν` (`research/T11/probes/rev314_sign_flip.lean:11`). The original
proof then fails, as expected, with:

```text
../research/T11/probes/rev314_sign_flip.lean:13:71: error: unsolved goals
ν : ℝ
hν : 0 < ν
u : SpaceTimeField
hν0 : ν ≠ 0
z : NavierStokes.ProblemStatement.SpaceTime
⊢ -u (-(ν * z.1) / ν, z.2) = u z
```

Hygiene passes. The new implementation and positive probe contain none of
`sorry`, `admit`, `axiom`, or `native_decide`, no heartbeat override, and no
anonymous instance. The base diff reports `Rescaling.lean` as added, not as a
modification of an existing Lean module; the only modified pre-existing file
is the required one-line status addition in `research/T11/T11_SPLIT.md:64`.

## 3. Gaps

There is no proof or statement gap and no fix is required. The attempts file
honestly records no residual named input (`research/T11/ATTEMPTS_RESCALING.md:65`).
Its closest-tree citations are accurate: `normalized_residual`,
`normalized_smooth`, and `normalized_periodic` occur at
`formalization/NSFormalization/Paper1/PeriodicUniqueness.lean:19`,
`formalization/NSFormalization/Paper1/PeriodicUniqueness.lean:43`, and
`formalization/NSFormalization/Paper1/PeriodicUniqueness.lean:51`, but do not
package either exact U4 field.

The required whole-tree check

```text
grep -rnE 'unitViscosity|restoreViscosity|scaled_classes|inverse_identities' formalization/NSFormalization/Section4
```

returned no output (exit 0). The broader claimed search scope returned the U4
names only in the new `Rescaling.lean`, plus the underlying scaling definitions
in `LocalTheory.lean`; hence the worker's “no pre-existing exact declaration”
claim is supported.

`verification/` is absent from
`git diff --name-only origin/erenup/integration-section3...HEAD`, so the
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply to this lane.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T11.Rescaling` — exit 0. The complete
   captured output had 82 lines / 4639 bytes, SHA-256
   `e70b7bb24940935c2fbf5742f6c5a5ed975dd0c62bbf3bc8e489d40986fe7b01`.
   It replayed warnings from pre-existing dependency modules, with no line for
   `Rescaling` and no error; its exact final output was:

   ```text
   Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
   Build completed successfully (9897 jobs).
   ```

2. `lake env lean ../formalization/NSFormalization/Section3/T11/Rescaling.lean`
   — exit 0, exact output: empty.

3. `lake env lean ../research/T11/probes/rescaling_closes.lean` — exit 0,
   exact output: empty.

4. `lake env lean ../research/T11/axioms_rescaling.lean` — exit 0, exact
   output: empty; its `#guard_msgs` checks enforce the exact printed axiom
   lists quoted in part 2.

5. `lake env lean ../research/T11/probes/rev314_axioms.lean` — exit 0, with
   the exact two axiom lines quoted in part 2.

6. `lake env lean ../research/T11/probes/rev314_sign_flip.lean` — expected exit
   1, with the exact unsolved goal quoted in part 2.

7. `make check` from the worktree root — exit 0. The complete captured output
   had 43,333 lines / 1,785,368 bytes, SHA-256
   `1029e2e9a64232cb9d89c12b2a3abe46326fc3cf70d1934e6d30d1532f936af0`.
   Its exact final output was:

   ```text
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.047s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

8. `git diff --check origin/erenup/integration-section3...HEAD` — exit 0,
   exact output: empty. `git diff --name-status` reported:

   ```text
   A formalization/NSFormalization/Section3/T11/Rescaling.lean
   A research/T11/ATTEMPTS_RESCALING.md
   A research/T11/REPORT_314.md
   M research/T11/T11_SPLIT.md
   A research/T11/axioms_rescaling.lean
   A research/T11/probes/rescaling_closes.lean
   ```
