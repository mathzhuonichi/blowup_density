ACCEPT

## 1. What the lane claims

The worker claims three declarations: `fixedInitialDensity`,
`regularReferenceSingular`, and `mixedDensity` (`research/T19/REPORT_464.md:5`,
`:14`, `:26`). All three declarations exist at
`formalization/NSFormalization/Section3/T19/DensityEngine.lean:24`, `:49`, and
`:65`, and the report's displayed types are exact copies of their Lean types.

The claims match the lane brief and the canonical fields:

- `fixedInitialDensity` agrees literally with
  `PeriodicDensityAPI.fixedInitialDensity`
  (`formalization/NSFormalization/Section3/T19/Density.lean:74`) and with the
  paper's fixed-`a`, fixed-`nu`, fixed-`T`, `s < 1/2` density statement
  (`paper/sections/03-torus.tex:349`). The paper requires `f in F`, strict
  norm distance, and lifespan at most `T` (`paper/sections/03-torus.tex:352`),
  exactly as expanded by `RelativelyDenseT` and `breakdownSetT`
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:318`, `:322`).
- `regularReferenceSingular` agrees literally with
  `PeriodicDensityAPI.regularReferenceSingular`
  (`formalization/NSFormalization/Section3/T19/Density.lean:86`). Its exact
  lifespan equality is the sharp regular-reference conclusion used in the
  paper proof (`paper/sections/03-torus.tex:363`) and explicitly distinguished
  from the by-`T` headline statement at `paper/sections/03-torus.tex:589`.
- `mixedDensity` agrees literally with `MixedRegionAPI.mixedDensity`
  (`formalization/NSFormalization/Section3/T19/Density.lean:113`) and retains
  `1 <= p,q <= infinity` and `3/p + 2/q > 3` from
  `paper/sections/03-torus.tex:528`-`:536`. The relative mixed topology itself
  has the required `forall g in F, forall r > 0` expansion at
  `formalization/NSFormalization/Section3/T19/Density.lean:57`.

The conformance probe copies all three canonical result types and closes each
by the corresponding theorem, with no extra hypotheses
(`research/T19/probes/density_engine_closes.lean:10`, `:17`, `:27`).

## 2. What is in Lean

The implementation follows the intended mathematical dichotomy.

- The already-broken branch witnesses the reference force itself
  (`DensityEngine.lean:30`-`:32`, `:72`-`:77`). The zero values are proved by
  genuine zero representatives, not by a `top.toReal` convention
  (`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:238`, `:258`).
- In the regular branch, strict inequality above `ofReal T` is unpacked from
  the defining supremum of realized solution horizons
  (`DensityEngine.lean:33`-`:40`, `:78`-`:85`); this is faithful to the
  definitions of `maximalLifespanT` and `RegularThroughT`
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:303`, `:307`).
  It is the same dichotomy as the cited R3 template
  (`verification/Bindings/DensityFromInsertion.lean:30`-`:50`).
- U7 and U8 use the isolated U0 export `exists_force_close`, whose result
  includes both force membership and exact lifespan
  (`formalization/NSFormalization/Section3/T19/Threading.lean:226`-`:237`).
  U8 preserves that equality at `DensityEngine.lean:60`-`:62`, matching the
  cited exact-lifespan template (`verification/Bindings/MainThresholds.lean:97`).
- U9 uses the U0 mixed bound
  (`formalization/NSFormalization/Section3/T19/Threading.lean:172`) and U2's two
  positive exponents (`formalization/NSFormalization/Section3/T19/Bookkeeping.lean:58`).
  Both powers tend to zero (`DensityEngine.lean:88`-`:105`), the norm is
  squeezed by the mixed bound (`:106`-`:113`), and an actual positive scale in
  `Ioc 0 eps0` is selected (`:114`-`:118`). This is the mixed analogue of the
  cited witness-selection pattern at
  `verification/Bindings/CompletedClosure.lean:179`-`:194`.

No theorem has an unused semantic binder: `a`, `nu`, `T`, force membership,
and the positivity/regularity hypotheses are passed into the insertion or the
lifespan comparison; `s` and its bound feed U0; `p`, `q`, and their region
hypotheses feed U2 and the mixed estimate (`DensityEngine.lean:29`-`:46`,
`:57`-`:62`, `:71`-`:118`). There are no named inputs or placeholder
propositions. The direct module check emits no unused-variable warning.

Non-vacuity is checked independently in
`research/T19/probes/rev464_nonvacuity.lean:10`-`:33`: the zero datum is in
`initialClassT`, the zero force is in `forceClassT`, `nu=T=1`, `s=0`, and
`r=1` satisfy all guards, and the theorem produces an actual member of
`breakdownSetT 1 0 1`. This probe compiles with exit 0 and no output.

The axiom audit prints exactly the required three axioms for each declaration:

```text
'NSFormalization.Section3.T19.fixedInitialDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.regularReferenceSingular' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T19.mixedDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Gaps and hygiene

No theorem gap remains. The worker report makes no "not in the tree" claim, so
the conditional whole-Section4 missing-lemma check has no claim to validate.
For comparison, a whole-tree `grep -rn "regularThrough_iff"
formalization/NSFormalization/Section4` does find the R3 theorem at
`formalization/NSFormalization/Section4/A02/Order.lean:135`; the lane does not
misstate its availability.

The substantive negative mutation widens `s < 1/2` to `s < 3/4`
(`research/T19/probes/rev464_mutation.lean:9`-`:15`). It fails with exit 1 for
the expected theorem-type mismatch, not because an argument was removed:

```text
../research/T19/probes/rev464_mutation.lean:15:2: error: Type mismatch
  fixedInitialDensity
has type
  ∀ a ∈ initialClassT,
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → ∀ s < 1 / 2, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
but is expected to have type
  ∀ a ∈ initialClassT,
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T → ∀ s < 3 / 4, RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)
```

Hygiene scans on `DensityEngine.lean` returned exactly:

```text
NO_FORBIDDEN_TOKENS
NO_MAXHEARTBEATS
```

Thus there is no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`. `git diff --check 4d1f4944^ 4d1f4944` exits 0 with no output.
Commit `4d1f4944` adds one implementation module and two Lean audit/probe files;
it modifies no pre-existing Lean module. Its exact name-status output is:

```text
A formalization/NSFormalization/Section3/T19/DensityEngine.lean
A research/T19/ATTEMPTS_U7_U9.md
A research/T19/REPORT_464.md
M research/T19/T19_SPLIT.md
A research/T19/axioms_u7_u9.lean
A research/T19/probes/density_engine_closes.lean
```

The requested `git diff --name-only
origin/erenup/integration-section3...HEAD` warns that there are multiple merge
bases and chooses `e5b9e31a`; it lists integration-side record files as well as
the six lane files. None of the listed pre-existing files is a Lean module, and
the only listed implementation module is the newly added `DensityEngine.lean`.
No path under `verification/` is listed. The worktree already had an uncommitted
brief-text adjustment at review start; it is not part of commit `4d1f4944` and
was left untouched.

## 4. Commands and results

Environment for every Lean command: `. ../scripts/lean-env.sh`, working
directory `verification/`, `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T19.Threading NSFormalization.Section3.T19.Density`
   exited 0. Lake replayed only pre-existing dependency lints and ended exactly:

   ```text
   Build completed successfully (10657 jobs).
   ```

2. `lake build NSFormalization.Section3.T19.DensityEngine` exited 0. It emitted
   no diagnostic from `DensityEngine.lean`; after replayed pre-existing
   dependency lints, the exact terminal output was:

   ```text
   Build completed successfully (10658 jobs).
   ```

3. `lake env lean
   ../formalization/NSFormalization/Section3/T19/DensityEngine.lean` exited 0;
   exact output: empty.

4. `lake env lean ../research/T19/probes/density_engine_closes.lean` exited 0;
   exact output: empty.

5. `lake env lean ../research/T19/axioms_u7_u9.lean` exited 0; exact output is
   the three axiom lines pasted in part 2.

6. `lake env lean ../research/T19/probes/rev464_nonvacuity.lean` exited 0;
   exact output: empty.

7. `lake env lean ../research/T19/probes/rev464_mutation.lean` exited 1 with the
   expected diagnostic pasted in part 3.

8. `. scripts/lean-env.sh && make check` exited 0. The command prints a large
   contract-closure JSON object. These selected lines are verbatim; the bracketed
   ellipsis marks that JSON output:

   ```text
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   [... contract-closure JSON ...]
   python3 experiments/test_contract_policy.py
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The preceding JSON reports 50 registered contracts; its existing
   `source_hashes_match: false` and copied-source token inventory are
   informational, and the command returns success.

9. `git diff --check origin/erenup/integration-section3...HEAD` exited 0 with
   only the multiple-merge-base warning noted above.

Because the requested diff contains no `verification/` path, the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates do not apply to this lane and were not
run. No fix is required.
