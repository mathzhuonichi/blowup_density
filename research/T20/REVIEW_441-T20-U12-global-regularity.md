ACCEPT

# Independent review — lane 441 T20 U12 `globalRegularity`

## 1. What the lane claims

The worker report claims two declarations: the supporting endpoint lemma
`maximal_squaredHTwoIntegralT_ne_top` and the final theorem
`globalRegularity`, with the latter literally inhabiting the
`CriticalRegularityTAPI.globalRegularity` field at
`c := criticalSmallnessH1` (`research/T20/REPORT_441.md:5-28`).  It claims no
named input and no residual gap (`research/T20/REPORT_441.md:26-28,46-65`).

That is faithful to the requested mathematics:

- The paper states that there is a positive universal `c` such that
  `g ∈ F` and `ρ < cν` imply infinite from-rest maximal lifespan
  (`paper/sections/03-torus.tex:383-390`), and its continuation argument is
  precisely finiteness of the squared `H²` time integral at a hypothetical
  finite endpoint (`paper/sections/03-torus.tex:490-503`).
- The canonical Lean field has quantifier order
  `ν, 0 < ν, g, g ∈ forceClassT, ρ < ofReal (c*ν)` and conclusion
  `maximalLifespanT ν 0 g = ⊤`
  (`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:365-368`).
  The delivered theorem has exactly this type after substituting
  `criticalSmallnessH1` for `c`
  (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:114-117`).
  The conformance probe also checks the abstract API field and the concrete
  theorem (`research/T20/probes/global_regularity_closes.lean:27-38`).
- The chosen constant is genuinely positive
  (`formalization/NSFormalization/Section3/T20/H1Energy.lean:368-373`), so the
  strict smallness condition is not made empty by the substitution.
- T11's exact consumer premise is `∀ S > 0`,
  `ofReal S ≤ maximalLifespanT`, then
  `squaredHTwoIntegralT S u ≠ ⊤`
  (`formalization/NSFormalization/Section3/T11/Assembly.lean:318-326`).  The
  supporting theorem has exactly those horizon hypotheses
  (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:35-42`).
  Its exhaustion uses positive, strict subhorizons and a directed union of
  `Ioo 0 (S-S/(n+2))`
  (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:43-99`).
  The maximal-solution API really supplies a classical solution together with
  `w.velocity = u` on every strict subhorizon
  (`formalization/NSFormalization/Section3/T11/LocalTheory.lean:51-56`), so the
  report is correct that no uniqueness transport is needed.
- The estimate applied on each strict subhorizon is U11's exact three-conjunct
  `continuationBound`
  (`formalization/NSFormalization/Section3/T20/Continuation.lean:677-696`), and
  the proof extends its first term monotonically from the subhorizon to `S`
  (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:100-106`).
  The final theorem obtains an unconditional maximal solution and invokes the
  proved H3-narrowed continuation package
  (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:118-124`;
  `formalization/NSFormalization/Section3/T11/Assembly.lean:370-380`).

All named hypotheses are honest and used: `hν` and `hg` enter maximal
existence and the local estimate, while `hsmall` enters the local estimate and
the proof that its uniform bound is finite; `hmax` supplies the strict-horizon
solutions; and `hS`, `hSL` control the nonempty exhaustion and lifespan
comparison (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:35-106,118-124`).
There is no `⊤.toReal = 0` shortcut, empty-interval shortcut, unused theorem
binder, named assumption, or repackaged residual proposition.

## 2. What is in Lean

The new proof module contains exactly the two claimed public declarations
(`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:35-42,114-124`).
The final theorem is the canonical field verbatim, and the helper supplies the
endpoint-local finiteness needed by T11 rather than weakening the consumer.

Non-vacuity is explicit.  The delivered probe constructs zero force in
`forceClassT`, proves `criticalRho 0 = 0`, proves
`0 < ofReal (criticalSmallnessH1 * 1)`, and applies `globalRegularity`
(`research/T20/probes/global_regularity_closes.lean:40-68`).  Thus the
hypotheses are simultaneously satisfiable and the theorem is not vacuous.

The axiom file names both declarations
(`research/T20/axioms_u12.lean:10-13`), and rerunning it printed exactly
`[propext, Classical.choice, Quot.sound]` for each.  The proof module has no
`sorry`, `admit`, declaration `axiom`, `native_decide`, or `maxHeartbeats`
override (`formalization/NSFormalization/Section3/T20/GlobalRegularity.lean:1-126`).

Hygiene is satisfactory.  Relative to the lane commit, the only Lean files are
new files; no pre-existing Lean module is modified.  The requested comparison
against `origin/erenup/integration-section3` lists `Continuation.lean` (the
inherited lane-437 addition) and `GlobalRegularity.lean` as additions, not
modifications.  The lane-441 commit itself adds only `GlobalRegularity.lean`
under `formalization/`.  The paper citations in the module and report agree
with the passages quoted above.

## 3. Gaps and negative check

No mathematical or Lean gap remains.  The report makes no “not in the tree”
claim: its only use of “missing” is the recorded pre-build `.olean` diagnostic
(`research/T20/REPORT_441.md:46-65`; `research/T20/ATTEMPTS_U12.md:78-88`).
Consequently there is no alleged missing Section4 lemma for which the mandated
whole-tree absence search applies.

Reviewer mutation: `research/T20/probes/rev441_doubled_radius.lean:16-20`
doubles the permitted force radius from `criticalSmallnessH1` to
`2 * criticalSmallnessH1` without dropping an argument.  Reusing the delivered
proof fails exactly at that stronger constant:

```text
../research/T20/probes/rev441_doubled_radius.lean:20:2: error: Type mismatch
  globalRegularity
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ g ∈ forceClassT,
        criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) → maximalLifespanT ν (fun x => 0) g = ∞
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ g ∈ forceClassT,
        criticalRho g < ENNReal.ofReal (2 * criticalSmallnessH1 * ν) → maximalLifespanT ν (fun x => 0) g = ∞
```

Exit status was `1`, as expected.  This is a substantive strengthening of the
main statement and confirms that the stated smallness radius is not silently
ignored.  The positive non-vacuity check is the delivered zero-force instance
cited in part 2.

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`; Lake was run
only from `verification/`, and the build used `LEAN_NUM_THREADS=6`.

1. Module build

   ```text
   $ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.GlobalRegularity
   [449 lines / 26641 bytes of replayed warnings from pre-existing dependencies]
   Build completed successfully (10656 jobs).
   ```

   Exit `0`.  There was no line naming `GlobalRegularity` and no `error:` line.
   The complete captured output had SHA-256
   `24188b1b4cf70872eca6a0370436b031d308b877120714095ea12554befcf428`;
   all non-final lines were replayed dependency warnings.  The target module
   itself was silent.

2. Direct module check

   ```text
   $ lake env lean ../formalization/NSFormalization/Section3/T20/GlobalRegularity.lean
   ```

   Exit `0`; exact output was empty.

3. Canonical-shape/non-vacuity probe

   ```text
   $ lake env lean ../research/T20/probes/global_regularity_closes.lean
   ```

   Exit `0`; exact output was empty.

4. Axiom audit

   ```text
   $ lake env lean ../research/T20/axioms_u12.lean
   'NSFormalization.Section3.T20.maximal_squaredHTwoIntegralT_ne_top' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T20.globalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit `0`; both declarations have exactly the permitted axiom set.

5. Repository gate

   ```text
   $ make check
   python3 experiments/check_formalization_plan.py --check
   ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   Exit `0`.  `check_contracts.py` reported `registered_contracts: 46` and no
   failure.  Its architecture closure makes the exact output large (52,503
   lines / 2,170,111 bytes); the complete captured output had SHA-256
   `6c75be9c102bc54bbdb97c667ef32ed363b69efbc4e44d8fabbbdf321ebaa7c3`.
   The pre-existing plan scan reports the known copied-source token in
   `Paper1/BoundaryCorollary.lean`; it is outside this lane and the gate exits
   successfully.

6. Hygiene scan

   ```text
   $ rg -n -i '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section3/T20/GlobalRegularity.lean
   ```

   Exact output was empty; `rg` exit `1` means no match.

7. Requested base diff

   ```text
   $ git diff --name-only origin/erenup/integration-section3...HEAD
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 1c965400e3308df1cd679dfe843b0d5c47e49b82
   formalization/NSFormalization/Section3/T20/Continuation.lean
   formalization/NSFormalization/Section3/T20/GlobalRegularity.lean
   logs/LESSONS.md
   research/T20/ATTEMPTS_U11.md
   research/T20/ATTEMPTS_U12.md
   research/T20/REPORT_437.md
   research/T20/REPORT_441.md
   research/T20/T20_SPLIT.md
   research/T20/axioms_u11.lean
   research/T20/axioms_u12.lean
   research/T20/probes/continuation_closes.lean
   research/T20/probes/global_regularity_closes.lean
   ```

   `git diff-tree --no-commit-id --name-status -r HEAD -- '*.lean'` printed only
   three `A` entries: the new module, its axiom audit, and its probe.  No
   existing Lean module was modified.  `git diff --check` exited `0` (with only
   the same multiple-merge-base warning).

8. Reviewer mutation

   ```text
   $ lake env lean ../research/T20/probes/rev441_doubled_radius.lean
   ```

   Exit `1`; exact diagnostic is pasted in part 3.

9. Conditional contract gates

   ```text
   $ git diff --name-only origin/erenup/integration-section3...HEAD -- verification/
   warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 1c965400e3308df1cd679dfe843b0d5c47e49b82
   ```

   There is no `verification/` path in the diff.  Therefore `scripts/gates.sh`
   and `check_contracts.py --base-ref origin/erenup/integration-section3` are
   not required by the conditional review gate and were not run.
