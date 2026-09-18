ACCEPT

## 1. What the lane claims

The worker claims a route-R2 coefficient construction with one honestly isolated
analytic residue, forced prescribed-window existence and uniqueness, restriction,
and an explicit positive H³ time; it explicitly does **not** claim the amended H¹
existence input (`research/T11/REPORT_313.md:3-7`, `:108-111`). That is an accurate
description of the delivered scope.

Statement comparison:

* `PeriodicQuantitativeLocalInput'` in
  `formalization/NSFormalization/Section3/T11/LocalExistence.lean:24-29` is verbatim
  the amended target in `research/T11/LEAD_AMENDMENTS.md:12-18`. Its conditional
  lifespan consequence is exactly at `LocalExistence.lean:31-44`; it preserves the
  H¹ datum bound, the order-wise `M : ℕ → ℝ≥0∞`, all finiteness hypotheses,
  and one positive common `δ`.
* The first route target is `∀ ν, 0 < ν → Nonempty
  (TorusTwoSpaceContract ν)` at `research/T11/EXISTENCE_ROUTE.md:127-137`.
  As the brief expressly permits, the missing H³×H³→H² convolution bound is
  isolated as the single `TorusConvolutionInput` at `LocalExistence.lean:230-235`,
  and the target is proved from precisely that input at `:237-266`. The input is a
  bounded real bilinear realization of the fixed projected symbol, not the desired
  contract or existence theorem restated.
* The second exact route target is displayed at `EXISTENCE_ROUTE.md:139-152` and is
  byte-for-byte the conclusion and hypotheses of `torusForcedPicard_exists` at
  `LocalExistence.lean:384-393` (up to implicit binder presentation). In
  particular, the force is continuous on `Icc 0 T`, the supplied linear path has
  the stated bound `b`, and the result stays in the radius-`R` ball.
* The explicit quantitative strengthening reported at
  `REPORT_313.md:74-89,98-111` exists at `LocalExistence.lean:542-575,577-628` with
  exactly the claimed constants, force bound on `Icc 0 1`, positive `T ≤ 1`,
  radius `b+1`, and ball uniqueness.

The mathematics agrees with the cited paper. Appendix A gives the torus Fourier
convolution/product estimate that remains to be formalized
(`paper/sections/appendix-a-local-theory.tex:31-50`), and its mild equation has
exactly the signs used here: initial heat term, minus projected convection, plus
forced heat term (`:109-114`). The paper's H¹/common-interval conclusion is a later
and stronger obligation (`:62-77,147-151`), which this lane does not relabel as its
H³ coefficient theorem.

There is no hidden vacuity. `TorusPicardConstants` itself requires `0 < T`,
`0 < R`, the self-map inequality, and a strict contraction
(`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:260-268`).
The explicit theorem proves those conditions (`LocalExistence.lean:578-602`).
The amended input excludes `⊤` order by order and demands `0 < δ`
(`:24-29`); it contains no `.toReal` escape. Finally, the unconditional physical
witness has nonzero velocity and force (`:653-663`), while the delivered probe
also checks a nonzero constant coefficient datum and force for every exact
contract (`research/T11/probes/existence_u9b.lean:29-45,63-73`).

## 2. What is in Lean

Every exact theorem block printed in the worker report exists with that statement:

* lifespan consequence: `LocalExistence.lean:31-44`;
* absolute coefficient convolution: `:199-228`;
* conditional exact-contract constructor: `:230-266`;
* forced existence and actual integrability certificates: `:347-428`;
* restriction and ball uniqueness: `:431-483`;
* restricted numeric certificate: `:485-496`;
* explicit kernel mass, Picard constants, and quantitative solution: `:499-628`.

The underlying contract really requires identity at zero, semigroup composition,
joint strong continuity, positive smoothing, a continuous bilinear source,
integrable kernel, and smoothing coherence
(`vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceDuhamel.lean:407-444`). The
constructor fills those fields and pins the heat, smoothing, bilinear, and kernel
symbols at `LocalExistence.lean:241-266`. The reused heat estimate is the genuine
one-derivative weighted estimate
(`formalization/NSFormalization/Paper1/PeriodicHeatMultiplier.lean:95-151`), and
the Banach target agrees with the endpoint-safe library's ball existence and
uniqueness statement
(`vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:714-730,879-904`).

Hygiene is clean. The branch diff against
`origin/erenup/integration-section3` adds one Lean module and the requested
research files, and only appends to the route record; no pre-existing Lean module
or `verification/` file is changed. The new module has 39 named declarations,
including explicitly named local instances (`LocalExistence.lean:18-21`), no
`sorry`, `admit`, `axiom`, or `native_decide`, and no `maxHeartbeats` override.
The conformance file has 39 guarded `#print axioms` checks, each expecting exactly
`[propext, Classical.choice, Quot.sound]`
(`research/T11/axioms_existence_u9b.lean:5-159`).

## 3. Gaps

The only unfinished construction field is exactly the weighted
H³×H³→H² bounded realization in `TorusConvolutionInput`
(`LocalExistence.lean:230-235`; reported at `REPORT_313.md:131-146`). The lane does
prove absolute convergence coefficient by coefficient (`LocalExistence.lean:199-228`).
The cited T12 result is only a bounded diagonal reweighting
(`formalization/NSFormalization/Section3/T12/SpectralGap.lean:127-178`), and T10's
rapid-decay theorem assumes a smooth physical field
(`formalization/NSFormalization/Section3/T10/FourierCalculus.lean:79-101`); neither
already supplies the required bilinear map on arbitrary complete-carrier data.

The mandated whole-Section4 searches returned no occurrence of
`TorusConvolutionInput`, `torusProjectedConvectionSymbol`,
`PeriodicQuantitativeLocalInput'`, `TorusForcedMildOn`, or
`IsPeriodicSobolevPathOn`, and no match for a discrete/weighted convolution
H³→H² lemma. A whole-`formalization/NSFormalization` exact-name search found the
convolution target only in `LocalExistenceProbe.lean:213,231` and this lane at
`LocalExistence.lean:233-238,649-651`. Thus the claimed U9c convolution gap is
genuine. The later physical/pressure recovery and amended H¹ common-horizon work
are also stated without weakening at `research/T11/EXISTENCE_ROUTE.md:253-270`.

Negative check: `research/T11/probes/rev313_lifespan_mutation.lean:14-28`
replaces the proved denominator `1 + 2 / √ν` by `1 + 1 / √ν`, widening the
quantitative interval while leaving every argument present. Lean exits 1 at line
28 with the expected mismatch:

```text
error: Type mismatch
  torusForcedPicard_quantitative hν C A F B hB hF hFB
has type
  ... T := torusKernelTime ν ...
but is expected to have type
  ... T := torusKernelTimeWidened ν ...
```

No fix is required. The residue is exactly the one permitted by the lane brief and
is assigned to the next construction sub-lane.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran `lake` only from `verification/`.

1. `bash scripts/lean-install.sh` — exit 0. Exact terminal tail:

   ```text
   == lake test
   ...
   ℹ [10743/10743] Replayed Tests.CompletedDensity
   info: Tests/CompletedDensity.lean:20:0: Contract BlowupDensity.Tests.checkedCompletedDensity: checked; standard logical axioms only
   == OK
   ```

2. `lake build NSFormalization.Section3.T11.LocalExistence` — exit 0. Exact final
   output:

   ```text
   Build completed successfully (9906 jobs).
   ```

   Lake replayed warnings from pre-existing dependencies (for example
   `NSFormalization.Source.FiniteHilbertBochner`,
   `Formal.EndpointSafeTwoSpacePicard`, and
   `NSFormalization.Source.RealSobolev`); there was no warning or other output
   from `NSFormalization.Section3.T11.LocalExistence` itself.

3. Direct checks:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T11/LocalExistence.lean
   exit 0; stdout/stderr: <empty>

   lake env lean ../research/T11/probes/existence_u9b.lean
   exit 0; stdout/stderr: <empty>

   lake env lean ../research/T11/axioms_existence_u9b.lean
   exit 0; stdout/stderr: <empty>
   ```

   Audit counts were exactly:

   ```text
   axiom_checks=39
   expected_messages=39
   new_named_declarations=39
   ```

   Hence every guarded `#print axioms` result is exactly
   `[propext, Classical.choice, Quot.sound]`.

4. `make check` from the worktree root — exit 0. The architecture JSON is very
   large, so these are its exact gate-relevant head/tail lines (the pre-existing
   `source_hashes_match: false` diagnostic is non-failing):

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 562,
       "vendor/NavierStokesAndEuler": 2486,
       "vendor/HeliCorgi": 129
     },
     ...
     "tracked_cache_free": true,
     "source_hashes_match": false
   }
   Explicit axiom/admission tokens, all copied sources: 11
   python3 experiments/check_contracts.py
   ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.046s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

5. Hygiene and scope checks:

   ```text
   git diff --check origin/erenup/integration-section3...HEAD
   <empty; exit 0>

   git diff --name-only origin/erenup/integration-section3...HEAD -- verification
   <empty; exit 0>

   git diff --name-only origin/erenup/integration-section3...HEAD -- formalization
   formalization/NSFormalization/Section3/T11/LocalExistence.lean
   ```

   The forbidden-token/heartbeat scan also had empty output. Because
   `verification/` was not touched, the brief's conditional `scripts/gates.sh`
   and `check_contracts.py --base-ref origin/erenup/integration-section3` gates
   do not apply.

6. Required negative command:

   ```text
   lake env lean ../research/T11/probes/rev313_lifespan_mutation.lean
   exit 1
   ../research/T11/probes/rev313_lifespan_mutation.lean:28:2: error: Type mismatch
   ```
