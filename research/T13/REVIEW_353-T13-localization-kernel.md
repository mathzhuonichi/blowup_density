REJECT

## 1. What the lane claims

The worker report claims a uniform lattice-tail result, the geometric helper
`2 * r < 1`, and an inhomogeneous/homogeneous torus estimate
(`research/T13/REPORT_353.md:15-28`).  It also explicitly says that the required
kernel comparison `iTorus_periodize_le` was not shipped
(`research/T13/REPORT_353.md:51-64`).  The report's consumer probe confirms that
the final example takes the two needed bounds as hypotheses rather than proving
them (`research/T13/probes/localization_kernel_closes.lean:111-123`).

The paper passage was checked directly.  The inhomogeneous estimate in
`paper/sections/03-torus.tex:73-78` is the squared norm estimate, while the
kernel comparison in `paper/sections/03-torus.tex:79-95` uses the clearance
constant `C_{s,d}`.  In particular, lines 81-94 do not establish the report's
`tailConst s (2*r)` bound on all of `cube × cube`; they use the ball-to-boundary
separation and then the `4 C_{s,d}` estimate.

## 2. What is in Lean

The source does prove the following exact declarations:

* `summable_latticeVector_rpow`, `tailSum`, `tailConst`, and
  `tailSum_lt_top`/`tailConst_lt_top` are at
  `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:78-134`.
* The pointwise tail estimate is
  `latticeTail_le_tailConst (hs : 0 ≤ s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
  (hh : ‖h‖ ≤ ρ)` at
  `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:136-161`.
  This is at least as permissive in `s` as the report's advertised `0 < s`.
* The admissible-ball consequence is exactly
  `2 * r < 1` at
  `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:163-189`.
* The torus norm comparison is proved at
  `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:191-277`.
  Its right-hand `L²` term is the coefficient-side
  `periodicSobolevENorm 0 g`, not the physical torus spelling from the brief
  (`formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:199-202`).
  T10 already has the corresponding physical bridge
  `sobolevENorm_zero_eq` at
  `formalization/NSFormalization/Section3/T10/ForcePaths.lean:370-375`.

There is no declaration named `iTorus_periodize_le` in the new module (the file
ends at line 278), and the probe has no such theorem application.  The shipped
probe does give substantive instances: a finite tail constant and tail bound
(`research/T13/probes/localization_kernel_closes.lean:38-48`), an explicit
admissible ball (`:52-73`), and a nonconstant smooth periodic mode
(`:75-109`).  Thus the positive checks are not merely zero/vacuous instances.

## 3. Gaps and findings

1. **Blocking — mandatory estimate absent.**  The lane brief requires the
   standalone `iTorus_periodize_le` kernel comparison, but neither that theorem
   nor any of its four residual components is present.  The worker records the
   omission and the exact residual plan in
   `research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md:56-96` and
   `research/T13/COMPARISON.md:245-257`.  The geometric reason is substantive:
   when only one point is in the support ball, `x - y` need not have norm at
   most `2*r`; the paper's `d`-dependent bound is the applicable one.  Add a
   proved Lean comparison with the corrected clearance-dependent constant, or
   obtain an owner-approved correction of the brief before adding a theorem;
   the current consumer sketch is not a substitute.

2. **Major — norm spelling is not the requested physical `L²` statement.**
   The theorem at `LocalizationKernel.lean:199-202` proves a bound with
   `periodicSobolevENorm 0 g`, while the reconciled T13 specification calls for
   the registered physical norm in the localization route
   (`research/T13/Spec.lean:272-286`).  The report explains this choice at
   `research/T13/REPORT_353.md:74-78`, and it is mathematically reasonable, but
   the lane should either state the physical `eLpNorm (torusLift g) 2
   periodicTorusMeasure` form (using the existing T10 bridge) or add an
   explicit bridge theorem and document the exact conversion needed by lane
   354.

3. **Hygiene — the module gate is not silent.**  Both `lake build` and direct
   `lake env lean` emit the deprecation warning at
   `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:234`
   (`if_neg`; use `ite_eq_right`).  This is harmless to soundness but does not
   meet the brief's stated zero-output check.  Replace that one occurrence and
   rerun the gates.

4. **Citation precision.**  The report labels its `tailConst` result as the
   paper's `:80-89` estimate (`research/T13/REPORT_353.md:15-22`), but the cited
   paper lines use `d = dist(closure B, ∂Q)` and bound the full cube integral
   (`paper/sections/03-torus.tex:79-94`).  Reword the citation as an auxiliary
   pointwise lattice lemma, and reserve the paper citation for the clearance-
   dependent comparison.

5. **Probe deliverable mismatch.**  The brief asks the closure probe to use the
   `ContDiffBump` witness from the lane-344 probe.  That witness is
   `probeBump`/`probeField`, with smoothness, support, and nonzero proofs at
   `research/T13/probes/constant_endpoints_closes.lean:204-262`.  The lane-353
   probe instead defines a separate trigonometric `probeMode` at
   `research/T13/probes/localization_kernel_closes.lean:75-109`; it never
   instantiates the requested bump field (and cannot instantiate the missing
   kernel theorem).  Rework the probe to consume the existing bump witness once
   the three required estimates are actually available.

The module contains no forbidden declaration tokens, no `maxHeartbeats`, and no
anonymous instance declarations.  `git diff --name-status
origin/erenup/integration-section3...HEAD` shows the formalization files as
additions, not modifications; the only modified tracked files are research
records.  The whole Section4 search for the reported missing names returned no
matches (`iTorus_periodize_le`, `tailGeomConst`, `iTorus_singular_le`,
`lattice_summable`, `tail_bound`).

## 4. Commands and results

All Lean commands below were run from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

`lake build NSFormalization.Section3.T13.LocalizationKernel` exited 0.  Its
module-specific tail was:

```
⚠ [9993/9993] Replayed NSFormalization.Section3.T13.LocalizationKernel
warning: NSFormalization/Section3/T13/LocalizationKernel.lean:234:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
Build completed successfully (9993 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T13/LocalizationKernel.lean`
exited 0 with the exact output:

```
../formalization/NSFormalization/Section3/T13/LocalizationKernel.lean:234:8: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead
```

The axioms conformance command exited 0.  Its exact declarations were:

```
'NSFormalization.Section3.T13.summable_latticeVector_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.tailSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.tailConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.tailSum_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.tailConst_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.latticeTail_le_tailConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.two_r_lt_one_of_closure_ball_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T13.periodicSobolevENorm_le_l2_add_homogeneous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`lake env lean ../research/T13/probes/localization_kernel_closes.lean`
exited 0 with no output.

The required substantive negative probe was added as
`research/T13/probes/rev353_negative.lean`.  It changes the conclusion from
`2*r < 1` to `3*r < 1`; the expected proof break is reproduced exactly:

```
../research/T13/probes/rev353_negative.lean:14:2: error: Type mismatch
  two_r_lt_one_of_closure_ball_subset hr hball
has type
  2 * r < 1
but is expected to have type
  3 * r < 1
```

`make check` exited 0.  The exact final output was:

```
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

`git diff --check` exited 0.  The conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gate was not
required: `git diff --name-only origin/erenup/integration-section3...HEAD` has
no `verification/` path.

Fixes required:

1. Prove and ship the missing clearance-aware `iTorus_periodize_le` estimate
   (or obtain and record a corrected contract for its constant).
2. Resolve the physical-vs-coefficient `L²` spelling with an explicit T10
   bridge for the downstream consumer.
3. Replace `if_neg` at `LocalizationKernel.lean:234` and rerun the zero-output
   gate.
4. Correct the tail-lemma paper citation.
5. Rebuild `localization_kernel_closes.lean` around the lane-344
   `ContDiffBump`/`probeField` witness.

Verdict: REJECT

---

## Fix note — lane 353 (2026-09-18, after lead ruling)

Lead ruling on the REJECT: review items (1) "clearance-aware kernel comparison"
and (2) "physical/coefficient `L²` bridge" are **re-scoped** — (1) is **lane
354** (on this branch, with the geometric constant `C_{s,d}` identified in
`ATTEMPTS_LOCALIZATION_KERNEL.md`), (2) is the **assembly lane 359**.  Lane 353
does not attempt them.  The three hygiene items were fixed:

3. **Deprecated `if_neg`** — replaced at
   `formalization/NSFormalization/Section3/T13/LocalizationKernel.lean` (the
   `hhk` step in `periodicSobolevENorm_le_l2_add_homogeneous`) by
   `simp only [homogeneousDatumWeight, hk, ↓reduceIte]; rfl`.  `lake build` and
   `lake env lean` on the module now emit **0 warnings, 0 output**.

4. **Citation** — the module docstring §1 bullet and `REPORT_353.md` now label
   the `tailConst`/`latticeTail_le_tailConst` result as an *auxiliary pointwise
   lattice lemma*, explicitly **not** the paper's cube-integral clearance
   estimate of `03-torus.tex:79-94` (whose constant `C_{s,d}` uses
   `d = dist(closure B, ∂Q)`), which is lane 354's.

5. **Probe** — `research/T13/probes/localization_kernel_closes.lean` now consumes
   the lane-344 `ContDiffBump` witness (`probeCenter`, `probeBump`, `probeField`,
   `probe_ball_admissible`, `probeField_contDiff`, `probeField_supported`,
   `probeField_ne_zero`): `two_r_lt_one_of_closure_ball_subset` on the bump's
   admissible ball, and `latticeTail_le_tailConst` on every difference `x-y` of
   two points of `ball probeCenter (3/8)` at radius `2·(3/8)`.  The
   trigonometric mode `probeMode` is kept as the additional §3 instance (the
   compactly supported bump is not periodic).  The consumer-sketch `example` is
   unchanged (its `hL2`/`hHom` hypotheses are probe-only).

No declaration name or statement in the module changed (lane 354 branched from
`6b9a76c9`); the ATTEMPTS residual statements are untouched.  Gates re-run: see
the updated `REPORT_353.md` §4.
