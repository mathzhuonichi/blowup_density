ACCEPT-WITH-NOTES

Exact one-line fix: delete the empty line after `#print axioms mean_derivative` at
`research/T11/axioms_mean_identity.lean:44`; `git diff --check` then agrees with
the PASS claim at `research/T11/REPORT_316.md:72`.

## 1. What the lane claims

The report claims two unconditional U7 declarations, with no named analytic
input:

- `mean_formula`, the equality
  `velocityMeanT w.velocity t = galileanMeanT a f t` on `Ico 0 T`;
- `mean_derivative`, the derivative identity
  `HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t` on `Ioo 0 T`.

Those are the two canonical fields at
`research/T11/probes/api_on_canonical.lean:152-166`, and the worker reports them
at `research/T11/REPORT_316.md:5-28`.  The report also claims six elementary
adapter declarations, an exact-shape probe, a nonzero solution witness, and
eight standard-axiom audits (`research/T11/REPORT_316.md:30-43`).

The manuscript defines the data-dependent mean and shift by
`m(t) = mean(a) + integral_0^t mean(f(r)) dr` and `X(t) = integral_0^t m(r) dr`
at `paper/sections/appendix-a-local-theory.tex:89-98`; it states that the
translated velocity and force are mean-zero at
`paper/sections/appendix-a-local-theory.tex:97-103`.  The Section 3 argument
also says explicitly that integrating the periodic equation eliminates the
convective, Laplacian, and pressure terms and yields `m' = mean(g)` at
`paper/sections/03-torus.tex:395-405`.  Thus the claimed mathematics is the
mathematics requested by the brief.

## 2. What is in Lean

### Exact statements and proof route

The implemented declarations are at
`formalization/NSFormalization/Section3/T11/MeanIdentity.lean:137-171`.  Their
binders, quantifier order, class hypotheses, `Ico`/`Ioo` intervals, functions,
and conclusions are exactly the canonical fields at
`research/T11/probes/api_on_canonical.lean:153-166`.  The direct conformance
terms at `research/T11/probes/mean_identity_closes.lean:18-30` elaborate with
no adapters or additional hypotheses.

The definitions have the intended content: `velocityMeanT`, `forceMeanT`, and
`galileanMeanT` are respectively the Haar means and the prescribed integral
formula at `formalization/NSFormalization/Section3/T11/LocalTheory.lean:96-106`;
there is no `ENNReal.toReal` or other junk-value convention in either target.

Reuse of U3 is legitimate and not circular.  U3 proves the three periodic
cancellations at
`formalization/NSFormalization/Section3/T11/GalileanClasses.lean:371-437`,
differentiates the velocity mean and uses `w.momentum` at lines 439-514, and
uses the initial value plus FTC to prove the mean formula at lines 516-546.
Its public `transformed_mean_zero` then consumes that result at lines 573-605.
The new `mean_formula` recovers the untranslated equality from that public
theorem by Haar translation invariance and constant subtraction at
`formalization/NSFormalization/Section3/T11/MeanIdentity.lean:143-153`.
`mean_derivative` differentiates the prescribed primitive and transfers the
derivative across the local equality at lines 161-171.  The cited Haar/cube
bridge exists at `formalization/NSFormalization/Paper1/TorusCube.lean:39-49`,
and the cited differentiation-under-the-integral result exists at
`formalization/NSFormalization/Paper1/PeriodicPressureNormalization.lean:149-158`.

The six reported adapters all exist at
`formalization/NSFormalization/Section3/T11/MeanIdentity.lean:20-133`.
The upstream private declarations named in the attempt record also exist at
`formalization/NSFormalization/Section3/T11/GalileanClasses.lean:371-546`.

### Non-vacuity and hypotheses

No hypothesis was added.  In particular, `ClassicalSolutionT` carries
`0 < T`, the initial value, the equation, periodicity, and Sobolev data at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-299`.
Consequently the `Ico 0 T` target is not empty (it contains zero), and the real
interval `Ioo 0 T` is not empty.  The viscosity/class hypotheses are exactly
the canonical ones; there is no named input predicate.

The probe constructs `a(x) = coordinateVector 0`, zero force, and an explicit
constant nonzero classical solution at viscosity and horizon one at
`research/T11/probes/mean_identity_closes.lean:32-87`.  The probe compiled
with zero output.  This witnesses all class and solution premises
simultaneously and prevents the target from being accepted solely through an
empty solution type.  Zero force is sufficient here because there is no named
input whose claimed satisfiability requires nonzero forcing.

### Axioms and hygiene

The eight guarded audits are at
`research/T11/axioms_mean_identity.lean:5-43`.  The guarded file compiled with
zero output, and a supplemental raw audit printed exactly
`[propext, Classical.choice, Quot.sound]` for every declaration.

The forbidden-token/heartbeat scan over the three new Lean files returned no
matches for `sorry`, `admit`, `axiom`, `native_decide`, or
`set_option maxHeartbeats`; the explicit-instance scan also returned no
matches.  The pre-review diff contained one new formalization module and five
research files only; no pre-existing Lean module or `verification/` file was
modified.  The `T11_SPLIT.md` change is the one appended status line requested
by the brief (`research/T11/T11_SPLIT.md:83`).

## 3. Gaps

There is no mathematical, statement, build, axiom, or non-vacuity gap.

There is one minor hygiene/report-honesty discrepancy.  The report says
`git diff --check: PASS` at `research/T11/REPORT_316.md:72`, but the rerun exits
2 because `research/T11/axioms_mean_identity.lean:44` is an extra blank line at
EOF.  The exact one-line deletion stated above is the only required fix.

The lane report declares no missing theorem or residual named input, so no
"not in the tree" assertion is needed to justify acceptance.  As an additional
check, the requested whole-tree search
`grep -rnE 'PeriodicMeanReduction|mean_formula|mean_derivative|velocityMean_hasDerivAt|galileanMeanT' formalization/NSFormalization/Section4`
returned no output; the actual reused mean-evolution lemmas are in the cited
Section 3 U3 module.

The branch was five commits behind the moving integration ref at final review,
but the three-dot diff remained confined to the six reported lane files.  This
is merge bookkeeping, not a proof defect.

## 4. Commands and results

Every Lean command below was run from `verification/` after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, and only one Lake process
was run at a time.

### Required build

Command:

```text
lake build NSFormalization.Section3.T11.MeanIdentity
```

Exit 0.  Exact output (all warnings are replayed upstream warnings; there is no
warning from `MeanIdentity.lean`):

```text
⚠ [8778/9321] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9843/9930] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9847/9930] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9854/9930] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9857/9930] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9867/9930] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9870/9930] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
ℹ [9879/9930] Replayed NSFormalization.Source.PhysicalBesselSobolev
info: NSFormalization/Source/PhysicalBesselSobolev.lean:134:4: Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
⚠ [9896/9930] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
Build completed successfully (9930 jobs).
```

### Direct elaboration gates

All exited 0 with exactly zero stdout/stderr:

```text
lake env lean ../formalization/NSFormalization/Section3/T11/MeanIdentity.lean
lake env lean ../research/T11/probes/mean_identity_closes.lean
lake env lean ../research/T11/axioms_mean_identity.lean
```

The last command's zero output means every `#guard_msgs` matched.  Supplemental
unguarded `#print axioms` output was:

```text
'NSFormalization.Section3.T11.MeanIdentity.torusLift_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.MeanIdentity.integrable_torusLift_translate_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.MeanIdentity.meanT_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.MeanIdentity.cubeIntegral_contDiff_of_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.MeanIdentity.forceMeanT_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T11.MeanIdentity.meanT_sub_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.mean_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T11.mean_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Root check

Command:

```text
LEAN_NUM_THREADS=6 make check
```

Exit 0.  The command emits a very large generated contract-closure JSON; in
accordance with the top-of-file `logs/LESSONS.md` rule, here are exact output
head/tail excerpts rather than thousands of generated lines:

```text
python3 experiments/check_formalization_plan.py --check
```

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

No `verification/` path appears in
`git diff --name-only origin/erenup/integration-section3...HEAD`, so the brief's
conditional `scripts/gates.sh` and base-ref contract commands were not
applicable.  (`make check` did run the ordinary `check_contracts.py` check.)

### Negative mutation

A scratch stdin probe changed the main formula's right side from
`galileanMeanT a f t` to `-galileanMeanT a f t`, while retaining every binder
and hypothesis, then attempted `:= mean_formula`.  This is a substantive sign
flip, and Lean exited 1 with exactly:

```text
<stdin>:14:2: error: Type mismatch
  mean_formula
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), ∀ t ∈ Ico 0 T, velocityMeanT w.velocity t = galileanMeanT a f t
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), ∀ t ∈ Ico 0 T, velocityMeanT w.velocity t = -galileanMeanT a f t
```

This failure is mathematically meaningful: the compiled constant nonzero
solution witness has `m(0) != 0`, so the sign-flipped equality already fails at
`t = 0`; no argument was dropped.

### Diff and hygiene outputs

Pre-review lane diff:

```text
formalization/NSFormalization/Section3/T11/MeanIdentity.lean
research/T11/ATTEMPTS_MEAN_IDENTITY.md
research/T11/REPORT_316.md
research/T11/T11_SPLIT.md
research/T11/axioms_mean_identity.lean
research/T11/probes/mean_identity_closes.lean
```

`git diff --name-only ... -- verification` and both forbidden-token scans had
exactly zero output.  `git diff --check` exited 2 with exactly:

```text
research/T11/axioms_mean_identity.lean:44: new blank line at EOF.
```
